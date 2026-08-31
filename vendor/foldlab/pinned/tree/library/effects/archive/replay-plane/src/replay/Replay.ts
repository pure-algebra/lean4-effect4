/**
 * Replay runtime: the service, session execution, tripwires, transports, and
 * layers over the pure reducer and public session carriers.
 *
 * Transport ruling (GR-1b): caller-facing method types are byte-identical
 * across live, record, and replay modes. Replay rejections and violations
 * travel from wrapped methods to the session boundary through a named
 * defect-class seam — they never widen a method's error union — and land in
 * the tagged session outcome. The internal defect is plumbing, never
 * modeled defect semantics.
 */
import {
  Cause,
  Clock,
  Context,
  Data,
  Effect,
  Layer,
  Match,
  Option,
  Predicate,
  Random,
  Result,
  References,
  Ref,
  Schema,
} from "effect"
import {
  CasNodeInput,
  StoreFailure,
  UnknownKind,
  type CasError,
  type CasReference,
  type ContentId,
} from "../cas/Node.ts"
import { CasStore, type CasStoreShape } from "../cas/Store.ts"
import type { Decision, DecisionTrace } from "./Decision.ts"
import type { AnyOperationDescription, OperationSchema } from "./Operation.ts"
import { liveHandler } from "../internal/live.ts"
import { HistoryKindTag, WitnessKindTag } from "../internal/kindTags.ts"
import { makeSessionCell, type SessionCell } from "../internal/sessionCell.ts"
import {
  decodeHistoryEntry,
  decodeStoredValue,
  encodeHistoryEntry,
  encodeStoredValue,
  encodeWitness,
  InternalStorageError,
  StoredHistoryEntry,
  StoredWitness,
} from "../internal/storage.ts"
import { reduce, rejectStep } from "./Reducer.ts"
import { WitnessSink, type WitnessReceipt } from "./WitnessSink.ts"
import type {
  AmbientService,
  Invocation,
  MismatchCategory,
  Outcome,
  SessionOutcome,
  SessionOptions,
  SessionResult,
  SessionState,
  StepOut,
  Terminal,
  TerminalSchemas,
} from "./Session.ts"

export interface ReplayShape {
  /** Adapter-facing: route one described invocation through the session.
   * The error channel is exactly the operation's declared failure type.
   * Mismatch, inadmissibility, AND record-mode append failure all travel
   * the defect-class transport seam (GR-1b) — orchestration cannot catch
   * what is not in the channel, so a store failure aborts the session and
   * history stays a truthful prefix structurally (GR-7's poisoning intent,
   * realized without a mutable poisoned flag; the failure surfaces as the
   * session's typed CasError). */
  readonly invoke: <D extends AnyOperationDescription>(
    operation: D,
    request: D["request"]["Type"],
  ) => Effect.Effect<D["success"]["Type"], D["failure"]["Type"]>

  /** Session-facing: install the per-session invocation handler and execute
   * one complete record or replay attempt. Replay mode replaces the default
   * Clock and Random services with ambient-use tripwires while disabling
   * tracer timing, so Effect.fn spans remain usable without consulting Clock.
   * Semantic Clock and Random use still produces a Violated outcome. */
  readonly run: <A, E, R>(
    program: Effect.Effect<A, E, R>,
    options: SessionOptions<A, E>,
  ) => Effect.Effect<SessionResult<A, E>, CasError, R>
}

export class Replay extends Context.Service<Replay, ReplayShape>()(
  "foldlab/effect-replay/Replay",
) {}

/** The abort-path persistence deadline. A hung store must not hang
 * session teardown; the sink reports what the deadline cost. */
const AbortPersistDeadline = "1 second"

class MismatchTransport extends Data.TaggedError("ReplayMismatchTransport")<{
  readonly category: MismatchCategory
  readonly at: number
}> {}

class AmbientTransport extends Data.TaggedError("ReplayAmbientTransport")<{
  readonly service: AmbientService
}> {}

class CasTransport extends Data.TaggedError("ReplayCasTransport")<{
  readonly error: CasError
}> {}

class RuntimeTransport extends Data.TaggedError("ReplayRuntimeTransport")<{
  readonly reason: string
}> {}

interface ActiveSession {
  readonly state: SessionState<string, string, unknown, unknown>
  readonly historyRoot: ContentId | undefined
  readonly trace: ReadonlyArray<Decision>
}

const transportCasFailure = <A, R>(
  self: Effect.Effect<A, CasError, R>,
): Effect.Effect<A, never, R> =>
  Effect.matchEffect(self, {
    onFailure: (error) => Effect.die(new CasTransport({ error })),
    onSuccess: Effect.succeed,
  })

const storageEffect = <A>(
  operation: string,
  evaluate: () => A,
): Effect.Effect<A, StoreFailure> =>
  Effect.sync(evaluate).pipe(
    Effect.catchDefect((cause) => Effect.fail(new StoreFailure({
      reason: `${operation}: ${String(cause)}`,
    }))),
  )

const encodeOperationValue = <S extends OperationSchema>(
  schema: S,
  value: S["Type"],
): Effect.Effect<string, StoreFailure> =>
  storageEffect("Operation value encoding failed", () =>
    encodeStoredValue(Result.getOrThrowWith(
      Schema.encodeUnknownResult(schema)(value),
      (failure) => new InternalStorageError(String(failure)),
    )))

const decodeOperationValue = <S extends OperationSchema>(
  schema: S,
  value: string,
): Effect.Effect<S["Type"], StoreFailure> =>
  storageEffect("Operation value decoding failed", () =>
    Result.getOrThrowWith(
      Schema.decodeUnknownResult(schema)(decodeStoredValue(value)),
      (failure) => new InternalStorageError(String(failure)),
    ))

const appendDecisions = (
  active: ActiveSession,
  state: SessionState<string, string, unknown, unknown>,
  decisions: DecisionTrace,
  historyRoot: ContentId | undefined = active.historyRoot,
): ActiveSession => ({
  state,
  historyRoot,
  trace: [...active.trace, ...decisions],
})

const abortForStoreFailure = (
  active: ActiveSession,
): ActiveSession => {
  const aborted = reduce(active.state, { _tag: "AppendFailed" })
  return appendDecisions(active, aborted.state, aborted.decisions)
}

const rejectForMismatch = (
  active: ActiveSession,
  category: MismatchCategory,
): readonly [ActiveSession, MismatchTransport] => {
  const rejected = rejectStep(active.state, category)
  return [
    appendDecisions(active, rejected.state, rejected.decisions),
    new MismatchTransport({
      category,
      at: active.state.cursor,
    }),
  ]
}

const loadHistory = (
  store: CasStoreShape,
  root: ContentId,
): Effect.Effect<ReadonlyArray<StoredHistoryEntry>, CasError> =>
  Effect.gen(function* () {
    const entries: Array<StoredHistoryEntry> = []
    const visited = new Set<ContentId>()
    let current: ContentId | undefined = root

    while (current !== undefined) {
      if (visited.has(current)) {
        return yield* new StoreFailure({ reason: `Cyclic history root: ${current}` })
      }
      visited.add(current)

      const node: CasNodeInput = yield* store.load(current)
      if (node.kind.tag !== HistoryKindTag) return yield* new UnknownKind(node.kind)
      if (node.refs.length > 1) {
        return yield* new StoreFailure({ reason: `History node has multiple predecessors: ${current}` })
      }

      const raw = yield* storageEffect(
        `History payload decoding failed at ${current}`,
        () => decodeHistoryEntry(node.payload),
      )
      const entry = yield* Schema.decodeUnknownEffect(StoredHistoryEntry)(raw).pipe(
        Effect.mapError((issue) => new StoreFailure({
          reason: `History payload validation failed at ${current}: ${String(issue)}`,
        })),
      )
      entries.push(entry)

      const predecessor: CasReference | undefined = node.refs[0]
      if (predecessor !== undefined && predecessor.expectedTag !== HistoryKindTag) {
        return yield* new StoreFailure({
          reason: `History predecessor has wrong declared tag at ${current}`,
        })
      }
      current = predecessor?.id
    }

    entries.reverse()
    return entries
  })

const tripwireClock: Clock.Clock = {
  currentTimeMillisUnsafe: () => {
    throw new AmbientTransport({ service: "Clock" })
  },
  currentTimeMillis: Effect.die(new AmbientTransport({ service: "Clock" })),
  currentTimeNanosUnsafe: () => {
    throw new AmbientTransport({ service: "Clock" })
  },
  currentTimeNanos: Effect.die(new AmbientTransport({ service: "Clock" })),
  monotonicTimeNanosUnsafe: () => {
    throw new AmbientTransport({ service: "Clock" })
  },
  monotonicTimeNanos: Effect.die(new AmbientTransport({ service: "Clock" })),
  sleep: () => Effect.die(new AmbientTransport({ service: "Clock" })),
}

const tripwireRandom: Context.Service.Shape<typeof Random.Random> = {
  nextIntUnsafe: () => {
    throw new AmbientTransport({ service: "Random" })
  },
  nextDoubleUnsafe: () => {
    throw new AmbientTransport({ service: "Random" })
  },
}

type StoredTerminalValue = string | { readonly _tag: "Unrepresentable" }

const unrepresentable = (): StoredTerminalValue => ({ _tag: "Unrepresentable" })

const encodeTerminalValue = <A>(
  value: A,
  schema: Schema.Codec<A, unknown, never, never> | undefined,
): Effect.Effect<StoredTerminalValue, StoreFailure> => {
  if (schema === undefined) {
    return Effect.sync(() => encodeStoredValue(value)).pipe(
      Effect.catchDefect(() => Effect.succeed(unrepresentable())),
    )
  }
  return storageEffect("Witness terminal encoding failed", () =>
    encodeStoredValue(Result.getOrThrowWith(
      Schema.encodeUnknownResult(schema)(value),
      (failure) => new InternalStorageError(String(failure)),
    )))
}

type StoredTerminal =
  | { readonly _tag: "Succeeded"; readonly value: StoredTerminalValue }
  | { readonly _tag: "Failed"; readonly error: StoredTerminalValue }

const makeStoredTerminal = <A, E>(
  terminal: Terminal<A, E>,
  schemas: TerminalSchemas<A, E> | undefined,
): Effect.Effect<StoredTerminal, StoreFailure> => terminal._tag === "Succeeded"
  ? encodeTerminalValue(terminal.value, schemas?.success).pipe(
      Effect.map((value): StoredTerminal => ({ _tag: "Succeeded", value })),
    )
  : encodeTerminalValue(terminal.error, schemas?.failure).pipe(
      Effect.map((error): StoredTerminal => ({ _tag: "Failed", error })),
    )

type WitnessOutcome<A, E> = SessionOutcome<A, E> | {
  readonly _tag: "Aborted"
  readonly reason: "Defect" | "Interrupted"
}

const makeStoredOutcome = <A, E>(
  outcome: WitnessOutcome<A, E>,
  schemas: TerminalSchemas<A, E> | undefined,
): Effect.Effect<StoredWitness["outcome"], StoreFailure> =>
  Match.value(outcome).pipe(Match.tagsExhaustive({
    Completed: (completed) =>
      makeStoredTerminal(completed.terminal, schemas).pipe(
        Effect.map((terminal): StoredWitness["outcome"] => ({
          _tag: "Completed",
          terminal,
        })),
      ),
    Violated: (violated) =>
      Effect.succeed<StoredWitness["outcome"]>({
        _tag: "Violated",
        service: violated.service,
      }),
    Aborted: (aborted) => Effect.succeed<StoredWitness["outcome"]>(aborted),
    Rejected: (rejected) =>
      rejected.terminalSoFar === undefined
        ? Effect.succeed<StoredWitness["outcome"]>({
            _tag: "Rejected",
            category: rejected.category,
            at: rejected.at,
          })
        : makeStoredTerminal(rejected.terminalSoFar, schemas).pipe(
            Effect.map((terminalSoFar): StoredWitness["outcome"] => ({
              _tag: "Rejected",
              category: rejected.category,
              at: rejected.at,
              terminalSoFar,
            })),
          ),
  }))

const persistWitness = <A, E>(
  store: CasStoreShape,
  executionId: string,
  active: ActiveSession,
  outcome: WitnessOutcome<A, E>,
  schemas?: TerminalSchemas<A, E>,
): Effect.Effect<ContentId, CasError> =>
  Effect.gen(function* () {
    const common = {
      mode: active.state.mode,
      executionId,
      consumed: active.state.cursor,
      trace: active.trace,
      outcome: yield* makeStoredOutcome(outcome, schemas),
    }
    const raw = active.historyRoot === undefined
      ? common
      : { ...common, historyRoot: active.historyRoot }
    const witness = yield* StoredWitness.makeEffect(raw).pipe(
      Effect.mapError((issue) => new StoreFailure({
        reason: `Witness validation failed: ${String(issue)}`,
      })),
    )
    const payload = yield* storageEffect("Witness encoding failed", () =>
      encodeWitness(witness))
    const node = CasNodeInput.make({
      kind: { version: 0, tag: WitnessKindTag },
      payload,
      refs: active.historyRoot === undefined
        ? []
        : [{ id: active.historyRoot, expectedTag: HistoryKindTag }],
    })
    return yield* store.put(node)
  })

const sessionResult = <A, E>(
  active: ActiveSession,
  outcome: SessionOutcome<A, E>,
  witness: ContentId,
): SessionResult<A, E> => {
  const history = active.state.mode === "replay"
    ? active.historyRoot
    : active.trace.some((decision) => decision._tag === "OccurrenceAppended")
      ? active.historyRoot
      : undefined
  return history === undefined
    ? { outcome, witness }
    : { outcome, witness, history }
}

type AppendCellResult =
  | { readonly _tag: "Appended" }
  | { readonly _tag: "Absorbed" }
  | { readonly _tag: "CasFailure"; readonly error: CasError }

type AppendPersisted = {
  readonly _tag: "Appended" | "Absorbed"
  readonly next: ActiveSession
}

type ReplayCellResult<D extends AnyOperationDescription> =
  | { readonly _tag: "Success"; readonly value: D["success"]["Type"] }
  | { readonly _tag: "Failure"; readonly error: D["failure"]["Type"] }
  | { readonly _tag: "Rejected"; readonly transport: MismatchTransport }

const appendRecordedOutcome = <D extends AnyOperationDescription>(
  store: CasStoreShape,
  cell: SessionCell<ActiveSession>,
  operation: D,
  invocation: Invocation<string, string>,
  outcome:
    | { readonly _tag: "Success"; readonly value: D["success"]["Type"] }
    | { readonly _tag: "Failure"; readonly error: D["failure"]["Type"] },
): Effect.Effect<void> =>
  cell.modifyMasked<AppendCellResult, never, never>((active) => {
    const persist: Effect.Effect<AppendPersisted, CasError> = Effect.gen(function* () {
      let stored: Outcome<string, string>
      if (outcome._tag === "Success") {
        stored = {
          _tag: "Success",
          value: yield* encodeOperationValue(operation.success, outcome.value),
        }
      } else {
        stored = {
          _tag: "Failure",
          error: yield* encodeOperationValue(operation.failure, outcome.error),
        }
      }

      const appended = reduce(active.state, {
        _tag: "Recorded",
        invocation,
        outcome: stored,
      })
      if (appended.result._tag === "Absorbed") {
        // The session aborted while this outcome was in flight — the model
        // absorbs it, so the late outcome is discarded, never persisted.
        return { _tag: "Absorbed", next: active }
      }
      if (appended.result._tag !== "Appended") {
        return yield* Effect.die(new RuntimeTransport({
          reason: `Record append produced ${appended.result._tag}`,
        }))
      }

      const entry = yield* StoredHistoryEntry.makeEffect({
        ...invocation,
        outcome: stored,
      }).pipe(
        Effect.mapError((issue) => new StoreFailure({
          reason: `History entry validation failed: ${String(issue)}`,
        })),
      )
      const payload = yield* storageEffect(
        "History entry encoding failed",
        () => encodeHistoryEntry(entry),
      )
      const node = CasNodeInput.make({
        kind: { version: 0, tag: HistoryKindTag },
        payload,
        refs: active.historyRoot === undefined
          ? []
          : [{ id: active.historyRoot, expectedTag: HistoryKindTag }],
      })
      const root = yield* store.put(node)
      return {
        _tag: "Appended",
        next: appendDecisions(active, appended.state, appended.decisions, root),
      }
    })

    return persist.pipe(Effect.match({
      onFailure: (error): readonly [AppendCellResult, ActiveSession] => [
        { _tag: "CasFailure", error },
        abortForStoreFailure(active),
      ],
      onSuccess: (result): readonly [AppendCellResult, ActiveSession] => [
        { _tag: result._tag },
        result.next,
      ],
    }))
  }).pipe(Effect.flatMap((result) => result._tag === "CasFailure"
    ? Effect.die(new CasTransport({ error: result.error }))
    : Effect.void))

const invokeInSession = <D extends AnyOperationDescription>(
  store: CasStoreShape,
  cell: SessionCell<ActiveSession>,
  operation: D,
  request: D["request"]["Type"],
): Effect.Effect<D["success"]["Type"], D["failure"]["Type"]> =>
  Effect.gen(function* () {
    const storedRequest = yield* transportCasFailure(
      encodeOperationValue(operation.request, request),
    )
    const invocation = {
      op: operation.id,
      revision: operation.revision,
      request: storedRequest,
    }

    const mode = (yield* cell.read).state.mode
    if (mode === "record") {
      const invoked = yield* cell.modify((current) => {
        const transition = reduce(current.state, { _tag: "Invoke", invocation })
        const next = appendDecisions(
          current,
          transition.state,
          transition.decisions,
        )
        const step: readonly [
          {
            readonly transition: StepOut<string, string, unknown, unknown>
            readonly at: number
          },
          ActiveSession,
        ] = [{ transition, at: current.state.cursor }, next]
        return Effect.succeed(step)
      })
      if (invoked.transition.result._tag === "Rejected") {
        // The model refused the invocation — delegation is exclusive, so
        // an interleaved record-mode call is a typed session rejection,
        // exactly like a replay mismatch.
        return yield* Effect.die(new MismatchTransport({
          category: invoked.transition.result.category,
          at: invoked.transition.result.at,
        }))
      }
      if (invoked.transition.result._tag !== "Delegated") {
        return yield* Effect.die(new RuntimeTransport({
          reason: `Record invocation produced ${invoked.transition.result._tag}`,
        }))
      }

      const handler = liveHandler(operation)
      if (handler === undefined) {
        return yield* Effect.die(new RuntimeTransport({
          reason: `No live role supplied for ${operation.id}`,
        }))
      }

      return yield* handler(request).pipe(
        Effect.matchEffect({
          onFailure: (error) =>
            appendRecordedOutcome(store, cell, operation, invocation, {
              _tag: "Failure",
              error,
            }).pipe(Effect.andThen(Effect.fail(error))),
          onSuccess: (value) =>
            appendRecordedOutcome(store, cell, operation, invocation, {
              _tag: "Success",
              value,
            }).pipe(Effect.as(value)),
        }),
      )
    }

    const replayed = yield* cell.modify<ReplayCellResult<D>, never, never>(
      (current): Effect.Effect<readonly [ReplayCellResult<D>, ActiveSession]> =>
        Effect.gen(function* () {
          const stepped = reduce(current.state, { _tag: "Invoke", invocation })
          if (stepped.result._tag === "Rejected") {
            const next = appendDecisions(current, stepped.state, stepped.decisions)
            const rejected: readonly [ReplayCellResult<D>, ActiveSession] = [{
              _tag: "Rejected",
              transport: new MismatchTransport({
                category: stepped.result.category,
                at: stepped.result.at,
              }),
            }, next]
            return rejected
          }
          if (stepped.result._tag !== "Substituted") {
            return yield* Effect.die(new RuntimeTransport({
              reason: `Replay invocation produced ${stepped.result._tag}`,
            }))
          }

          const recorded = stepped.result.outcome
          const encoded = recorded._tag === "Success" ? recorded.value : recorded.error
          if (!Predicate.isString(encoded)) {
            const [next, transport] = rejectForMismatch(current, "OutcomeInadmissible")
            const rejected: readonly [ReplayCellResult<D>, ActiveSession] = [
              { _tag: "Rejected", transport },
              next,
            ]
            return rejected
          }

          if (recorded._tag === "Success") {
            const decoded = yield* Effect.result(
              decodeOperationValue(operation.success, encoded),
            )
            if (Result.isFailure(decoded)) {
              const [next, transport] = rejectForMismatch(current, "OutcomeInadmissible")
              const rejected: readonly [ReplayCellResult<D>, ActiveSession] = [
                { _tag: "Rejected", transport },
                next,
              ]
              return rejected
            }
            const substituted: readonly [ReplayCellResult<D>, ActiveSession] = [
              { _tag: "Success", value: decoded.success },
              appendDecisions(current, stepped.state, stepped.decisions),
            ]
            return substituted
          }

          const decoded = yield* Effect.result(
            decodeOperationValue(operation.failure, encoded),
          )
          if (Result.isFailure(decoded)) {
            const [next, transport] = rejectForMismatch(current, "OutcomeInadmissible")
            const rejected: readonly [ReplayCellResult<D>, ActiveSession] = [
              { _tag: "Rejected", transport },
              next,
            ]
            return rejected
          }
          const substituted: readonly [ReplayCellResult<D>, ActiveSession] = [
            { _tag: "Failure", error: decoded.success },
            appendDecisions(current, stepped.state, stepped.decisions),
          ]
          return substituted
        }),
    )
    return yield* Match.value(replayed).pipe(Match.tagsExhaustive({
      Rejected: (rejected) => Effect.die(rejected.transport),
      Success: (substituted) => Effect.succeed(substituted.value),
      Failure: (failed) => Effect.fail(failed.error),
    }))
  })

const finishSession = <A, E>(
  store: CasStoreShape,
  executionId: string,
  cell: SessionCell<ActiveSession>,
  terminal: Terminal<A, E>,
  schemas: TerminalSchemas<A, E> | undefined,
): Effect.Effect<SessionResult<A, E>, CasError> =>
  cell.modify((active) => Effect.gen(function* () {
    const completed = reduce(active.state, { _tag: "Complete", terminal })
    if (completed.result._tag !== "SessionOutcome") {
      return yield* Effect.die(new RuntimeTransport({
        reason: `Session completion produced ${completed.result._tag}`,
      }))
    }

    const next = appendDecisions(active, completed.state, completed.decisions)
    const reducedOutcome = completed.result.outcome
    let outcome: SessionOutcome<A, E>
    if (reducedOutcome._tag === "Completed") {
      outcome = { _tag: "Completed", terminal }
    } else if (reducedOutcome._tag === "Rejected") {
      outcome = {
        _tag: "Rejected",
        category: reducedOutcome.category,
        at: reducedOutcome.at,
        terminalSoFar: terminal,
      }
    } else {
      return yield* Effect.die(new RuntimeTransport({
        reason: "Completion reducer returned an ambient violation",
      }))
    }
    const witness = yield* persistWitness(store, executionId, next, outcome, schemas)
    const finished: readonly [SessionResult<A, E>, ActiveSession] = [
      sessionResult(next, outcome, witness),
      next,
    ]
    return finished
  }))

const makeReplayRun = (
  store: CasStoreShape,
  executionCounter: Ref.Ref<number>,
): ReplayShape["run"] => {
  const run: ReplayShape["run"] = <A, E, R>(
    program: Effect.Effect<A, E, R>,
    options: SessionOptions<A, E>,
  ): Effect.Effect<SessionResult<A, E>, CasError, R> =>
    Effect.gen(function* () {
      const executionId = options.executionId ?? `execution-${
        yield* Ref.updateAndGet(executionCounter, (value) => value + 1)
      }`
      const history = options.history === undefined
        ? []
        : yield* loadHistory(store, options.history)
      const cell = yield* makeSessionCell<ActiveSession>({
        state: {
          mode: options.mode,
          status: "active",
          history,
          cursor: options.mode === "record" ? history.length : 0,
        },
        historyRoot: options.history,
        trace: [],
      })

      const scopedReplay = Replay.of({
        invoke: (operation, request) =>
          invokeInSession(store, cell, operation, request),
        run,
      })
      const scopedProgram = options.mode === "replay"
        ? program.pipe(
            Effect.provideService(Replay, scopedReplay),
            Effect.provideService(Clock.Clock, tripwireClock),
            Effect.provideService(Random.Random, tripwireRandom),
            Effect.provideService(References.TracerTimingEnabled, false),
          )
        : program.pipe(Effect.provideService(Replay, scopedReplay))
      const attempted = scopedProgram.pipe(
        Effect.match({
          onFailure: (error): Terminal<A, E> => ({ _tag: "Failed", error }),
          onSuccess: (value): Terminal<A, E> => ({ _tag: "Succeeded", value }),
        }),
        Effect.flatMap((terminal) =>
          finishSession(store, executionId, cell, terminal, options.terminal)),
      )

      const handled = attempted.pipe(
        Effect.catchDefect((defect): Effect.Effect<SessionResult<A, E>, CasError> => {
          if (defect instanceof CasTransport) return Effect.fail(defect.error)
          if (defect instanceof MismatchTransport) {
            const outcome: SessionOutcome<A, E> = {
              _tag: "Rejected",
              category: defect.category,
              at: defect.at,
            }
            return cell.modify((active) =>
              persistWitness<A, E>(
                store,
                executionId,
                active,
                outcome,
                options.terminal,
              ).pipe(Effect.map(
                (witness): readonly [SessionResult<A, E>, ActiveSession] => [
                  sessionResult<A, E>(active, outcome, witness),
                  active,
                ],
              )))
          }
          if (defect instanceof AmbientTransport) {
            const outcome: SessionOutcome<A, E> = {
              _tag: "Violated",
              service: defect.service,
            }
            return cell.modify((active) =>
              persistWitness<A, E>(
                store,
                executionId,
                active,
                outcome,
                options.terminal,
              ).pipe(Effect.map(
                (witness): readonly [SessionResult<A, E>, ActiveSession] => [
                  sessionResult<A, E>(active, outcome, witness),
                  active,
                ],
              )))
          }
          return Effect.die(defect)
        }),
      )

      return yield* handled.pipe(
        Effect.onExit((exit) => {
          if (exit._tag === "Success") return Effect.void
          if (!Cause.hasDies(exit.cause) && !Cause.hasInterrupts(exit.cause)) {
            return Effect.void
          }
          const reason: "Defect" | "Interrupted" = Cause.hasInterrupts(exit.cause)
            ? "Interrupted"
            : "Defect"
          return Effect.gen(function* () {
            const active = yield* cell.read
            const sink = yield* WitnessSink
            // The abort-path write is owned by this finalizer fiber and
            // truly bounded: on deadline the interruptible put is
            // interrupted (CAS puts are content-addressed, so a repeat
            // is idempotent), and the sacrifice is reported to the
            // sink instead of a detached fiber outliving the session
            // with its receipt discarded.
            const persisted = yield* persistWitness<A, E>(
              store,
              executionId,
              active,
              { _tag: "Aborted", reason },
              options.terminal,
            ).pipe(
              Effect.timeoutOption(AbortPersistDeadline),
              Effect.result,
            )
            const result: WitnessReceipt["result"] = Result.isFailure(persisted)
              ? { _tag: "Failed", error: persisted.failure }
              : Option.isNone(persisted.success)
                ? { _tag: "TimedOut" }
                : { _tag: "Persisted", witness: persisted.success.value }
            yield* sink.record({ executionId, reason, result })
          })
        }),
      )
    })
  return run
}

/** Construct the replay runtime over the supplied CAS store. */
export const layerReplay: Layer.Layer<Replay, never, CasStore> = Layer.effect(
  Replay,
  Effect.gen(function* () {
    const store = yield* CasStore
    const executionCounter = yield* Ref.make(0)
    const run = makeReplayRun(store, executionCounter)
    const service = Replay.of({
      invoke: () => Effect.die(new RuntimeTransport({
        reason: "Replay.invoke used outside session",
      })),
      run,
    })
    return service
  }),
)

/** Run a program under a session. The history root resolves through the
 * Replay runtime's CasStore; record mode creates a fresh immutable suffix. */
export const session = <A, E, R>(
  program: Effect.Effect<A, E, R>,
  options: SessionOptions<A, E>,
): Effect.Effect<SessionResult<A, E>, CasError, R | Replay> =>
  Replay.use((replay) => replay.run(program, options))

/** Record a run. A thin wrapper over `session` whose type cannot carry a
 * history root — recording never consumes one. */
export const record = <A, E, R>(
  program: Effect.Effect<A, E, R>,
  options?: Omit<SessionOptions<A, E>, "mode" | "history">,
): Effect.Effect<SessionResult<A, E>, CasError, R | Replay> =>
  session(program, { ...options, mode: "record" })

/** Replay a run against its recorded history. The root is positional and
 * required — a replay without a history is not expressible here, where
 * the flat `session` options accept the meaningless combination. */
export const replay = <A, E, R>(
  program: Effect.Effect<A, E, R>,
  history: ContentId,
  options?: Omit<SessionOptions<A, E>, "mode" | "history">,
): Effect.Effect<SessionResult<A, E>, CasError, R | Replay> =>
  session(program, { ...options, mode: "replay", history })
