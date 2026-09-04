import { Cause, Deferred, Effect, Exit, Option, Result } from "effect"
import {
  Deferreds,
  DeferredsRows,
  deferredDoubleComplete,
  deferredFailAwait,
  deferredPendingAwait,
  deferredPollPending,
  deferredSucceedAwait,
  deferredTwoHandles
} from "./deferred-fixture.ts"
import {
  DeferredsFull,
  DeferredsFullRows,
  deferredCompleteWithStoresEffect,
  deferredCompletionShapes,
  deferredDoneIsCompleteWith,
  deferredInterruptIsAFailure,
  deferredIntoUninterruptible,
  type DeferredsFullService
} from "./deferreds-fixture.stub.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Deferreds` family: rc.112's own `Deferred`, wrapped so
 * the shared alphabet can see it.
 *
 * - `make` is `Deferred.make`, `succeed`/`fail` are `Deferred.succeed`/`fail`
 *   and answer whether this call completed the cell, `isDone` is
 *   `Deferred.isDone`.
 * - `poll` is the only method that is not a `Deferred` call verbatim: rc.112's
 *   `Deferred.poll` answers `Option<Effect<A, E>>`, the completion *effect*,
 *   while the family answers the completion *value*. Running that effect
 *   through `Effect.result` is total and observes nothing — the cell is
 *   already completed, so the effect is a `succeed`/`fail` — and lands in
 *   exactly the `Option<Result<number, number>>` the family declares.
 * - `awaitValue` is `Deferred.await`; `awaitError` is `Effect.flip` of it, so
 *   the failure is the answer and the value is the abort.
 *
 * A cell never reaches the wire as an object. `registerHandle` brands it and
 * `wire` encodes it as its index in first-seen order, which is the `make` order
 * the Lean face numbers cells in.
 *
 * `deferredPendingAwait` awaits a cell nothing completes. rc.112 parks the
 * fiber (`Deferred.ts` `_await` pushes a resume onto `self.resumes`), no
 * primitive runs after that, so the op budget cannot fire and the run never
 * settles. `stallMs` turns that park into the frontier the golden records
 * (`RunOptions.stallMs` in `tracer.ts`).
 */

// The brand rc.112 stamps on every deferred (`Deferred.ts` TypeId). It is a
// string key, not an exported value, so it is written out here.
const DeferredTypeId = "~effect/Deferred"
registerHandle((value) => DeferredTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "deferredSucceedAwait"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const stallMs = Number(process.env.EFFECT4_STALL_MS ?? "50")
const sink: Event[] = []

/** The completion a `poll` found, as the family's answer. */
const polled = (
  cell: Deferred.Deferred<number, number>
): Effect.Effect<Option.Option<Result.Result<number, number>>> =>
  Effect.flatMap(Deferred.poll(cell), (completion) =>
    Option.isNone(completion)
      ? Effect.succeed(Option.none<Result.Result<number, number>>())
      : Effect.asSome(Effect.result(completion.value)))

const live = {
  make: Deferred.make<number, number>(),
  succeed: (cell: Deferred.Deferred<number, number>, value: number) => Deferred.succeed(cell, value),
  fail: (cell: Deferred.Deferred<number, number>, error: number) => Deferred.fail(cell, error),
  isDone: (cell: Deferred.Deferred<number, number>) => Deferred.isDone(cell),
  poll: (cell: Deferred.Deferred<number, number>) => polled(cell),
  awaitValue: (cell: Deferred.Deferred<number, number>) => Deferred.await(cell),
  awaitError: (cell: Deferred.Deferred<number, number>) => Effect.flip(Deferred.await(cell))
}

/** Build the service before the `run` sentinel so construction is outside the
 * compared window; the cells themselves are minted by `make`, inside it. */
/**
 * The full rc.112 `Deferred` surface. Every method is that module's own call,
 * with the line the census row cites
 * (`docs/research/2026-09-03-deep-state-models.md` §1.2, §2.2).
 *
 * A `Deferred` has two optional fields and no tag: `effect` (the stored
 * completion) and `resumes` (`Deferred.ts:58-61`). Every completion below ends
 * in `doneUnsafe` (`:1648-1662`), which answers `false` and changes nothing
 * when a completion is already stored, and otherwise stores it, **clears the
 * waiter array before resuming**, and resumes every waiter in registration
 * order with the stored effect.
 */

/** The primitive table: a `code` names a completion, the way `PrimInterp`
 * names one in Lean. `ran` records which of them were actually *run*, which is
 * what separates `completeWith` (stores, never runs) from `complete` (runs the
 * effect once through `into`). */
const ran: number[] = []
const bodyOf = (code: number): Effect.Effect<number, number> =>
  Effect.flatMap(
    Effect.sync(() => { ran.push(code) }),
    (): Effect.Effect<number, number> =>
      code === 0
        ? Effect.succeed(11)
        : code === 1
        ? Effect.succeed(22)
        : code === 2
        ? Effect.fail(1)
        : code === 3
        ? Effect.fail(2)
        : Effect.succeed(code)
  )

/** The exit table, for the `Exit`-taking rows. `Exit.succeed` — `Exit.ts:216`;
 * `Exit.fail` — `Exit.ts:276`. */
const exitOf = (code: number): Exit.Exit<number, number> =>
  code % 2 === 0 ? Exit.succeed(11 * (code + 1)) : Exit.fail(code)

const fullLive: DeferredsFullService = {
  // `Deferred.make` — `Deferred.ts:171`: `sync(() => makeUnsafe())`, and
  // `makeUnsafe` (`:140-145`) leaves both fields `undefined`.
  make: Deferred.make<number, number>(),
  // `Deferred.isDone` — `Deferred.ts:1366`, over `isDoneUnsafe` (`:1382`):
  // done-ness is exactly `self.effect !== undefined`.
  isDone: (cell) => Deferred.isDone(cell),
  // `Deferred.poll` — `Deferred.ts:1414-1416`: a non-blocking sync read that
  // maps the undefined slot to `None`. rc.112 answers the completion *effect*;
  // the family answers the completion *value*, and running an already-stored
  // completion through `Effect.result` observes nothing because the stored
  // primitive is the `succeed`/`fail` the completion put there.
  poll: (cell) => polled(cell),
  // `Deferred.succeed` — `Deferred.ts:1514`: `done(self, exitSucceed(value))`.
  succeed: (cell, value) => Deferred.succeed(cell, value),
  // `Deferred.fail` — `Deferred.ts:669`: `done(self, exitFail(error))`.
  fail: (cell, error) => Deferred.fail(cell, error),
  // `Deferred.failCause` — `Deferred.ts:877`: `done(self, exitFailCause(cause))`.
  // `Cause.fail` — `Cause.ts:482`.
  failCause: (cell, error) => Deferred.failCause(cell, Cause.fail(error)),
  // `Deferred.die` — `Deferred.ts:1087`: `done(self, exitDie(defect))`.
  die: (cell, defect) => Deferred.die(cell, defect),
  // `Deferred.interrupt` — `Deferred.ts:1231-1232`: `withFiber(fiber =>
  // interruptWith(self, fiber.id))`, so the recorded interruptor is the
  // *completing* fiber and not the awaiting one.
  interrupt: (cell) => Deferred.interrupt(cell),
  // `Deferred.interruptWith` — `Deferred.ts:1332-1337`: `failCause(self,
  // causeInterrupt(fiberId))`, i.e. an ordinary stored failure completion and
  // not a distinguished state.
  interruptWith: (cell, fiberId) => Deferred.interruptWith(cell, fiberId),
  // `Deferred.complete` — `Deferred.ts:330-335`: a `suspend`, so the done
  // check happens at run time; already done answers `false` *without running
  // the effect*, and otherwise the effect goes through `into`, which memoizes
  // its result.
  complete: (cell, code) => Deferred.complete(cell, bodyOf(code)),
  // `Deferred.completeWith` — `Deferred.ts:456-461`: stores the given effect
  // as the completion **without running it**, so a waiter is resumed with that
  // primitive rather than with a computed result.
  completeWith: (cell, code) => Deferred.completeWith(cell, bodyOf(code)),
  // `Deferred.done` — `Deferred.ts:570-571`: literally `completeWith as any`.
  // Since an `Exit` *is* an `Effect`, completing from an `Exit` stores that
  // `Exit`, which is why an `Exit` completion is shared and an arbitrary
  // effect completion is re-run per awaiter.
  done: (cell, code) => Deferred.done(cell, exitOf(code)),
  // `Deferred.into` — `Deferred.ts:1774-1784`: runs the body under an
  // uninterruptible mask with interruptibility restored only inside, takes the
  // body's `Exit`, and completes with it, so an interrupted body still
  // completes the cell.
  into: (code, cell) => Deferred.into(bodyOf(code), cell),
  // `Deferred.await` — `Deferred.ts:173-186`, `internalEffect.callback`
  // (`internal/effect.ts:1163-1169`): resumes at once when done, otherwise
  // lazily creates `resumes`, appends its own resume, and returns a cleanup
  // that splices it out.
  awaitValue: (cell) => Deferred.await(cell),
  ran: Effect.sync(() => ran.slice())
}

const deferredProgram = (
  body: (n: number) => Effect.Effect<number, number, Deferreds>,
  argument: number
) =>
  Effect.gen(function* () {
    const service = traceService(DeferredsRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(Deferreds, service))
  })

const fullProgram = (
  body: (n: number) => Effect.Effect<unknown, number, DeferredsFull>,
  argument: number
) =>
  Effect.gen(function* () {
    const service = traceService(DeferredsFullRows, fullLive, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(DeferredsFull, service))
  })

const programs: Record<string, Effect.Effect<unknown, number, never>> = {
  deferredSucceedAwait: deferredProgram(deferredSucceedAwait, 7),
  deferredFailAwait: deferredProgram(deferredFailAwait, 5),
  deferredDoubleComplete: deferredProgram(deferredDoubleComplete, 4),
  deferredPollPending: deferredProgram(deferredPollPending, 6),
  deferredTwoHandles: deferredProgram(deferredTwoHandles, 8),
  deferredPendingAwait: deferredProgram(deferredPendingAwait, 1),
  completionShapes: fullProgram(deferredCompletionShapes, 3),
  interruptIsAFailure: fullProgram(deferredInterruptIsAFailure, 9),
  completeWithStoresEffect: fullProgram(deferredCompleteWithStoresEffect, 2),
  doneIsCompleteWith: fullProgram(deferredDoneIsCompleteWith, 4),
  intoUninterruptible: fullProgram(deferredIntoUninterruptible, 6)
}
/** The one program whose run parks; every other program must settle on its own. */
const stalls = name === "deferredPendingAwait"

const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(
  program,
  sink,
  stalls ? { budget, maxOpsBeforeYield, stallMs } : { budget, maxOpsBeforeYield }
)
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
  foreign: ["flagToNat@./atoms.ts", "pollValue@./atoms.ts", "addNat@./atoms.ts"]
}))
