/** Public replay-session carriers shared by the pure reducer and runtime. */
import { Schema } from "effect"
import type { ContentId } from "../cas/Node.ts"
import type { DecisionTrace } from "./Decision.ts"

/** Record invokes live adapters and appends history; replay is hermetic. */
export const ReplayMode = Schema.Literals(["record", "replay"])
export type ReplayMode = typeof ReplayMode.Type

/** The eight ratified mismatch categories (GR-2). Request-side, checked at
 * the cursor: operation, revision, request, history exhausted.
 * Completion-side: unconsumed suffix. Outcome-side, checked at consumption:
 * outcome inadmissible. Protocol-side, checked in record mode: delegation
 * outstanding (a second invocation while one delegation is in flight) and
 * unsolicited outcome (a recorded outcome no outstanding delegation asked
 * for, or naming a different invocation than registered). "Order mismatch"
 * is deliberately not a category; CAS storage failures are a distinct
 * typed family. */
export const MismatchCategory = Schema.Literals([
  "OperationMismatch",
  "RevisionMismatch",
  "RequestMismatch",
  "HistoryExhausted",
  "UnconsumedSuffix",
  "OutcomeInadmissible",
  "DelegationOutstanding",
  "UnsolicitedOutcome",
])
export type MismatchCategory = typeof MismatchCategory.Type

/** Channel-preserving recorded outcome envelope (GR-9): success of the
 * declared success Schema or failure of the declared typed-failure Schema.
 * Substitution re-injects through the native Effect channels so recovery
 * combinators fire exactly as they did live. */
export const RecordedOutcome = <S extends Schema.Top, F extends Schema.Top>(
  success: S,
  failure: F,
) =>
  Schema.Union([
    Schema.TaggedStruct("Success", { value: success }),
    Schema.TaggedStruct("Failure", { error: failure }),
  ])

/** A program terminal: success or declared typed failure. */
export type Terminal<A, E> =
  | { readonly _tag: "Succeeded"; readonly value: A }
  | { readonly _tag: "Failed"; readonly error: E }

/** An ambient service caught by the replay-mode tripwire defaults. */
export type AmbientService = "Clock" | "Random"

/** The tagged session outcome (GR-5, GR-8). UnconsumedSuffix is the
 * Rejected case that populates terminalSoFar — the program terminated, but
 * a recorded action was never re-emitted; request-side mismatches leave it
 * empty. The durable witness Schema is internal until the M3 re-freeze. */
export type SessionOutcome<A, E> =
  | { readonly _tag: "Completed"; readonly terminal: Terminal<A, E> }
  | {
      readonly _tag: "Rejected"
      readonly category: MismatchCategory
      readonly at: number
      readonly terminalSoFar?: Terminal<A, E>
    }
  | { readonly _tag: "Violated"; readonly service: AmbientService }

/** The durable result of one session attempt. Every outcome carries the
 * persisted witness root. Record mode also returns its newly appended history
 * root when the attempt recorded at least one occurrence; replay mode returns
 * the history root it consumed. */
export interface SessionResult<A, E> {
  readonly outcome: SessionOutcome<A, E>
  readonly witness: ContentId
  readonly history?: ContentId
}

/** Optional durable projections for a program's terminal channels. When
 * omitted, values unsupported by the internal witness carrier are recorded as
 * an explicit unrepresentable marker rather than failing the session. */
export interface TerminalSchemas<A, E> {
  readonly success: Schema.Codec<A, unknown, never, never>
  readonly failure: Schema.Codec<E, unknown, never, never>
}

export interface SessionOptions<A, E> {
  readonly mode: ReplayMode
  /** Stable identity for this attempt, persisted verbatim in its witness.
   * When omitted the runtime uses `execution-${counter}` from a process-local
   * development counter. That default is not globally unique: collisions
   * across processes and process restarts are expected. Production callers
   * that correlate witnesses must supply their own identity. */
  readonly executionId?: string
  readonly history?: ContentId
  readonly terminal?: TerminalSchemas<A, E>
}

/** A channel-preserving outcome stored in one history occurrence. */
export type Outcome<A, E> =
  | { readonly _tag: "Success"; readonly value: A }
  | { readonly _tag: "Failure"; readonly error: E }

/** One canonical invocation. Operation and request are string identities at
 * this boundary; branded string identities remain assignable without losing
 * their stronger application-level types. */
export interface Invocation<Op extends string = string, Req extends string = string> {
  readonly op: Op
  readonly revision: number
  readonly request: Req
}

/** One logical occurrence in the flat replay history. */
export interface HistoryEntry<
  Op extends string = string,
  Req extends string = string,
  Val = string,
  Err = string,
> extends Invocation<Op, Req> {
  readonly outcome: Outcome<Val, Err>
}

/** Structural session status. Aborted sessions absorb every later input. */
export type SessionStatus = "active" | "aborted"

/** State threaded through the pure reducer. `pending` carries the
 * invocation a record-mode live delegation is currently executing — set by
 * the record-mode invoke, cleared by the solicited append; record-mode
 * delegation is exclusive, so a present value refuses further invocations
 * until the outcome arrives. */
export interface SessionState<
  Op extends string = string,
  Req extends string = string,
  Val = string,
  Err = string,
> {
  readonly mode: ReplayMode
  readonly status: SessionStatus
  readonly history: ReadonlyArray<HistoryEntry<Op, Req, Val, Err>>
  readonly cursor: number
  readonly pending?: Invocation<Op, Req> | undefined
}

/** Reducer input. The interpreter emits Recorded only after live delegation
 * returns and AppendFailed only when the record store refuses that outcome. */
export type Input<
  Op extends string = string,
  Req extends string = string,
  Val = string,
  Err = string,
> =
  | { readonly _tag: "Invoke"; readonly invocation: Invocation<Op, Req> }
  | {
      readonly _tag: "Recorded"
      readonly invocation: Invocation<Op, Req>
      readonly outcome: Outcome<Val, Err>
    }
  | { readonly _tag: "AppendFailed" }
  | { readonly _tag: "Complete"; readonly terminal: Terminal<Val, Err> }

/** What the caller of one reducer step observes. */
export type StepResult<Val = string, Err = string> =
  | { readonly _tag: "Substituted"; readonly outcome: Outcome<Val, Err> }
  | { readonly _tag: "Delegated" }
  | { readonly _tag: "Appended" }
  | { readonly _tag: "Rejected"; readonly category: MismatchCategory; readonly at: number }
  | { readonly _tag: "SessionOutcome"; readonly outcome: SessionOutcome<Val, Err> }
  | { readonly _tag: "Aborted" }
  | { readonly _tag: "Absorbed" }

/** One step's result, successor state, and emitted decisions. */
export interface StepOut<
  Op extends string = string,
  Req extends string = string,
  Val = string,
  Err = string,
> {
  readonly result: StepResult<Val, Err>
  readonly state: SessionState<Op, Req, Val, Err>
  readonly decisions: DecisionTrace
}

/** The state invariant mirrored by SessionState.WF. */
export const isWellFormed = <
  Op extends string,
  Req extends string,
  Val,
  Err,
>(state: SessionState<Op, Req, Val, Err>): boolean =>
  Number.isInteger(state.cursor) &&
  state.cursor >= 0 &&
  state.cursor <= state.history.length &&
  (state.mode === "replay" || state.cursor === state.history.length) &&
  (state.mode === "record" || state.pending === undefined)
