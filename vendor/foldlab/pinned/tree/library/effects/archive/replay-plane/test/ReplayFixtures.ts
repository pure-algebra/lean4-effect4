import { Effect, Schema } from "effect"
import type { Decision } from "../src/replay/Decision.ts"
import { reduce } from "../src/replay/Reducer.ts"
import {
  isWellFormed,
  type Input,
  type SessionState,
  type StepResult,
} from "../src/replay/Session.ts"
import {
  assertFamilyRows,
  ManifestModel,
  type FamilyBinding,
} from "./conformance/harness.ts"

const OutcomeSchema = Schema.Union([
  Schema.TaggedStruct("Success", { value: Schema.String }),
  Schema.TaggedStruct("Failure", { error: Schema.String }),
])

const TerminalSchema = Schema.Union([
  Schema.TaggedStruct("Succeeded", { value: Schema.String }),
  Schema.TaggedStruct("Failed", { error: Schema.String }),
])

const InvocationSchema = Schema.Struct({
  op: Schema.String,
  request: Schema.String,
  revision: Schema.Natural,
})

const HistoryEntrySchema = Schema.Struct({
  op: Schema.String,
  outcome: OutcomeSchema,
  request: Schema.String,
  revision: Schema.Natural,
})

const SessionStateSchema = Schema.Struct({
  cursor: Schema.Natural,
  history: Schema.Array(HistoryEntrySchema),
  mode: Schema.Literals(["record", "replay"]),
  status: Schema.Literals(["active", "aborted"]),
  pending: Schema.optionalKey(InvocationSchema),
})

const InputSchema = Schema.Union([
  Schema.TaggedStruct("Invoke", { invocation: InvocationSchema }),
  Schema.TaggedStruct("Recorded", {
    invocation: InvocationSchema,
    outcome: OutcomeSchema,
  }),
  Schema.TaggedStruct("AppendFailed", {}),
  Schema.TaggedStruct("Complete", { terminal: TerminalSchema }),
])

const MismatchCategorySchema = Schema.Literals([
  "OperationMismatch",
  "RevisionMismatch",
  "RequestMismatch",
  "HistoryExhausted",
  "UnconsumedSuffix",
  "OutcomeInadmissible",
  "DelegationOutstanding",
  "UnsolicitedOutcome",
])

const DecisionSchema = Schema.Union([
  Schema.TaggedStruct("LiveDelegation", {
    at: Schema.Natural,
    operation: Schema.String,
  }),
  Schema.TaggedStruct("OccurrenceAppended", {
    at: Schema.Natural,
    operation: Schema.String,
  }),
  Schema.TaggedStruct("RecordedSubstitution", {
    at: Schema.Natural,
    operation: Schema.String,
  }),
  Schema.TaggedStruct("HistoryConsumed", { at: Schema.Natural }),
  Schema.TaggedStruct("TypedRejection", {
    at: Schema.Natural,
    category: MismatchCategorySchema,
  }),
  Schema.TaggedStruct("Completed", { consumed: Schema.Natural }),
])

const SessionOutcomeSchema = Schema.Union([
  Schema.TaggedStruct("Completed", { terminal: TerminalSchema }),
  Schema.TaggedStruct("Rejected", {
    at: Schema.Natural,
    category: MismatchCategorySchema,
    terminalSoFar: Schema.optionalKey(TerminalSchema),
  }),
  Schema.TaggedStruct("Violated", {
    service: Schema.Literals(["Clock", "Random"]),
  }),
])

const StepResultSchema = Schema.Union([
  Schema.TaggedStruct("Substituted", { outcome: OutcomeSchema }),
  Schema.TaggedStruct("Delegated", {}),
  Schema.TaggedStruct("Appended", {}),
  Schema.TaggedStruct("Rejected", {
    at: Schema.Natural,
    category: MismatchCategorySchema,
  }),
  Schema.TaggedStruct("SessionOutcome", { outcome: SessionOutcomeSchema }),
  Schema.TaggedStruct("Aborted", {}),
  Schema.TaggedStruct("Absorbed", {}),
])

const StateSummarySchema = Schema.Struct({
  cursor: Schema.Natural,
  historyLength: Schema.Natural,
  status: Schema.Literals(["active", "aborted"]),
  wellFormed: Schema.Boolean,
})

export const ReplayRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    decisions: Schema.Array(DecisionSchema),
    results: Schema.Array(StepResultSchema),
    state: StateSummarySchema,
  }),
  input: Schema.Struct({
    inputs: Schema.Array(InputSchema),
    state: SessionStateSchema,
  }),
})

export type ReplayFamily =
  | "RPL-002"
  | "RPL-003"
  | "RPL-004"
  | "RPL-005"
  | "SES-001"
  | "SES-002"
  | "SES-003"
  | "CMP-002"

export type ReplayReducer = typeof reduce

export const runReplayFixture = (
  reducer: ReplayReducer,
  initialState: SessionState,
  inputs: ReadonlyArray<Input>,
) => {
  let state = initialState
  const decisions: Array<Decision> = []
  const results: Array<StepResult> = []

  for (const input of inputs) {
    const step = reducer(state, input)
    state = step.state
    results.push(step.result)
    decisions.push(...step.decisions)
  }

  return {
    decisions,
    results,
    state: {
      cursor: state.cursor,
      historyLength: state.history.length,
      status: state.status,
      wellFormed: isWellFormed(state),
    },
  }
}

export const replayFamilyBinding = (
  family: ReplayFamily,
): FamilyBinding<ReplayFamily, typeof ReplayRowSchema> => ({
  family,
  model: ManifestModel,
  row: ReplayRowSchema,
  hasOracle: false,
})

export const replayRowEvaluator = (reducer: ReplayReducer) =>
  (row: typeof ReplayRowSchema.Type) => Effect.succeed(
    runReplayFixture(reducer, row.input.state, row.input.inputs),
  )

/** Decode the pinned family and compare its trace, per-step results, and
 * final state summary structurally. Green and direction-2 lanes deliberately
 * share replayRowEvaluator, so a mutant can only turn the same comparator red. */
export const assertFamily = (
  family: ReplayFamily,
  reducer: ReplayReducer = reduce,
) => assertFamilyRows(replayFamilyBinding(family), replayRowEvaluator(reducer))
