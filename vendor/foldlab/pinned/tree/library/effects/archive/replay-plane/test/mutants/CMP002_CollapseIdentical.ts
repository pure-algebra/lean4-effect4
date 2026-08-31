import { reduce } from "../../src/replay/Reducer.ts"
import type { Outcome } from "../../src/replay/Session.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice identical invocation content collapsing into one occurrence — request-content-keyed reuse answering an occurrence."

const outcomesEqual = <Val, Err>(
  left: Outcome<Val, Err>,
  right: Outcome<Val, Err>,
): boolean => left._tag === right._tag && (
  left._tag === "Success" && right._tag === "Success"
    ? left.value === right.value
    : left._tag === "Failure" && right._tag === "Failure" && left.error === right.error
)

export const mutant: ReplayReducer = (state, input) => {
  if (input._tag !== "Recorded") return reduce(state, input)
  const last = state.history[state.history.length - 1]
  const identical = last !== undefined &&
    last.op === input.invocation.op &&
    last.revision === input.invocation.revision &&
    last.request === input.invocation.request &&
    outcomesEqual(last.outcome, input.outcome)
  if (!identical) return reduce(state, input)
  return {
    result: { _tag: "Appended" },
    state,
    decisions: [{
      _tag: "OccurrenceAppended",
      operation: input.invocation.op,
      at: state.cursor - 1,
    }],
  }
}
