import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a completion that hides recorded actions never re-emitted — the same final value must not mask an unconsumed suffix."

export const mutant: ReplayReducer = (state, input) => {
  const output = reduce(state, input)
  if (
    input._tag !== "Complete" ||
    output.result._tag !== "SessionOutcome" ||
    output.result.outcome._tag !== "Rejected" ||
    output.result.outcome.category !== "UnconsumedSuffix"
  ) return output
  return {
    result: {
      _tag: "SessionOutcome",
      outcome: { _tag: "Completed", terminal: input.terminal },
    },
    state,
    decisions: [{ _tag: "Completed", consumed: state.cursor }],
  }
}
