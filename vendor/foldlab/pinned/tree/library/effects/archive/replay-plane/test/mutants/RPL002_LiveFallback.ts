import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a replay mismatch falling through to a live adapter — the decision trace, not a separate oracle, is what convicts the fallback."

export const mutant: ReplayReducer = (state, input) => {
  const output = reduce(state, input)
  if (state.mode !== "replay" || output.result._tag !== "Rejected") return output
  return {
    ...output,
    decisions: [
      ...output.decisions,
      { _tag: "LiveDelegation", operation: "fallback", at: state.cursor },
    ],
  }
}
