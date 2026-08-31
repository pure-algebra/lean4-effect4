import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a mismatch that fails open — consuming the occurrence it rejected instead of freezing the cursor."

export const mutant: ReplayReducer = (state, input) => {
  const output = reduce(state, input)
  return output.result._tag === "Rejected"
    ? { ...output, state: { ...output.state, cursor: state.cursor + 1 } }
    : output
}
