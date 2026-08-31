import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a step that breaks session-state well-formedness — the record-mode cursor detaches from the history length."

export const mutant: ReplayReducer = (state, input) => {
  const output = reduce(state, input)
  return output.result._tag === "Appended"
    ? { ...output, state: { ...output.state, cursor: state.cursor + 2 } }
    : output
}
