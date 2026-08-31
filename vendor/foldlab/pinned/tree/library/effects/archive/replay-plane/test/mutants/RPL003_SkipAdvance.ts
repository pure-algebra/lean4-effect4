import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a match that consumes zero occurrences — the same recorded outcome would answer forever."

export const mutant: ReplayReducer = (state, input) => {
  const output = reduce(state, input)
  return output.result._tag === "Substituted"
    ? { ...output, state: { ...output.state, cursor: state.cursor } }
    : output
}
