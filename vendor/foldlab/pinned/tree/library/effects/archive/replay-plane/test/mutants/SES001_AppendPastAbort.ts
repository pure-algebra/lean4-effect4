import { appendRecord, reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice recording past an append failure — a history that is a gapped subsequence, not a truthful prefix."

export const mutant: ReplayReducer = (state, input) =>
  state.status === "aborted" && input._tag === "Recorded"
    ? appendRecord(state, input.invocation, input.outcome)
    : reduce(state, input)
