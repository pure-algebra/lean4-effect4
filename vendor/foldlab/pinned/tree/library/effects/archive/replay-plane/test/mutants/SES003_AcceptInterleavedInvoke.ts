import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a reducer that accepts a second invocation while a delegation is outstanding — the exclusivity refusal, not scheduling luck, is what keeps histories in invocation order."

export const mutant: ReplayReducer = (state, input) =>
  state.status === "active" && state.mode === "record" && input._tag === "Invoke"
    ? {
        result: { _tag: "Delegated" },
        state: { ...state, pending: input.invocation },
        decisions: [{
          _tag: "LiveDelegation",
          operation: input.invocation.op,
          at: state.cursor,
        }],
      }
    : reduce(state, input)
