import { reduce } from "../../src/replay/Reducer.ts"
import type { ReplayReducer } from "../ReplayFixtures.ts"

export const meaning = "Killing this mutant demonstrates the vectors notice a reducer that appends an outcome nobody solicited — without the solicitation refusal, a cross-wired or duplicated outcome enters a durable history silently."

export const mutant: ReplayReducer = (state, input) =>
  state.status === "active" && state.mode === "record" && input._tag === "Recorded"
    ? {
        result: { _tag: "Appended" },
        state: {
          ...state,
          pending: undefined,
          history: [...state.history, { ...input.invocation, outcome: input.outcome }],
          cursor: state.cursor + 1,
        },
        decisions: [{
          _tag: "OccurrenceAppended",
          operation: input.invocation.op,
          at: state.cursor,
        }],
      }
    : reduce(state, input)
