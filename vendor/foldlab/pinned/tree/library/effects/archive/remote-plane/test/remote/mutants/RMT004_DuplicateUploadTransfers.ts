import { HashMap, HashSet, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that re-transfers content already admitted for its key — an already-present exact-digest upload must resolve as success with zero additional transfer commands."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "Request" && input.op._tag === "Upload") {
    const { bytes, key } = input.op
    if (Option.isNone(HashMap.get(state.inFlight, input.id))
      && params.size(bytes) <= params.budgets.maxBytes
      && !HashSet.has(state.rejected, [key, bytes] as const)
      && params.verify(key, bytes)
      && HashSet.has(state.cache, key)) {
      const command = { _tag: "Upload" as const, key, bytes }
      return {
        result: { _tag: "Commanded" },
        state: {
          ...state,
          inFlight: HashMap.set(state.inFlight, input.id, { _tag: "Uploading", key, bytes }),
        },
        commands: [{ op: input.id, command }],
        decisions: [
          { op: input.id, decision: { _tag: "Verified", key } },
          { op: input.id, decision: { _tag: "Issued", command } },
        ],
      }
    }
  }
  return step(params, state, input)
}
