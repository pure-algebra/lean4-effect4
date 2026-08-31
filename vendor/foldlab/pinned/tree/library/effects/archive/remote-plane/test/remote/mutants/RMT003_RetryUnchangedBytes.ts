import { HashMap, HashSet, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that retries an upload with unchanged, already-rejected content — an integrity failure must be terminal for those bytes."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "Request" && input.op._tag === "Upload") {
    const { bytes, key } = input.op
    if (Option.isNone(HashMap.get(state.inFlight, input.id))
      && HashSet.has(state.rejected, [key, bytes] as const)) {
      const command = { _tag: "Upload" as const, key, bytes }
      return {
        result: { _tag: "Commanded" },
        state: {
          ...state,
          inFlight: HashMap.set(state.inFlight, input.id, { _tag: "Uploading", key, bytes }),
        },
        commands: [{ op: input.id, command }],
        decisions: [{ op: input.id, decision: { _tag: "Issued", command } }],
      }
    }
  }
  return step(params, state, input)
}
