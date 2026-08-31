import { HashMap, HashSet, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that delivers substituted bytes as a successful load — a successful remote load must deliver exactly the canonical encoding of the node the logical admitted-node load holds at that address."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "FromWire" && input.event._tag === "Ok") {
    const current = HashMap.get(state.inFlight, input.id)
    if (Option.isSome(current) && current.value._tag === "Loading") {
      const key = current.value.key
      const bytes = [...input.event.bytes, 0]
      return {
        result: { _tag: "Delivered", key, bytes },
        state: {
          ...state,
          inFlight: HashMap.remove(state.inFlight, input.id),
          cache: HashSet.add(state.cache, key),
        },
        commands: [],
        decisions: [
          { op: input.id, decision: { _tag: "Verified", key } },
          { op: input.id, decision: { _tag: "Cached", key } },
          { op: input.id, decision: { _tag: "Returned", key } },
        ],
      }
    }
  }
  return step(params, state, input)
}
