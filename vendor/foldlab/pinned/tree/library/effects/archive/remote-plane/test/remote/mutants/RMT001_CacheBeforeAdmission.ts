import { HashMap, HashSet, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that caches and returns un-verified wire bytes — a wire-supplied digest treated as an identity instead of a routing hint."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "FromWire" && input.event._tag === "Ok") {
    const current = HashMap.get(state.inFlight, input.id)
    if (Option.isSome(current) && current.value._tag === "Loading") {
      const key = current.value.key
      return {
        result: { _tag: "Delivered", key, bytes: input.event.bytes },
        state: {
          ...state,
          inFlight: HashMap.remove(state.inFlight, input.id),
          cache: HashSet.add(state.cache, key),
        },
        commands: [],
        decisions: [
          { op: input.id, decision: { _tag: "Cached", key } },
          { op: input.id, decision: { _tag: "Returned", key } },
        ],
      }
    }
  }
  return step(params, state, input)
}
