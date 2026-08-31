import { HashMap, HashSet, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that admits and confirms a key at an interruption point — semantic residue from an operation that never completed."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "FromWire" && input.event._tag === "Interrupted") {
    const current = HashMap.get(state.inFlight, input.id)
    if (Option.isSome(current) && current.value._tag !== "FindingMissing") {
      const output = step(params, state, input)
      return {
        ...output,
        state: {
          ...output.state,
          cache: HashSet.add(output.state.cache, current.value.key),
          confirmed: HashSet.add(output.state.confirmed, current.value.key),
        },
      }
    }
  }
  return step(params, state, input)
}
