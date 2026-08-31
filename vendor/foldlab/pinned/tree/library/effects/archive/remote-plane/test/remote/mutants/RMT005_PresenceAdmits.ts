import { HashSet } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that turns presence reports into admission — a server's claim to hold a key populating the cache without any verified bytes ever arriving."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  const output = step(params, state, input)
  if (input._tag !== "FromWire" || input.event._tag !== "BatchResult") return output

  let cache = output.state.cache
  for (const result of input.event.results) {
    if (result._tag === "Found") cache = HashSet.add(cache, result.key)
  }
  return { ...output, state: { ...output.state, cache } }
}
