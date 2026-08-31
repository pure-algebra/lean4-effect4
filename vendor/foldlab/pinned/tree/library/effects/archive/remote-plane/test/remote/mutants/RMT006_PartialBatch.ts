import { HashMap, Option } from "effect"
import { notePresence, step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that applies a misaligned batch answer instead of failing the whole batch closed — per-key answers partially applied and substituted across keys."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "FromWire" && input.event._tag === "BatchResult") {
    const current = HashMap.get(state.inFlight, input.id)
    if (Option.isSome(current) && current.value._tag === "FindingMissing") {
      const noted = notePresence(state, input.event.results)
      return {
        result: { _tag: "BatchAnswered", found: noted.found, missing: noted.missing },
        state: {
          ...noted.state,
          inFlight: HashMap.remove(noted.state.inFlight, input.id),
        },
        commands: [],
        decisions: [{
          op: input.id,
          decision: { _tag: "PresenceNoted", found: noted.found, missing: noted.missing },
        }],
      }
    }
  }
  return step(params, state, input)
}
