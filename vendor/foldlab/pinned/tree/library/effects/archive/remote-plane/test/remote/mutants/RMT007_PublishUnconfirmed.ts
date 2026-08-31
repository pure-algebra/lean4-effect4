import { HashMap, Option } from "effect"
import { step } from "../../../src/internal/remoteMachine.ts"
import type { RemoteStepShape } from "../../conformance/harness.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a client that publishes a root whose closure never stood confirmed — a reader could resolve the root before its children exist remotely."

export const mutantStep: RemoteStepShape["step"] = (params, state, input) => {
  if (input._tag === "Request"
    && input.op._tag === "PublishRoot"
    && Option.isNone(HashMap.get(state.inFlight, input.id))) {
    const command = { _tag: "PublishRoot" as const, key: input.op.key }
    return {
      result: { _tag: "Commanded" },
      state: {
        ...state,
        inFlight: HashMap.set(state.inFlight, input.id, {
          _tag: "Publishing",
          key: input.op.key,
        }),
      },
      commands: [{ op: input.id, command }],
      decisions: [{ op: input.id, decision: { _tag: "Issued", command } }],
    }
  }
  return step(params, state, input)
}
