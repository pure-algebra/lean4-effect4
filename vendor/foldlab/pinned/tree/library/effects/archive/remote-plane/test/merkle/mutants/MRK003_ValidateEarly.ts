import {
  dstep,
  type DStepFunction,
} from "../../../src/internal/merkleDecoder.ts"
import type { MerkleAddress } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a decoder that exposes the length before the final chunk validates — the declared length is vouched for exactly when the final chunk itself verifies against the root."

/** Append a length validation to every transition that emits a chunk. */
export const mutantStep: DStepFunction<MerkleAddress> = (params, state, input) => {
  const output = dstep(params, state, input)
  return output.decisions.some((decision) => decision._tag === "Emitted")
    ? {
      state: output.state,
      decisions: [...output.decisions, { _tag: "LengthValidated" }],
    }
    : output
}
