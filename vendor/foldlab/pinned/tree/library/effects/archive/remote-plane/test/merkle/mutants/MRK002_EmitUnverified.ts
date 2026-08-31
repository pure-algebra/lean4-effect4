import {
  disjoint,
  dstep,
  popped,
  type DStepFunction,
} from "../../../src/internal/merkleDecoder.ts"
import type { MerkleAddress } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a decoder that emits unverified bytes — a chunk is emitted only in the branch where its leaf pre-image hashed to exactly the expected subtree address."

/** Emit any chunk presented for an in-range leaf frame. */
export const mutantStep: DStepFunction<MerkleAddress> = (params, state, input) => {
  if (state.status === "active"
    && state.stack.length > 0
    && input._tag === "ChunkNode"
    && !disjoint(params, state.stack[0]!)
    && state.stack[0]!.count <= 1) {
    const frame = state.stack[0]!
    const rest = state.stack.slice(1)
    return {
      state: popped(rest),
      decisions: frame.base + 1 === params.total
        ? [
          { _tag: "Emitted", index: frame.base, bytes: input.bytes },
          { _tag: "LengthValidated" },
        ]
        : [{ _tag: "Emitted", index: frame.base, bytes: input.bytes }],
    }
  }
  return dstep(params, state, input)
}
