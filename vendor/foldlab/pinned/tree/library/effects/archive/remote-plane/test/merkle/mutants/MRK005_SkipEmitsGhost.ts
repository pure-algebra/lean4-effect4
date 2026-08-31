import {
  disjoint,
  dstep,
  popped,
  type DStepFunction,
} from "../../../src/internal/merkleDecoder.ts"
import type { MerkleAddress } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a slice decoder that emits bytes for skipped subtrees — a slice emits exactly what the whole decode would emit at those offsets, never more."

/** Emit an empty ghost chunk when a disjoint frame is skipped. */
export const mutantStep: DStepFunction<MerkleAddress> = (params, state, input) => {
  if (state.status === "active"
    && state.stack.length > 0
    && input._tag === "SkipNode"
    && disjoint(params, state.stack[0]!)) {
    const frame = state.stack[0]!
    const rest = state.stack.slice(1)
    return {
      state: popped(rest),
      decisions: [{ _tag: "Emitted", index: frame.base, bytes: [] }],
    }
  }
  return dstep(params, state, input)
}
