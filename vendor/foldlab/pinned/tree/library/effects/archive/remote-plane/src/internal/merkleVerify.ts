/** Inclusion reconstruction mirrored from Effects/Merkle/Verify.lean. */
import { Equal, Option } from "effect"
import type { Bytes } from "./merkleChunk.ts"
import { rebuildInclusion } from "./merkleGraph.ts"
import type { RebuildInclusionInput } from "./merkleGraph.ts"
import type { HP } from "./merkleTree.ts"

export type BranchRootInput<A> = RebuildInclusionInput<A>

export interface VerifyInclusionInput<A> {
  readonly P: HP<A>
  readonly index: number
  readonly count: number
  readonly bytes: Bytes
  readonly siblings: ReadonlyArray<A>
  readonly expectedRoot: A
}

/**
 * Recompute an opening's root. The walk derives every side from index and
 * count; the proof controls sibling values only.
 */
export const branchRoot = <A>(input: BranchRootInput<A>): Option.Option<A> => {
  return rebuildInclusion(input)
}

export const verifyInclusion = <A>({
  P,
  index,
  count,
  bytes,
  siblings,
  expectedRoot,
}: VerifyInclusionInput<A>): boolean => {
  if (!(index < count)) return false
  const rebuilt = branchRoot({ P, base: 0, index, count, bytes, siblings })
  return Option.isSome(rebuilt) && Equal.equals(rebuilt.value, expectedRoot)
}
