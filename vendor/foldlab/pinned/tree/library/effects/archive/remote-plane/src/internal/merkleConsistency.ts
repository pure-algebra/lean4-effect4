/** Consistency reconstruction mirrored from Effects/Merkle/Consistency.lean. */
import { Equal, Option } from "effect"
import { rebuildConsistency } from "./merkleGraph.ts"
import type { RebuildConsistencyInput } from "./merkleGraph.ts"
import type { HP } from "./merkleTree.ts"

export type RebuiltPair<A> = readonly [oldRoot: A, newRoot: A]
export type ConsRebuildInput<A> = RebuildConsistencyInput<A>

export interface VerifyConsistencyInput<A> {
  readonly P: HP<A>
  readonly oldSize: number
  readonly newSize: number
  readonly oldRoot: A
  readonly newRoot: A
  readonly proof: ReadonlyArray<A>
}

/**
 * Rebuild old and new roots from a bare proof list. The size-derived walk
 * consumes the list exactly; `anchored` is RFC 9162's b flag.
 */
export const consRebuild = <A>(input: ConsRebuildInput<A>): Option.Option<RebuiltPair<A>> => {
  return rebuildConsistency(input)
}

export const verifyConsistency = <A>({
  P,
  oldSize,
  newSize,
  oldRoot,
  newRoot,
  proof,
}: VerifyConsistencyInput<A>): boolean => {
  if (!(1 <= oldSize && oldSize < newSize)) return false
  const rebuilt = consRebuild({
    P,
    oldAnchor: oldRoot,
    oldSize,
    newSize,
    anchored: true,
    proof,
  })
  return Option.isSome(rebuilt)
    && Equal.equals(rebuilt.value[0], oldRoot)
    && Equal.equals(rebuilt.value[1], newRoot)
}
