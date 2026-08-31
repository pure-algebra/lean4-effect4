/**
 * Node admission helpers and the chain genesis.
 *
 * The store's own admission law does the ordering work: `put` refuses a
 * dangling reference, so children-first (context and output before the entry
 * that references them) is FORCED, not a convention — the Lean `wf` predicate
 * realized by the existing `CasStore`.
 */
import { Effect } from "effect"
import { Cas } from "../../src/index.ts"
import { KindTag } from "./kinds.ts"

export const putNode = (
  tag: number,
  payload: Uint8Array,
  refs: ReadonlyArray<{ readonly id: Cas.ContentId; readonly expectedTag: number }>,
): Effect.Effect<Cas.ContentId, Cas.Error, Cas.Store> =>
  Effect.gen(function* () {
    const store = yield* Cas.Store
    return yield* store.put(Cas.NodeInput.make({
      kind: { version: Cas.SchemeVersion, tag },
      payload,
      refs,
    }))
  })

/** The empty journal — mirrors `Tree.genesis`. */
export const genesis: Effect.Effect<Cas.ContentId, Cas.Error, Cas.Store> =
  putNode(KindTag.entry, new Uint8Array(0), [])
