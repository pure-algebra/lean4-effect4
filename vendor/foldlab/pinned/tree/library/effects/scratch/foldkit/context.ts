/**
 * Context assembly — the fold over digests (Lean `foldContext`).
 *
 * Fail-closed by construction: a dangling address fails as `ContentNotFound`
 * through the store, an unregistered tag as `UnknownKind`. Render dispatch is
 * the total registry, so the fold is defined for every admitted node.
 */
import { Effect } from "effect"
import { Cas } from "../../src/index.ts"
import { sortOf } from "./kinds.ts"
import { registry } from "./semantics.ts"

export const renderNode = (node: Cas.NodeInput): Effect.Effect<string, Cas.Error> => {
  const kind = sortOf(node.kind.tag)
  return kind === undefined
    ? Effect.fail(new Cas.UnknownKind(node.kind))
    : Effect.succeed(registry[kind].render(node))
}

export const foldContext = (
  ids: ReadonlyArray<Cas.ContentId>,
): Effect.Effect<string, Cas.Error, Cas.Store> =>
  Effect.gen(function* () {
    const store = yield* Cas.Store
    const fragments: Array<string> = []
    for (const id of ids) {
      const node = yield* store.load(id)
      fragments.push(yield* renderNode(node))
    }
    return fragments.join("\n\n")
  })
