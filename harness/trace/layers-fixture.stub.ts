// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the *full-surface* `Layers` fixture the L1/L3 lanes
 * generate. The four-row `Layers` of `layer-fixture.ts` stays exactly as it is
 * — its goldens are pinned — and this declares the rest of rc.112's public
 * `Layer` surface (`docs/research/2026-09-03-deep-state-models.md` §1.3,
 * §2.3).
 *
 * **Layers, memo maps and built contexts are handle indices.** rc.112 keys the
 * memo `Map` on the layer *object* (`Layer.ts:411`, `:438`), so two
 * structurally equal declarations are two memo entries; the model's stand-in
 * is a `LayerId` index into a declared table (§3.3), and a
 * `LAYER-FB-LAYER-IDENTITY` refusal row of the `SCOPE-FB-KEY-IDENTITY` shape
 * is owed. Every combinator row below therefore takes indices and answers the
 * index of the layer or memo map it appended to the tail's table.
 *
 * A **built context** answers as `ReadonlyArray<number>`: the bases of the
 * services it carries, read back through the declared tags. The `Context`
 * object itself is not the identity — `buildWithMemoMap` maps
 * `Context.add(CurrentMemoMap, …)` over it (`Layer.ts:762`), so the wrapper is
 * a fresh object on every build while the service inside is not.
 */
import { Context, Effect } from "effect"

export interface LayersFullService {
  readonly declare: (base: number) => Effect.Effect<number>
  readonly provide: (self: number, that: number) => Effect.Effect<number>
  readonly provideMerge: (self: number, that: number) => Effect.Effect<number>
  readonly merge: (self: number, that: number) => Effect.Effect<number>
  readonly mergeAll: (self: number, that: number) => Effect.Effect<number>
  readonly fresh: (layer: number) => Effect.Effect<number>
  readonly memoize: (layer: number) => Effect.Effect<number>
  readonly orDie: (layer: number) => Effect.Effect<number>
  readonly unwrap: (layer: number) => Effect.Effect<number>
  readonly makeMemoMap: Effect.Effect<number>
  readonly forkMemoMap: (memoMap: number) => Effect.Effect<number>
  readonly buildWithMemoMap: (
    layer: number,
    memoMap: number
  ) => Effect.Effect<ReadonlyArray<number>>
  readonly buildWithScope: (layer: number) => Effect.Effect<ReadonlyArray<number>>
  readonly launch: (layer: number) => Effect.Effect<void>
  readonly provideCount: (base: number) => Effect.Effect<number>
}

export class LayersFull extends Context.Service<LayersFull, LayersFullService>()("LayersFull") {}

/** Operation rows of `LayersFull`, for the trace harness. */
export const LayersFullRows = {
  "declare": { params: 1, answer: "number" },
  "provide": { params: 2, answer: "number" },
  "provideMerge": { params: 2, answer: "number" },
  "merge": { params: 2, answer: "number" },
  "mergeAll": { params: 2, answer: "number" },
  "fresh": { params: 1, answer: "number" },
  "memoize": { params: 1, answer: "number" },
  "orDie": { params: 1, answer: "number" },
  "unwrap": { params: 1, answer: "number" },
  "makeMemoMap": { params: 0, answer: "number" },
  "forkMemoMap": { params: 1, answer: "number" },
  "buildWithMemoMap": { params: 2, answer: "ReadonlyArray<number>" },
  "buildWithScope": { params: 1, answer: "ReadonlyArray<number>" },
  "launch": { params: 1, answer: "void" },
  "provideCount": { params: 1, answer: "number" }
}

/** Lowered from `layerProvideDependencyFirst` over `LayersFull`: `provide`
 * builds the dependency first on the same memo map and scope and combines the
 * two contexts with `identity`, so the dependency's services do not reach the
 * caller; `provideMerge` combines with `Context.merge` and they do. */
export const layerProvideDependencyFirst = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const provided = yield* layers.provide(0, 1)
    const a = yield* layers.buildWithScope(provided)
    const merged = yield* layers.provideMerge(0, 1)
    const b = yield* layers.buildWithScope(merged)
    return [a, b, n] as const
  })

/** Lowered from `layerMergeParallelScopes` over `LayersFull`. */
export const layerMergeParallelScopes = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const m = yield* layers.merge(0, 1)
    const a = yield* layers.buildWithScope(m)
    const all = yield* layers.mergeAll(0, 2)
    const b = yield* layers.buildWithScope(all)
    return [a, b, n] as const
  })

/** Lowered from `layerMemoParentLookup` over `LayersFull`: a forked memo map
 * sees layers already built by its parent, and a parent hit increments the
 * parent's entry. */
export const layerMemoParentLookup = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const parent = yield* layers.makeMemoMap
    yield* layers.buildWithMemoMap(0, parent)
    const child = yield* layers.forkMemoMap(parent)
    yield* layers.buildWithMemoMap(0, child)
    const c = yield* layers.provideCount(0)
    return [c, n] as const
  })

/**
 * Lowered from `layerFreshDropsMemoization` over `LayersFull`: `fresh` calls
 * the layer's build with a brand new memo map, so it rebuilds *even against a
 * shared memo map*; a memoized layer against that same map builds once.
 *
 * Both halves go through `buildWithMemoMap` and not `buildWithScope`, because
 * `buildWithScope` replaces only the scope — the memo map is still
 * `CurrentMemoMap.forkOrCreate(fiber.context)` (`Layer.ts:974-979`,
 * `:585-588`), so with no ambient `CurrentMemoMap` two `buildWithScope` calls
 * get *two different memo maps* and share no memoization at all. That is the
 * census row `layer.build-with-scope-still-forks-memo`, and it is why a
 * memoization witness has to name its memo map.
 */
export const layerFreshDropsMemoization = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const m = yield* layers.makeMemoMap
    const f = yield* layers.fresh(1)
    yield* layers.buildWithMemoMap(f, m)
    yield* layers.buildWithMemoMap(f, m)
    const freshCount = yield* layers.provideCount(1)
    const g = yield* layers.memoize(1)
    yield* layers.buildWithMemoMap(g, m)
    yield* layers.buildWithMemoMap(g, m)
    const memoCount = yield* layers.provideCount(1)
    return [freshCount, memoCount, n] as const
  })

/** Lowered from `layerDeclareIdentity` over `LayersFull`: two structurally
 * equal declarations are two memo entries **in the same memo map**, because
 * rc.112 keys the memo `Map` on the layer object (`Layer.ts:411`, `:438`) and
 * not on the description. */
export const layerDeclareIdentity = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const m = yield* layers.makeMemoMap
    const a = yield* layers.declare(2)
    const b = yield* layers.declare(2)
    yield* layers.buildWithMemoMap(a, m)
    yield* layers.buildWithMemoMap(a, m)
    const once = yield* layers.provideCount(2)
    yield* layers.buildWithMemoMap(b, m)
    const twice = yield* layers.provideCount(2)
    return [once, twice, n] as const
  })

/** Lowered from `layerOrDieUnwrap` over `LayersFull`. */
export const layerOrDieUnwrap = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    const d = yield* layers.orDie(0)
    const u = yield* layers.unwrap(d)
    const a = yield* layers.buildWithScope(u)
    return [a, n] as const
  })

/** Lowered from `layerLaunchHoldsScope` over `LayersFull`: `launch` builds the
 * layer inside a fresh scope and then runs `never`, so the run parks and the
 * golden is a frontier. */
export const layerLaunchHoldsScope = (n: number) =>
  Effect.gen(function*() {
    const layers = yield* LayersFull
    yield* layers.launch(0)
    return n
  })
