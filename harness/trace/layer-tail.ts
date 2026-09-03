import { Context, Effect, Exit, Layer, Ref, Scope } from "effect"
import {
  Layers,
  LayersRows,
  layerBuildMemo,
  layerBuildOnce,
  layerFreshRebuild,
  layerFreshRegion,
  layerFreshRelease,
  layerRebuildAfterClose,
  layerReleaseOrder,
  layerScopedRelease
} from "./layer-fixture.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Layers` family: rc.112's own layer machinery, wrapped
 * so the shared alphabet can see it.
 *
 * - Each declared layer is `Layer.effect(Tag, construction)`, so it is
 *   memoized through `fromBuildMemo`. `build` is
 *   `Layer.buildWithMemoMap(layer, memoMap, root)` and answers
 *   `Context.get(context, Tag)` — the **service object**, which the memo entry
 *   replays unchanged on a hit. The `Context` itself is not the identity:
 *   `buildWithMemoMap` maps `Context.add(CurrentMemoMap, …)` over it, so the
 *   wrapper is a fresh object on every build while the service inside is not.
 * - `provideCount` is a counter written by the construction effect itself.
 * - `scopeOf` is the layer scope `memoMapBuild` allocated for that
 *   construction: the construction effect reads it from `Effect.scope`
 *   (`effectContext` builds through `Scope.provide`) and records it against
 *   the service it returns.
 * - `close` is `Scope.close(root, Exit.void)`, and its answer is the slice of
 *   the release log this close appended: the services rc.112 actually
 *   released, in the order it released them. Each construction registers a
 *   finalizer on its own layer scope that appends its service.
 * - Layer 3 is `Layer.fresh(layer 1)`: a distinct layer identity built through
 *   a private memo map, so it constructs on every build, and its
 *   constructions are counted against layer 1 because it runs layer 1's
 *   construction effect.
 *
 * Neither a `Ref` nor a `Scope` reaches the wire as an object. `registerHandle`
 * brands both and `wire` encodes them as their index in first-seen order,
 * which is the order `Effect4/Layer/LayerFamily.lean` hands out handles in.
 */

// The brands rc.112 stamps on a Ref and on a Scope (`Ref.ts` and
// `internal/effect.ts` type ids). Both are string keys, not exported values.
const RefTypeId = "~effect/Ref"
const ScopeTypeId = "~effect/Scope"
registerHandle((value) => RefTypeId in value || ScopeTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "buildOnce"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

/** Three distinct service tags, one per ordinary declared layer. */
class L0 extends Context.Service<L0, Ref.Ref<number>>()("L0") {}
class L1 extends Context.Service<L1, Ref.Ref<number>>()("L1") {}
class L2 extends Context.Service<L2, Ref.Ref<number>>()("L2") {}

/** layer id -> how many times its construction effect ran */
const counts = new Map<number, number>()
/** service -> the layer scope `memoMapBuild` allocated for its construction */
const scopeOfService = new WeakMap<Ref.Ref<number>, Scope.Scope>()
/** every service released so far, oldest first */
const releaseLog: Array<Ref.Ref<number>> = []

/** The construction effect of layer `base`: it counts itself, takes the layer
 * scope it was given, and registers the finalizer that reports its release. */
const construct = (base: number) =>
  Effect.gen(function* () {
    const layerScope = yield* Effect.scope
    counts.set(base, (counts.get(base) ?? 0) + 1)
    const service = yield* Ref.make(base)
    scopeOfService.set(service, layerScope)
    yield* Scope.addFinalizerExit(layerScope, () =>
      Effect.sync(() => { releaseLog.push(service) }))
    return service
  })

const layer0 = Layer.effect(L0, construct(0))
const layer1 = Layer.effect(L1, construct(1))
const layer2 = Layer.effect(L2, construct(2))
const layer3 = Layer.fresh(layer1)

const declared = [
  { layer: layer0, tag: L0 },
  { layer: layer1, tag: L1 },
  { layer: layer2, tag: L2 },
  { layer: layer3, tag: L1 }
] as unknown as ReadonlyArray<{
  readonly layer: Layer.Layer<never, never, never>
  readonly tag: Context.Key<never, Ref.Ref<number>>
}>

/** The memo map and the enclosing scope are the family's own state, made
 * before the `run` sentinel so only the operations are compared. */
const memoMap = Layer.makeMemoMapUnsafe()
const root = Scope.makeUnsafe()

const live = {
  build: (layer: number) =>
    Effect.gen(function* () {
      const entry = declared[layer]
      if (entry === undefined) throw new Error(`unknown layer ${layer}`)
      const context = yield* Layer.buildWithMemoMap(entry.layer, memoMap, root)
      return Context.get(context, entry.tag)
    }),
  provideCount: (layer: number) => Effect.sync(() => counts.get(layer) ?? 0),
  scopeOf: (service: Ref.Ref<number>) =>
    Effect.sync(() => {
      const scope = scopeOfService.get(service)
      if (scope === undefined) throw new Error("no layer scope for that service")
      return scope as Scope.Closeable
    }),
  close: Effect.gen(function* () {
    const before = releaseLog.length
    yield* Scope.close(root, Exit.void)
    return releaseLog.slice(before)
  })
}

const layerProgram = (body: (n: number) => Effect.Effect<unknown, never, Layers>) =>
  Effect.gen(function* () {
    const service = traceService(LayersRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(Layers, service))
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  buildOnce: layerProgram(layerBuildOnce),
  buildMemo: layerProgram(layerBuildMemo),
  releaseOrder: layerProgram(layerReleaseOrder),
  scopedRelease: layerProgram(layerScopedRelease),
  freshRebuild: layerProgram(layerFreshRebuild),
  freshRegion: layerProgram(layerFreshRegion),
  freshRelease: layerProgram(layerFreshRelease),
  rebuildAfterClose: layerProgram(layerRebuildAfterClose)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(program, sink, { budget, maxOpsBeforeYield })
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
  foreign: []
}))
