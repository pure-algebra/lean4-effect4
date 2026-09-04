import { Context, Effect, Exit, Layer, Option, Ref, Scope } from "effect"
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
import {
  LayersFull,
  LayersFullRows,
  layerDeclareIdentity,
  layerFreshDropsMemoization,
  layerLaunchHoldsScope,
  layerMemoParentLookup,
  layerMergeParallelScopes,
  layerOrDieUnwrap,
  layerProvideDependencyFirst,
  type LayersFullService
} from "./layers-fixture.stub.ts"
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
const stallMs = Number(process.env.EFFECT4_STALL_MS ?? "50")
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

/**
 * The rest of rc.112's public `Layer` surface
 * (`docs/research/2026-09-03-deep-state-models.md` §2.3). Every method is a
 * `Layer.ts` call, cited by line.
 *
 * **Handles are indices into two tail-local tables.** rc.112 keys the memo
 * `Map` on the layer object (`Layer.ts:411`, `:438`), so identity, not
 * structure, decides memoization; the tables below are the model's stand-in
 * for that identity, and the index is what crosses the wire.
 */
const layerTable: Array<Layer.Layer<never, never, never>> =
  declared.map((entry) => entry.layer)
const memoTable: Array<Layer.MemoMap> = [memoMap]

/** Append a layer to the table and answer its index. */
const pushLayer = (layer: Layer.Layer<never, never, never>): number => {
  layerTable.push(layer)
  return layerTable.length - 1
}

const layerAt = (index: number): Layer.Layer<never, never, never> | undefined => layerTable[index]

/** A combinator whose request names an index the table does not hold is a
 * defect: on the host the request is built by the compiler, so the case is
 * unreachable and the service must die rather than build something else. */
const missingLayer = (op: string, index: number): Effect.Effect<never> =>
  Effect.die(new Error(`${op}: the request names no declared layer ${index}`))

/** The bases the built context carries, read back through the declared tags,
 * in tag order. `Context.getOption` — `Context.ts:1636-1709`; `Ref.getUnsafe`
 * — `Ref.ts:1672`. */
const basesOf = (context: Context.Context<never>): ReadonlyArray<number> => {
  const bases: number[] = []
  for (const tag of [L0, L1, L2] as unknown as ReadonlyArray<
    Context.Key<never, Ref.Ref<number>>
  >) {
    const found = Context.getOption(context, tag)
    if (Option.isSome(found)) bases.push(Ref.getUnsafe(found.value))
  }
  return bases
}

const fullLive: LayersFullService = {
  // `Layer.effect` — `Layer.ts:1347`, whose `effectImpl` (`:1435-1439`) goes
  // through `effectContext` (`:1479-1481`) and so through `fromBuildMemo`
  // (`:380-388`). Each call mints a *distinct* layer object over the same tag
  // and the same construction, which is exactly the identity the memo map
  // keys on.
  declare: (base) =>
    Effect.sync(() => {
      const tag = ([L0, L1, L2] as unknown as ReadonlyArray<
        Context.Key<never, Ref.Ref<number>>
      >)[base]
      if (tag === undefined) throw new Error(`declare: no tag for base ${base}`)
      return pushLayer(
        Layer.effect(tag, construct(base)) as unknown as Layer.Layer<never, never, never>
      )
    }),
  // `Layer.provide` — `Layer.ts:2008`, impl `:2345-2348`
  // (`provideWith(self, that, identity)`) over `provideWith` (`:1907-1926`):
  // the dependency is built first on the *same* memo map and the *same* scope,
  // its context is provided to the dependent layer's build, and the combiner
  // is `identity`, so the dependency's services do not reach the caller.
  provide: (self, that) => {
    const a = layerAt(self)
    const b = layerAt(that)
    if (a === undefined) return missingLayer("provide", self)
    if (b === undefined) return missingLayer("provide", that)
    return Effect.sync(() => pushLayer(Layer.provide(a, b)))
  },
  // `Layer.provideMerge` — `Layer.ts:2436`, impl `:2797-2805`: the same
  // `provideWith` with `(self, that) => Context.merge(that, self)`, so the
  // dependency's services *do* reach the caller.
  provideMerge: (self, that) => {
    const a = layerAt(self)
    const b = layerAt(that)
    if (a === undefined) return missingLayer("provideMerge", self)
    if (b === undefined) return missingLayer("provideMerge", that)
    return Effect.sync(() => pushLayer(Layer.provideMerge(a, b)))
  },
  // `Layer.merge` — `Layer.ts:1705`, impl `:1902`: `mergeAll` of the two.
  merge: (self, that) => {
    const a = layerAt(self)
    const b = layerAt(that)
    if (a === undefined) return missingLayer("merge", self)
    if (b === undefined) return missingLayer("merge", that)
    return Effect.sync(() => pushLayer(Layer.merge(a, b)))
  },
  // `Layer.mergeAll` — `Layer.ts:1652-1658` over `mergeAllEffect`
  // (`:1587-1602`): one `"parallel"` scope forked from the caller scope, one
  // `"sequential"` child of it per layer, all built at
  // `concurrency: layers.length` over one shared memo map, and the resulting
  // contexts merged.
  mergeAll: (self, that) => {
    const a = layerAt(self)
    const b = layerAt(that)
    if (a === undefined) return missingLayer("mergeAll", self)
    if (b === undefined) return missingLayer("mergeAll", that)
    return Effect.sync(() => pushLayer(Layer.mergeAll(a, b)))
  },
  // `Layer.fresh` — `Layer.ts:3850-3851`: calls the layer's build *directly*
  // with a brand new memo map, so it rebuilds even where the ambient memo map
  // holds it, and it is installed with `fromBuildUnsafe`, so the wrapper gets
  // no `fromBuild` child scope of its own. Both halves are in that one line.
  fresh: (layer) => {
    const a = layerAt(layer)
    return a === undefined ? missingLayer("fresh", layer) : Effect.sync(() => pushLayer(Layer.fresh(a)))
  },
  // REFUSAL — rc.112 exports **no `Layer.memoize`** at this pin, and the
  // builder a memoized layer wraps is not reachable publicly either.
  //
  // Memoization is `Layer.fromBuildMemo` (`Layer.ts:380-388`), which ties the
  // layer to itself through `memoMap.getOrElseMemoize(self, scope, build)`;
  // `Layer.effect` and `Layer.effectContext` are the ordinary route to it
  // (`:1439`, `:1481`). `fromBuildMemo` takes a raw build function, and the
  // raw builder of an existing layer is its `build` member (`Layer.ts:56`),
  // which carries the doc tag `@internal` and is **stripped from the shipped
  // declarations** (`dist/Layer.d.ts:44-48` has no `build`) — so `fresh`'s own
  // spelling at `:3851` cannot be written by a consumer.
  //
  // The public builder is `buildWithMemoMap` (`:645`, impl `:756-765`), which
  // is `self.build(memoMap, scope)` plus two things: the memo map is installed
  // as the `CurrentMemoMap` service for the build and added to the produced
  // context. The layer below is therefore memoized exactly as rc.112 memoizes
  // one, and carries that one extra service; the Lean row must record the
  // difference rather than claim `fromBuildMemo ∘ build`.
  memoize: (layer) => {
    const a = layerAt(layer)
    if (a === undefined) return missingLayer("memoize", layer)
    return Effect.sync(() =>
      pushLayer(
        Layer.fromBuildMemo((map, scope) => Layer.buildWithMemoMap(a, map, scope)) as unknown as
          Layer.Layer<never, never, never>
      )
    )
  },
  // `Layer.orDie` — `Layer.ts:3327-3328`: `fromBuildUnsafe` over
  // `Effect.orDie` of the layer's build, so a typed build failure becomes a
  // defect and the wrapper gets no child scope of its own.
  orDie: (layer) => {
    const a = layerAt(layer)
    return a === undefined ? missingLayer("orDie", layer) : Effect.sync(() => pushLayer(Layer.orDie(a)))
  },
  // `Layer.unwrap` — `Layer.ts:1580-1585`: the effect's layer is put in a
  // private one-service context and flat-mapped out, so the effect runs once
  // per build of the unwrapped layer.
  unwrap: (layer) => {
    const a = layerAt(layer)
    if (a === undefined) return missingLayer("unwrap", layer)
    return Effect.sync(() =>
      pushLayer(Layer.unwrap(Effect.succeed(a)) as unknown as Layer.Layer<never, never, never>)
    )
  },
  // `Layer.makeMemoMapUnsafe` — `Layer.ts:492`: `new MemoMapImpl()`, a memo
  // map with no parent.
  makeMemoMap: Effect.sync(() => {
    memoTable.push(Layer.makeMemoMapUnsafe())
    return memoTable.length - 1
  }),
  // `Layer.forkMemoMapUnsafe` — `Layer.ts:511`: `new MemoMapImpl(parent)`. A
  // forked map answers from its own entries first and otherwise delegates to
  // the parent (`MemoMapImpl.get`, `:434-443`), so it sees layers the parent
  // already built and never writes to it.
  forkMemoMap: (memo) => {
    const parent = memoTable[memo]
    if (parent === undefined) {
      return Effect.die(new Error(`forkMemoMap: the request names no memo map ${memo}`))
    }
    return Effect.sync(() => {
      memoTable.push(Layer.forkMemoMapUnsafe(parent))
      return memoTable.length - 1
    })
  },
  // `Layer.buildWithMemoMap` — `Layer.ts:645`, impl `:756-765`: runs the
  // layer's build with the memo map installed as the `CurrentMemoMap` service
  // *and* added to the produced context, so nested builds inherit it.
  buildWithMemoMap: (layer, memo) => {
    const a = layerAt(layer)
    const map = memoTable[memo]
    if (a === undefined) return missingLayer("buildWithMemoMap", layer)
    if (map === undefined) {
      return Effect.die(new Error(`buildWithMemoMap: the request names no memo map ${memo}`))
    }
    return Effect.map(Layer.buildWithMemoMap(a, map, root), basesOf)
  },
  // `Layer.buildWithScope` — `Layer.ts:863`, impl `:970-980`: replaces only
  // the scope; the memo map is still `CurrentMemoMap.forkOrCreate(fiber.context)`
  // (`:585-588`), so an explicit scope does not imply an explicit memo map.
  buildWithScope: (layer) => {
    const a = layerAt(layer)
    return a === undefined
      ? missingLayer("buildWithScope", layer)
      : Effect.map(Layer.buildWithScope(a, root), basesOf)
  },
  // `Layer.launch` — `Layer.ts:3897-3898`:
  // `scoped(andThen(build(self), never))`, and `never` is
  // `callback(constVoid)` (`internal/effect.ts:1172`). The built layer stays
  // alive until the effect is interrupted, so this row never answers and the
  // run reaches its stall frontier. `Layer.build` reads the ambient `Scope`
  // through an unchecked lookup (`:800-809`), which `scoped` installs.
  launch: (layer) => {
    const a = layerAt(layer)
    return a === undefined ? missingLayer("launch", layer) : Effect.asVoid(Layer.launch(a))
  },
  provideCount: (base) => Effect.sync(() => counts.get(base) ?? 0)
}

const layerProgram = (body: (n: number) => Effect.Effect<unknown, never, Layers>) =>
  Effect.gen(function* () {
    const service = traceService(LayersRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(Layers, service))
  })

const fullProgram = (body: (n: number) => Effect.Effect<unknown, never, LayersFull>) =>
  Effect.gen(function* () {
    const service = traceService(LayersFullRows, fullLive, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(LayersFull, service))
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  buildOnce: layerProgram(layerBuildOnce),
  buildMemo: layerProgram(layerBuildMemo),
  releaseOrder: layerProgram(layerReleaseOrder),
  scopedRelease: layerProgram(layerScopedRelease),
  freshRebuild: layerProgram(layerFreshRebuild),
  freshRegion: layerProgram(layerFreshRegion),
  freshRelease: layerProgram(layerFreshRelease),
  rebuildAfterClose: layerProgram(layerRebuildAfterClose),
  provideDependencyFirst: fullProgram(layerProvideDependencyFirst),
  mergeParallelScopes: fullProgram(layerMergeParallelScopes),
  memoParentLookup: fullProgram(layerMemoParentLookup),
  freshDropsMemoization: fullProgram(layerFreshDropsMemoization),
  declareIdentity: fullProgram(layerDeclareIdentity),
  orDieUnwrap: fullProgram(layerOrDieUnwrap),
  launchHoldsScope: fullProgram(layerLaunchHoldsScope)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

/** `Layer.launch` runs `never` after the build, so the run parks and the op
 * budget can never fire; the stall deadline turns it into the frontier the
 * golden records (`RunOptions.stallMs` in `tracer.ts`). */
const stalls = name === "launchHoldsScope"

const report = await runTraced(
  program,
  sink,
  stalls ? { budget, maxOpsBeforeYield, stallMs } : { budget, maxOpsBeforeYield }
)
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
