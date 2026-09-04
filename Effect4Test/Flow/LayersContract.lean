/-
Contract packet: the `Layers` family (`docs/TRACE-DAG.md`, the `layer` edge),
lowering lane L3.

Kernel receipts for the Lean face: the twenty-two rows of rc.112's `Layer`
surface, the exact rows of each of the thirteen programs the corpus carries,
and the memo-map clauses the handler is a projection of.

These are `#guard`s, evaluated by the kernel, not proofs. Nothing here is a
statement about the host: the same rows are compared with rc.112 by
`scripts/check-trace-host.sh`'s `layer` section through
`harness/trace/layer-tail.ts`, and that comparison is evidence, never a
theorem. Doc comments cannot precede `#guard`, so the receipts carry line
comments.

**The eight goldens under `generated/traces/layer/` are owed a regeneration.**
Before lane L3 a layer was a `Nat` and the family had four operations; a layer
is a `Handle "Layer.Layer<number>"` now, answered by the constructor that made
it, so every program declares its layers on the wire and every handle index
moved. The corpus is thirteen programs rather than eight, and `freshRegion` is
gone: with a real memo map the fresh wrapper's separate identity is what
`freshRebuild` and `memoMapParentLookup` show. The rows below are what the
regenerated goldens must carry; running the generator belongs to the harness
lane and nothing in this battery runs it.

The corpus is imported rather than restated, so a second copy of the handler
cannot drift from the one the goldens are generated from.
-/

import Effect4.Layer.LayerFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.LayersContract

open Effect4.LayerFamily

#check @Effect4.LayerFamily.Layers
#check (@Effect4.LayerFamily.Layers.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.LayerFamily.layersLive
#check @Effect4.LayerFamily.buildMany
#check @Effect4.LayerFamily.layerGoldenLog

/-! ## The rows, one per rc.112 entry point

Eleven constructors, two memo-map operations, three builds, `launch`, and the
five probes the corpus reads the store through. Every constructor answers a
`Handle "Layer.Layer<number>"` and every consumer takes one: that is what
lifted `E4-SEM-CE-019`'s composition clause. -/

#guard Layers.rows.name = "Layers"

#guard Layers.rows.ops.map (·.name) =
  [ "succeed", "effect", "scoped", "provide", "provideMerge", "merge", "mergeAll", "fresh"
  , "memoize", "orDie", "unwrap", "makeMemoMap", "forkMemoMap", "build", "buildWithScope"
  , "buildWithMemoMap", "launch", "servicesOf", "scopeOf", "provideCount", "observers", "close" ]

#guard Layers.rows.ops.map (·.params.length) =
  [1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 2, 3, 1, 1, 1, 1, 1, 0]

#guard Layers.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("succeed", "Layer.Layer<number>"), ("effect", "Layer.Layer<number>")
  , ("scoped", "Layer.Layer<number>"), ("provide", "Layer.Layer<number>")
  , ("provideMerge", "Layer.Layer<number>"), ("merge", "Layer.Layer<number>")
  , ("mergeAll", "Layer.Layer<number>"), ("fresh", "Layer.Layer<number>")
  , ("memoize", "Layer.Layer<number>"), ("orDie", "Layer.Layer<number>")
  , ("unwrap", "Layer.Layer<number>"), ("makeMemoMap", "Layer.MemoMap")
  , ("forkMemoMap", "Layer.MemoMap"), ("build", "Context.Context<never>")
  , ("buildWithScope", "Context.Context<never>")
  , ("buildWithMemoMap", "Context.Context<never>"), ("launch", "void")
  , ("servicesOf", "ReadonlyArray<Ref.Ref<number>>"), ("scopeOf", "Scope.Closeable")
  , ("provideCount", "number"), ("observers", "number")
  , ("close", "ReadonlyArray<Ref.Ref<number>>") ]

#guard Layers.rows.ops.map (fun row => (row.name, row.tsParams.map Prod.snd)) =
  [ ("succeed", ["number"]), ("effect", ["number"]), ("scoped", ["number"])
  , ("provide", ["Layer.Layer<number>", "Layer.Layer<number>"])
  , ("provideMerge", ["Layer.Layer<number>", "Layer.Layer<number>"])
  , ("merge", ["Layer.Layer<number>", "Layer.Layer<number>"])
  , ("mergeAll", ["ReadonlyArray<Layer.Layer<number>>"])
  , ("fresh", ["Layer.Layer<number>"]), ("memoize", ["Layer.Layer<number>"])
  , ("orDie", ["Layer.Layer<number>"]), ("unwrap", ["Layer.Layer<number>"])
  , ("makeMemoMap", []), ("forkMemoMap", ["Layer.MemoMap"])
  , ("build", ["Layer.Layer<number>"])
  , ("buildWithScope", ["Layer.Layer<number>", "Scope.Closeable"])
  , ("buildWithMemoMap", ["Layer.Layer<number>", "Layer.MemoMap", "Scope.Closeable"])
  , ("launch", ["Layer.Layer<number>"]), ("servicesOf", ["Context.Context<never>"])
  , ("scopeOf", ["Ref.Ref<number>"]), ("provideCount", ["Layer.Layer<number>"])
  , ("observers", ["Layer.Layer<number>"]), ("close", []) ]

-- No operation declares an error channel: every refusal in this lane is a
-- frontier of the model, never a typed failure.
#guard Layers.rows.ops.all (fun row => row.error.isNone)

-- The three build rows answer a context, and only `servicesOf` reads it back
-- into service handles. A context never crosses as a list of numbers.
#guard (Layers.rows.ops.filter (fun row => row.tsAnswer == "Context.Context<never>")).map (·.name) =
  ["build", "buildWithScope", "buildWithMemoMap"]

/-! ## The handler is a projection of the memo-map store

The clauses of `Effect4/Layer/LayerFamily.lean`, cited here as the shapes the
rows below rest on; their axiom receipts are in
`Effect4Test/Flow/LayersAxiomReport.lean`. -/

#check @Effect4.LayerFamily.declare_takes_the_next_handle
#check @Effect4.LayerFamily.memoChain_starts_at_the_map
#check @Effect4.LayerFamily.buildBase_memo_hit
#check @Effect4.LayerFamily.buildBase_miss_constructs
#check @Effect4.LayerFamily.buildBase_after_close_is_not_live
#check @Effect4.LayerFamily.close_releases_in_reverse
#check @Effect4.LayerFamily.close_is_terminal
#check @Effect4.LayerFamily.close_empties_every_memo_map

/-- The store after declaring one `Layer.effect` layer. -/
def declared : LayerStore := (layersLive Layers.Name.effect 0 {}).2

/-- The same store after one `build`: the ambient memo map is created on first
use (`CurrentMemoMap.forkOrCreate`, `Layer.ts:585-588`), so the map takes the
handle after the layer, the service the one after that, its layer scope the
next, and the context the last. -/
def builtOnce : LayerStore := (layersLive Layers.Name.build ⟨0⟩ declared).2

/-- And after a second build of the same layer: a memo hit. -/
def builtTwice : LayerStore := (layersLive Layers.Name.build ⟨0⟩ builtOnce).2

-- A declared layer takes the next handle and binds its description; nothing
-- else moves.
#guard decide (declared.layers = [(0, LayerDesc.effect 0)])
#guard declared.next == 1
#guard decide (declared.counts = [] ∧ declared.live = [] ∧ declared.maps = [])

-- The first build: one construction, counted once, live, with a layer scope of
-- its own, and a context holding it.
#guard decide (builtOnce.counts = [(0, 1)])
#guard decide (builtOnce.live = [2])
#guard decide (builtOnce.scopes = [(2, 3)])
#guard decide (builtOnce.contexts = [(4, [2])])
#guard builtOnce.next == 5

-- The second build constructs nothing: the count and the live set do not move,
-- the context is a *new* handle over the *same* service, and the observer
-- count rises. That last is the model fact the host cannot report.
#guard decide (builtTwice.counts = [(0, 1)])
#guard decide (builtTwice.live = [2])
#guard decide (builtTwice.contexts = [(4, [2]), (5, [2])])
#guard builtTwice.observersOf 0 == 2
#guard builtOnce.observersOf 0 == 1

-- `close` answers the live services in reverse construction order, empties
-- every memo map, and is terminal.
#guard decide ((layersLive Layers.Name.close () builtTwice).1
  = [(⟨2⟩ : Effect4.Meta.Handle "Ref.Ref<number>")])
#guard (layersLive Layers.Name.close () builtTwice).2.closed
#guard decide ((layersLive Layers.Name.close () builtTwice).2.live = [])
#guard (layersLive Layers.Name.close () builtTwice).2.maps.all
  (fun entry => entry.2.entries.isEmpty)

-- A forked memo map's chain is the child then the parent, and a lookup that
-- misses in the child finds the parent's entry (`Layer.ts:434-443`).
#guard decide (
  ((({ maps := [(0, {}), (1, { parent := Option.some 0, entries := [] })] } : LayerStore)).memoChain 1)
    = [1, 0])
#guard decide (
  (({ maps :=
        [ (0, { parent := Option.none,
                entries := [{ layer := 7, service := 5, scope := 6, observers := 1 }] })
        , (1, { parent := Option.some 0, entries := [] }) ] } : LayerStore).lookupMemo 1 7).map
    Prod.fst = Option.some 0)

/-! ## The rows of each program

The wire rows of a program's Lean log are computed inline in each receipt: a
`def` rendering rows would reach `Classical.choice` through the renderer and the
axiom gate scans test declarations too, while a `#guard` is a command, not a
declaration. An unknown name answers a row that no golden can match. -/

#guard layerPrograms.length == 13

#guard layerPrograms.map (·.name) ==
  [ "buildOnce", "buildMemo", "observerCount", "releaseOrder", "scopedRelease"
  , "freshRebuild", "freshRelease", "rebuildAfterClose", "provideDependencyFirst"
  , "provideMergeKeepsDependency", "mergeAllSharesMemo", "memoMapParentLookup"
  , "launchBuilds" ]

-- buildOnce: the layer is declared on the wire, then built once. The context
-- is handle 4 because the ambient memo map (1), the service (2) and its layer
-- scope (3) were minted first, from the one counter `handleIndex` is on the
-- host.
#guard ((layerPrograms.find? (·.name == "buildOnce")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

-- buildMemo: two builds, two contexts, one construction. A memo hit answers a
-- fresh context over the same service, which is what replaying the built
-- context looks like from a program.
#guard ((layerPrograms.find? (·.name == "buildMemo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tbuild\t0"
  , "answer\tbuild\t5"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

-- observerCount: one construction, two builds, two observers
-- (`memoMapReuse`'s `entry.observers++`, `Layer.ts:245`). The count is exact in
-- the store; a host trace forgets it unless `layer-tail.ts` instruments the
-- memo map. That is the forgetful direction of the join, not a refusal.
#guard ((layerPrograms.find? (·.name == "observerCount")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tbuild\t0"
  , "answer\tbuild\t5"
  , "op\tobservers\t0"
  , "answer\tobservers\t2"
  , "done\t{\"success\":2}" ]

-- releaseOrder: two layers, then close. The answer is the release order, and
-- it is the reverse of the construction order.
#guard ((layerPrograms.find? (·.name == "releaseOrder")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\teffect\t1"
  , "answer\teffect\t1"
  , "op\tbuild\t0"
  , "answer\tbuild\t5"
  , "op\tbuild\t1"
  , "answer\tbuild\t8"
  , "op\tclose\t[]"
  , "answer\tclose\t[6, [3, []]]"
  , "done\t{\"success\":[6, [3, []]]}" ]

-- scopedRelease: a `Layer.effect` of a construction that acquires in its layer
-- scope. `servicesOf` reads the context back and `scopeOf` names the scope the
-- construction owns.
#guard ((layerPrograms.find? (·.name == "scopedRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tscoped\t2"
  , "answer\tscoped\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tservicesOf\t4"
  , "answer\tservicesOf\t[2, []]"
  , "op\tscopeOf\t2"
  , "answer\tscopeOf\t3"
  , "op\tclose\t[]"
  , "answer\tclose\t[2, []]"
  , "done\t{\"success\":3}" ]

-- freshRebuild: `Layer.fresh` builds through a private memo map
-- (`Layer.ts:3851`), so two builds construct twice and both count against the
-- layer it wraps.
#guard ((layerPrograms.find? (·.name == "freshRebuild")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t1"
  , "answer\teffect\t0"
  , "op\tfresh\t0"
  , "answer\tfresh\t1"
  , "op\tbuild\t1"
  , "answer\tbuild\t6"
  , "op\tbuild\t1"
  , "answer\tbuild\t10"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

-- freshRelease: a fresh construction is released on the same rule as any
-- other, last constructed first.
#guard ((layerPrograms.find? (·.name == "freshRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t1"
  , "answer\teffect\t0"
  , "op\tfresh\t0"
  , "answer\tfresh\t1"
  , "op\tbuild\t0"
  , "answer\tbuild\t5"
  , "op\tbuild\t1"
  , "answer\tbuild\t9"
  , "op\tclose\t[]"
  , "answer\tclose\t[7, [3, []]]"
  , "done\t{\"success\":[7, [3, []]]}" ]

-- rebuildAfterClose: close is terminal. The rebuild is a new construction (a
-- new service, and the count rises to 2), it is released inside its own build
-- because a closed scope forks closed, and the second close answers the empty
-- order.
#guard ((layerPrograms.find? (·.name == "rebuildAfterClose")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tclose\t[]"
  , "answer\tclose\t[2, []]"
  , "op\tbuild\t0"
  , "answer\tbuild\t7"
  , "op\tclose\t[]"
  , "answer\tclose\t[]"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

-- provideDependencyFirst: `provideWith(self, that, identity)`
-- (`Layer.ts:1907-1926`, `:2345-2348`) builds the dependency first and keeps it
-- out of the result, so the built context holds one service.
#guard ((layerPrograms.find? (·.name == "provideDependencyFirst")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\teffect\t1"
  , "answer\teffect\t1"
  , "op\tprovide\t[1, 0]"
  , "answer\tprovide\t2"
  , "op\tbuild\t2"
  , "answer\tbuild\t8"
  , "op\tservicesOf\t8"
  , "answer\tservicesOf\t[6, []]"
  , "done\t{\"success\":[6, []]}" ]

-- provideMergeKeepsDependency: the same build with `Context.merge` as the
-- combiner (`Layer.ts:2797-2805`) keeps the dependency, and it comes first
-- because it was built first.
#guard ((layerPrograms.find? (·.name == "provideMergeKeepsDependency")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\teffect\t1"
  , "answer\teffect\t1"
  , "op\tprovideMerge\t[1, 0]"
  , "answer\tprovideMerge\t2"
  , "op\tbuild\t2"
  , "answer\tbuild\t8"
  , "op\tservicesOf\t8"
  , "answer\tservicesOf\t[4, [6, []]]"
  , "done\t{\"success\":[4, [6, []]]}" ]

-- mergeAllSharesMemo: `mergeAll` names one layer twice and builds it once,
-- because both arms go through the same memo map (`Layer.ts:1587-1602`).
#guard ((layerPrograms.find? (·.name == "mergeAllSharesMemo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tmergeAll\t[0, [0, []]]"
  , "answer\tmergeAll\t1"
  , "op\tbuild\t1"
  , "answer\tbuild\t5"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

-- memoMapParentLookup: a build into a *fresh* memo map is a miss even though
-- the ambient map already holds the layer (that is
-- `layer.build-with-scope-still-forks-memo` read from the memo-map side), and
-- the build into its child then hits the parent's entry. Two constructions,
-- three builds.
#guard ((layerPrograms.find? (·.name == "memoMapParentLookup")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t4"
  , "op\tservicesOf\t4"
  , "answer\tservicesOf\t[2, []]"
  , "op\tscopeOf\t2"
  , "answer\tscopeOf\t3"
  , "op\tmakeMemoMap\t[]"
  , "answer\tmakeMemoMap\t5"
  , "op\tforkMemoMap\t5"
  , "answer\tforkMemoMap\t6"
  , "op\tbuildWithMemoMap\t[0, [5, 3]]"
  , "answer\tbuildWithMemoMap\t9"
  , "op\tbuildWithMemoMap\t[0, [6, 3]]"
  , "answer\tbuildWithMemoMap\t10"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

-- launchBuilds: `launch` builds the layer and answers unit. rc.112 then parks
-- forever (`scoped(andThen(build(self), never))`, `Layer.ts:3898`), and that
-- park is the refusal this row records: the construction ledger moves and no
-- answer carries the `Effect<never>`.
#guard ((layerPrograms.find? (·.name == "launchBuilds")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0"
  , "answer\teffect\t0"
  , "op\tlaunch\t0"
  , "answer\tlaunch\t[]"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

/-! ## What the family fixes about a handle -/

-- A layer, a memo map, a context, a service and a layer scope all cross the
-- wire as a bare index and as nothing else.
#guard Layers.encodeAnswer .effect ⟨3⟩ = Effects.Trace.Val.nat 3
#guard Layers.encodeAnswer .makeMemoMap ⟨1⟩ = Effects.Trace.Val.nat 1
#guard Layers.encodeAnswer .build ⟨4⟩ = Effects.Trace.Val.nat 4
#guard Layers.encodeParam .buildWithMemoMap (⟨0⟩, ⟨5⟩, ⟨3⟩) =
  Effects.Trace.Val.pair (.nat 0) (.pair (.nat 5) (.nat 3))

-- Every program of the corpus ends in a success: no operation of this family
-- has an error channel, and no build of it is a frontier.
#guard layerPrograms.all (fun entry => entry.log.all (fun event =>
  match event with
  | .done (.success _) => true
  | .done _ => false
  | _ => true))

-- Every log agrees with itself under every registered mask; agreement is a
-- projection equality and never more.
#guard layerPrograms.all (fun entry =>
  Effect4.Trace.maskTable.all (fun mask => Effect4.Trace.agree mask.2 entry.log entry.log))

end Effect4Test.Flow.LayersContract
