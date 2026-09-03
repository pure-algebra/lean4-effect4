/-
Contract packet: M4 (`docs/research/2026-09-03-reification-plan.md`). Kernel
receipts for the `Layers` family's Lean face: the exact rows of each of the
eight goldens under `generated/traces/layer/`, and the memo-table clauses they
rest on.

These are `#guard`s, evaluated by the kernel, not proofs. Nothing here is a
statement about the host: the same rows are compared with rc.112 by
`scripts/check-trace-host.sh`'s `layer` section through
`harness/trace/layer-tail.ts`, and that comparison is evidence, never a
theorem. Doc comments cannot precede `#guard`, so the receipts carry line
comments.
-/

import Effect4.Layer.LayerFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.LayersContract

open Effect4.LayerFamily

#check @Effect4.LayerFamily.Layers
#check (@Effect4.LayerFamily.Layers.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.LayerFamily.layersLive
#check @Effect4.LayerFamily.layerGoldenLog
#check @Effect4.LayerFamily.freshOf

/-! ## The corpus -/

#guard layerPrograms.length == 8

#guard layerPrograms.map (·.name) ==
  [ "buildOnce", "buildMemo", "releaseOrder", "scopedRelease"
  , "freshRebuild", "freshRegion", "freshRelease", "rebuildAfterClose" ]

-- Four declared layers: 0, 1 and 2 ordinary, 3 the `Layer.fresh` wrapper of 1.
#guard [0, 1, 2, 3].map freshOf == [none, none, none, some 1]
#guard [0, 1, 2, 3].map layerBase == [0, 1, 2, 1]

/-! ## The rows of each golden

The wire rows of a program's Lean log are computed inline in each receipt: a
`def` rendering rows would reach `Classical.choice` through the renderer and the
axiom gate scans test declarations too, while a `#guard` is a command, not a
declaration. An unknown name answers a row that no golden can match. -/

-- buildOnce: one build, one construction. The handle `0` is the first object
-- the wire has seen.
#guard ((layerPrograms.find? (·.name == "buildOnce")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0"
  , "answer\tbuild\t0"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

-- buildMemo: the second build answers the *same* handle and constructs
-- nothing, which is what a memo hit looks like from a program.
#guard ((layerPrograms.find? (·.name == "buildMemo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0"
  , "answer\tbuild\t0"
  , "op\tbuild\t0"
  , "answer\tbuild\t0"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]

-- releaseOrder: two layers, then close. The answer is the release order, and
-- it is the reverse of the construction order.
#guard ((layerPrograms.find? (·.name == "releaseOrder")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0"
  , "answer\tbuild\t0"
  , "op\tbuild\t1"
  , "answer\tbuild\t1"
  , "op\tclose\t[]"
  , "answer\tclose\t[1, [0, []]]"
  , "done\t{\"success\":[1, [0, []]]}" ]

-- scopedRelease: the construction owns a layer scope of its own — handle `1`,
-- the second object the wire has seen — and close releases the service in it.
#guard ((layerPrograms.find? (·.name == "scopedRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t2"
  , "answer\tbuild\t0"
  , "op\tscopeOf\t0"
  , "answer\tscopeOf\t1"
  , "op\tclose\t[]"
  , "answer\tclose\t[0, []]"
  , "done\t{\"success\":1}" ]

-- freshRebuild: `Layer.fresh` is never memoized, so two builds of layer 3
-- answer two handles and count twice against layer 1.
#guard ((layerPrograms.find? (·.name == "freshRebuild")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t3"
  , "answer\tbuild\t0"
  , "op\tbuild\t3"
  , "answer\tbuild\t1"
  , "op\tprovideCount\t1"
  , "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

-- freshRegion: the memoized layer and its fresh wrapper are different
-- identities, so the fresh construction has a layer scope of its own.
#guard ((layerPrograms.find? (·.name == "freshRegion")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t1"
  , "answer\tbuild\t0"
  , "op\tbuild\t3"
  , "answer\tbuild\t1"
  , "op\tscopeOf\t1"
  , "answer\tscopeOf\t2"
  , "done\t{\"success\":2}" ]

-- freshRelease: a fresh construction is released on the same rule as any
-- other, last constructed first.
#guard ((layerPrograms.find? (·.name == "freshRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t1"
  , "answer\tbuild\t0"
  , "op\tbuild\t3"
  , "answer\tbuild\t1"
  , "op\tclose\t[]"
  , "answer\tclose\t[1, [0, []]]"
  , "done\t{\"success\":[1, [0, []]]}" ]

-- rebuildAfterClose: close is terminal. The rebuild is a new construction (a
-- new handle, and the count rises to 2), it is released inside its own build
-- because a closed scope forks closed, and the second close therefore answers
-- the empty order.
#guard ((layerPrograms.find? (·.name == "rebuildAfterClose")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0"
  , "answer\tbuild\t0"
  , "op\tclose\t[]"
  , "answer\tclose\t[0, []]"
  , "op\tbuild\t0"
  , "answer\tbuild\t1"
  , "op\tclose\t[]"
  , "answer\tclose\t[]"
  , "op\tprovideCount\t0"
  , "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

/-! ## The clauses of the memo table

The five theorems of `Effect4/Layer/LayerFamily.lean`, checked here as the
shapes the goldens above rest on, and again as receipts in
`Effect4Test/Flow/LayersAxiomReport.lean`. -/

#check @Effect4.LayerFamily.build_constructs
#check @Effect4.LayerFamily.build_memoizes
#check @Effect4.LayerFamily.build_memo_hit
#check @Effect4.LayerFamily.build_fresh_ignores_memo
#check @Effect4.LayerFamily.build_after_close_is_not_live
#check @Effect4.LayerFamily.build_after_close_is_not_memoized
#check @Effect4.LayerFamily.close_releases_in_reverse
#check @Effect4.LayerFamily.close_is_terminal

-- A build into an open, empty store takes handle 0, memoizes it, counts it and
-- makes it live.
#guard decide ((layersLive Effect4.LayerFamily.Layers.Name.build 0 {}).2 =
  { memo := [(0, 0)], counts := [(0, 1)], scopes := [], live := [0], next := 1, closed := false })

-- `scopeOf` allocates the layer scope's handle on demand, from the same
-- counter the services come from, which is what `handleIndex` does on the host.
#guard decide ((layersLive Effect4.LayerFamily.Layers.Name.scopeOf ⟨0⟩
    { memo := [(0, 0)], counts := [(0, 1)], scopes := [], live := [0], next := 1 }).2.scopes
  = [(0, 1)])

-- Asking twice answers the same handle and allocates nothing.
#guard (layersLive Effect4.LayerFamily.Layers.Name.scopeOf ⟨0⟩
    { scopes := [(0, 1)], next := 2 }).2.next == 2

-- `close` empties the memo table, so the next build cannot hit it.
#guard decide ((layersLive Effect4.LayerFamily.Layers.Name.close ()
    { memo := [(0, 0), (1, 1)], live := [0, 1], next := 2 }).2
  = { memo := [], counts := [], scopes := [], live := [], next := 2, closed := true })

end Effect4Test.Flow.LayersContract
