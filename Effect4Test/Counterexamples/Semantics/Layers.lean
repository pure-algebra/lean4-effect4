/-
Counterexamples for the `Layers` family (`test/counterexamples/REGISTER.md`,
`E4-SEM-CE-016` through `E4-SEM-CE-019`; `test/counterexamples/semantics/ATTACKS.md`).

Each attack names a reading of rc.112's layer machinery that this family must
refuse, and the witness is a `#guard` over the same handler
`harness/trace/Generate.lean` renders `generated/traces/layer/` from. The last
two rows are refusals rather than repairs: they name host facts this face
cannot express, and are registered so nothing later claims them.
-/

import Effect4.Layer.LayerFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Counterexamples.Semantics.Layers

open Effect4.LayerFamily

/-! ## E4-SEM-CE-016: a memoized rebuild is a second construction

Attack: read `build` as "run the layer", so a second build constructs again,
answers a new handle and raises the count. Repair: rc.112's memo entry replays
the built context (`layer.memo-build-once`, `layer.memo-get-or-else`), so the
handler answers the memo table whenever the layer is memoized and the scope is
open, and only a construction raises `provideCount` or takes a handle. -/

-- A memo hit changes nothing at all: same handle, same store.
#guard decide (((layersLive Layers.Name.build 0
    { memo := [(0, 7)], counts := [(0, 1)], live := [7], next := 8 }).1
  : Effect4.Meta.Handle "Ref.Ref<number>") = ⟨7⟩)
#guard decide ((layersLive Layers.Name.build 0
    { memo := [(0, 7)], counts := [(0, 1)], live := [7], next := 8 }).2
  = { memo := [(0, 7)], counts := [(0, 1)], live := [7], next := 8 })

-- The contrast that makes the reading a real choice: layer 3 is
-- `Layer.fresh` of layer 1, a distinct layer identity that is never memoized
-- (`layer.fresh-drops-memoization`), so it constructs even where the memo
-- table already binds it, and counts against the layer it wraps.
#guard decide ((layersLive Layers.Name.build 3
    { memo := [(3, 7)], counts := [(1, 1)], live := [7], next := 8 }).2
  = { memo := [(3, 7)], counts := [(1, 2)], live := [7, 8], next := 9 })

-- On the wire: two builds of an ordinary layer, one handle; two builds of the
-- fresh wrapper, two handles and two constructions.
#guard ((layerPrograms.find? (·.name == "buildMemo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0", "answer\tbuild\t0"
  , "op\tbuild\t0", "answer\tbuild\t0"
  , "op\tprovideCount\t0", "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]
#guard ((layerPrograms.find? (·.name == "freshRebuild")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t3", "answer\tbuild\t0"
  , "op\tbuild\t3", "answer\tbuild\t1"
  , "op\tprovideCount\t1", "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

/-! ## E4-SEM-CE-017: layers are released in construction order

Attack: release the constructed layers in the order they were built, or leave
the order unstated because "a scope closes what it owns". Repair: `memoMapBuild`
registers the memo entry's finalizer on the caller scope *before* running the
construction, and a scope runs its finalizers in reverse registration order, so
`close` answers `live.reverse`. -/

#guard decide ((layersLive Layers.Name.close () { live := [0, 1, 2], next := 3 }).1
  = [(⟨2⟩ : Effect4.Meta.Handle "Ref.Ref<number>"), ⟨1⟩, ⟨0⟩])

-- Release order is not construction order: on three live layers the two lists
-- differ, so the attack is refuted and not merely unstated.
#guard decide (([0, 1, 2] : List Nat).reverse ≠ [0, 1, 2])

-- On the wire, for an ordinary layer beside a fresh one.
#guard ((layerPrograms.find? (·.name == "releaseOrder")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0", "answer\tbuild\t0"
  , "op\tbuild\t1", "answer\tbuild\t1"
  , "op\tclose\t[]", "answer\tclose\t[1, [0, []]]"
  , "done\t{\"success\":[1, [0, []]]}" ]
#guard ((layerPrograms.find? (·.name == "freshRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t1", "answer\tbuild\t0"
  , "op\tbuild\t3", "answer\tbuild\t1"
  , "op\tclose\t[]", "answer\tclose\t[1, [0, []]]"
  , "done\t{\"success\":[1, [0, []]]}" ]

/-! ## E4-SEM-CE-018: `close` only drops the memo table

Attack: treat `close` as a memo reset, so a later build is an ordinary first
build — constructed, memoized, live until the next close. Repair: `close` is
terminal. A closed scope forks closed (`internal/effect.ts`,
`scopeForkUnsafe`), so the construction lands in an already-closed layer scope:
it is released inside its own build, never memoized, and never live. The
second close therefore answers the empty order. -/

#guard decide ((layersLive Layers.Name.build 0
    { counts := [(0, 1)], next := 1, closed := true }).2
  = { counts := [(0, 2)], scopes := [], live := [], next := 2, closed := true })

#guard ((layerPrograms.find? (·.name == "rebuildAfterClose")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\tbuild\t0", "answer\tbuild\t0"
  , "op\tclose\t[]", "answer\tclose\t[0, []]"
  , "op\tbuild\t0", "answer\tbuild\t1"
  , "op\tclose\t[]", "answer\tclose\t[]"
  , "op\tprovideCount\t0", "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

/-! ## E4-SEM-CE-019: observer counting and concurrent memo identity

Refusals, not repairs.

**Observer counting.** A memoized rebuild registers the memo entry's finalizer
a second time (`layer.memo-reuse-observer-count`); at close that finalizer
decrements the observer count and releases nothing
(`layer.memo-finalizer-last-observer`). One release per *construction* reaches
the wire, never one per build, so nothing at this alphabet can see the
decrementing finalizer. The handler keeps one live entry per construction, and
the receipt below is the whole of what is claimed.

**Concurrent memo identity.** `memoMapBuild` installs the entry and a
`Deferred` before the construction runs, so a second fiber awaits the first
fiber's result instead of constructing. This handler is a single-fiber state
machine and the corpus is single-fiber; no event of this alphabet separates
"awaited another fiber's build" from "answered the memo table". No golden of
`generated/traces/layer/` is evidence about concurrent builds.

**Layer composition.** `Layer.provide`, `Layer.merge` and the parent-chain
lookup of a forked memo map are refused at this alphabet for a third reason:
they need a layer *value* on the wire, and a layer is a build function, not a
handle. -/

-- Two builds, one live entry, therefore one release: the second observer is
-- invisible.
#guard decide ((layersLive Layers.Name.build 0
    (layersLive Layers.Name.build 0 {}).2).2.live = [0])
#guard decide ((layersLive Layers.Name.close ()
    (layersLive Layers.Name.build 0 (layersLive Layers.Name.build 0 {}).2).2).1
  = [(⟨0⟩ : Effect4.Meta.Handle "Ref.Ref<number>")])

-- The family has exactly four operations; composition is not among them.
#guard Layers.rows.ops.map (·.name) == ["build", "provideCount", "scopeOf", "close"]

end Effect4Test.Counterexamples.Semantics.Layers
