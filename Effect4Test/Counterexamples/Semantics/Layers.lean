/-
Counterexamples for the `Layers` family (`test/counterexamples/REGISTER.md`,
`E4-SEM-CE-016` through `E4-SEM-CE-019`; `test/counterexamples/semantics/ATTACKS.md`).

Each attack names a reading of rc.112's layer machinery that this family must
refuse, and the witness is a `#guard` over the same handler
`harness/trace/Generate.lean` renders `generated/traces/layer/` from.

Re-pinned by lowering lane L3. A layer is a `Handle "Layer.Layer<number>"` now
and the store is a **memo map** (`MemoMapImpl`, `Layer.ts:421-458`) rather than
a table keyed by layer id, so every witness below is restated over that
carrier. The three repairs are unchanged facts; the third clause of
`E4-SEM-CE-019` — layer composition — is **lifted**, and what is left of that
row is the forgetful direction of the join.
-/

import Effect4.Layer.LayerFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Counterexamples.Semantics.Layers

open Effect4.LayerFamily

/-! ## The three stores every witness below is read off -/

/-- One `Layer.effect` declared, nothing built. -/
def declared : LayerStore := (layersLive Layers.Name.effect 0 {}).2

/-- The same layer built once: the ambient memo map is created on first use, so
it takes handle 1, the service 2, its layer scope 3, and the context 4. -/
def builtOnce : LayerStore := (layersLive Layers.Name.build ⟨0⟩ declared).2

/-- And built a second time. -/
def builtTwice : LayerStore := (layersLive Layers.Name.build ⟨0⟩ builtOnce).2

/-- The `Layer.fresh` wrapper of the same layer, built twice. -/
def freshBuiltTwice : LayerStore :=
  (layersLive Layers.Name.build ⟨1⟩
    (layersLive Layers.Name.build ⟨1⟩
      (layersLive Layers.Name.fresh ⟨0⟩ declared).2).2).2

/-! ## E4-SEM-CE-016: a memoized rebuild is a second construction

Attack: read `build` as "run the layer", so a second build constructs again,
takes new handles and raises the count. Repair: `getOrElseMemoize` consults the
memo map first (`Layer.ts:445-457`), so a hit replays the built context and
only a *miss* runs `memoMapBuild`. -/

-- A memo hit constructs nothing: the count, the live set and the layer scopes
-- are exactly where the first build left them.
#guard decide (builtTwice.counts = builtOnce.counts)
#guard decide (builtTwice.live = builtOnce.live)
#guard decide (builtTwice.scopes = builtOnce.scopes)

-- What a hit does move is the *context* handle and the observer count: the
-- second build answers a fresh context over the same service.
#guard decide (builtTwice.contexts = [(4, [2]), (5, [2])])
#guard builtOnce.observersOf 0 == 1
#guard builtTwice.observersOf 0 == 2

-- The contrast that makes the reading a real choice: `Layer.fresh` calls the
-- layer's own build with a brand new memo map (`Layer.ts:3851`), so it
-- constructs on every build, counts against the layer it wraps, and leaves the
-- caller's ambient memo map empty.
#guard decide (freshBuiltTwice.counts = [(0, 2)])
#guard decide (freshBuiltTwice.live = [4, 8])
#guard decide ((assocGet freshBuiltTwice.maps 2).map MemoMap.entries = Option.some [])

-- On the wire: two builds of an ordinary layer, one construction; two builds
-- of the fresh wrapper, two.
#guard ((layerPrograms.find? (·.name == "buildMemo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0", "answer\teffect\t0"
  , "op\tbuild\t0", "answer\tbuild\t4"
  , "op\tbuild\t0", "answer\tbuild\t5"
  , "op\tprovideCount\t0", "answer\tprovideCount\t1"
  , "done\t{\"success\":1}" ]
#guard ((layerPrograms.find? (·.name == "freshRebuild")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t1", "answer\teffect\t0"
  , "op\tfresh\t0", "answer\tfresh\t1"
  , "op\tbuild\t1", "answer\tbuild\t6"
  , "op\tbuild\t1", "answer\tbuild\t10"
  , "op\tprovideCount\t0", "answer\tprovideCount\t2"
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

-- On the wire, for two ordinary layers and for an ordinary layer beside a
-- fresh one.
#guard ((layerPrograms.find? (·.name == "releaseOrder")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0", "answer\teffect\t0"
  , "op\teffect\t1", "answer\teffect\t1"
  , "op\tbuild\t0", "answer\tbuild\t5"
  , "op\tbuild\t1", "answer\tbuild\t8"
  , "op\tclose\t[]", "answer\tclose\t[6, [3, []]]"
  , "done\t{\"success\":[6, [3, []]]}" ]
#guard ((layerPrograms.find? (·.name == "freshRelease")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t1", "answer\teffect\t0"
  , "op\tfresh\t0", "answer\tfresh\t1"
  , "op\tbuild\t0", "answer\tbuild\t5"
  , "op\tbuild\t1", "answer\tbuild\t9"
  , "op\tclose\t[]", "answer\tclose\t[7, [3, []]]"
  , "done\t{\"success\":[7, [3, []]]}" ]

/-! ## E4-SEM-CE-018: `close` only drops the memo table

Attack: treat `close` as a memo reset, so a later build is an ordinary first
build — constructed, memoized, live until the next close. Repair: `close` is
terminal. A closed scope forks closed (`internal/effect.ts`,
`scopeForkUnsafe`), so the construction lands in an already-closed layer scope:
it is released inside its own build, never memoized, and never live. The second
close therefore answers the empty order. -/

-- The close itself empties every memo map and the live set, and sets `closed`.
#guard (layersLive Layers.Name.close () builtOnce).2.maps.all
  (fun entry => entry.2.entries.isEmpty)
#guard decide ((layersLive Layers.Name.close () builtOnce).2.live = [])
#guard (layersLive Layers.Name.close () builtOnce).2.closed

-- The rebuild after it *does* construct — a second count, a new service and a
-- new layer scope — and joins neither the live set nor any memo map.
#guard decide ((layersLive Layers.Name.build ⟨0⟩
    (layersLive Layers.Name.close () builtOnce).2).2.counts = [(0, 2)])
#guard decide ((layersLive Layers.Name.build ⟨0⟩
    (layersLive Layers.Name.close () builtOnce).2).2.live = [])
#guard (layersLive Layers.Name.build ⟨0⟩
    (layersLive Layers.Name.close () builtOnce).2).2.maps.all
  (fun entry => entry.2.entries.isEmpty)

#guard ((layerPrograms.find? (·.name == "rebuildAfterClose")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0", "answer\teffect\t0"
  , "op\tbuild\t0", "answer\tbuild\t4"
  , "op\tclose\t[]", "answer\tclose\t[2, []]"
  , "op\tbuild\t0", "answer\tbuild\t7"
  , "op\tclose\t[]", "answer\tclose\t[]"
  , "op\tprovideCount\t0", "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

/-! ## E4-SEM-CE-019: what the join to a host trace forgets

Two clauses survive, and one is lifted.

**Observer counting is exact in the model and invisible to an uninstrumented
host.** The old reading of this row said observer counting is "invisible", on
the grounds that a memoized rebuild registers the memo entry's finalizer a
second time and at close that finalizer only decrements (`Layer.ts:401-410`),
so one release per *construction* reaches the wire and never one per build.
That is a fact about the wire, not about the store: `memoMapReuse`'s
`entry.observers++` (`Layer.ts:245`) is modelled exactly, and the `observers`
row reads it. The row is a **probe of the store**, not an rc.112 call, and
`harness/trace/layer-tail.ts` owes an observer counter of its own before any
golden compares it. That is the forgetful direction of the join.

**Concurrent memo identity is out of reach for the reason it always was.**
`memoMapBuild` installs the entry and a `Deferred` before the construction runs
(`Layer.ts:390-419`), so a second fiber awaits the first fiber's result instead
of constructing. This handler is a single-fiber state machine and the corpus is
single-fiber; no event of this alphabet separates "awaited another fiber's
build" from "answered the memo table". No golden of `generated/traces/layer/`
is evidence about concurrent builds.

**Layer composition is no longer refused.** The old third clause said
`Layer.provide`, `Layer.merge` and the parent-chain lookup "need a layer *value*
on the wire, and a layer is a build function, not a handle". A layer crosses as
a handle answered by the constructor that made it, exactly as a `Ref` does, so
the eleven constructors and the two memo-map operations are rows. What remains
of the refusal is `LAYER-FB-LAYER-IDENTITY`: rc.112 keys the memo `Map` on the
layer *object* (`Layer.ts:411`, `:438`) and an index is only a stand-in for that
identity, the same standing refusal `SCOPE-FB-KEY-IDENTITY` is for a scope key.
-/

-- The two builds above are one live entry, therefore one release: the second
-- observer never reaches the answer.
#guard decide ((layersLive Layers.Name.close () builtTwice).1
  = [(⟨2⟩ : Effect4.Meta.Handle "Ref.Ref<number>")])
#guard builtTwice.observersOf 0 == 2

-- Composition is on the wire now: eleven constructors, every one answering a
-- layer handle and every consumer taking one.
#guard Layers.rows.ops.map (·.name) ==
  [ "succeed", "effect", "scoped", "provide", "provideMerge", "merge", "mergeAll", "fresh"
  , "memoize", "orDie", "unwrap", "makeMemoMap", "forkMemoMap", "build", "buildWithScope"
  , "buildWithMemoMap", "launch", "servicesOf", "scopeOf", "provideCount", "observers", "close" ]

#guard (Layers.rows.ops.filter (fun row => row.tsAnswer == "Layer.Layer<number>")).map (·.name) ==
  [ "succeed", "effect", "scoped", "provide", "provideMerge", "merge", "mergeAll", "fresh"
  , "memoize", "orDie", "unwrap" ]

-- The parent-chain lookup is a row too: a build into a forked memo map finds
-- the parent's entry and constructs nothing.
#guard ((layerPrograms.find? (·.name == "memoMapParentLookup")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown layer program"] ==
  [ "op\teffect\t0", "answer\teffect\t0"
  , "op\tbuild\t0", "answer\tbuild\t4"
  , "op\tservicesOf\t4", "answer\tservicesOf\t[2, []]"
  , "op\tscopeOf\t2", "answer\tscopeOf\t3"
  , "op\tmakeMemoMap\t[]", "answer\tmakeMemoMap\t5"
  , "op\tforkMemoMap\t5", "answer\tforkMemoMap\t6"
  , "op\tbuildWithMemoMap\t[0, [5, 3]]", "answer\tbuildWithMemoMap\t9"
  , "op\tbuildWithMemoMap\t[0, [6, 3]]", "answer\tbuildWithMemoMap\t10"
  , "op\tprovideCount\t0", "answer\tprovideCount\t2"
  , "done\t{\"success\":2}" ]

-- What the model cannot separate: two builds of one layer against one memo map
-- answer the same service whether the second one hit the table or awaited
-- another fiber's construction. There is no second fiber in this alphabet, so
-- the two readings are the same store.
#guard decide (
  ((assocGet builtTwice.maps 1).map MemoMap.entries)
    = Option.some [{ layer := 0, service := 2, scope := 3, observers := 2 }])

end Effect4Test.Counterexamples.Semantics.Layers
