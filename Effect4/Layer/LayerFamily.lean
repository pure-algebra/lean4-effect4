import Effect4.Meta.Derive

/-!
# Layer.LayerFamily

`Layers`: a traced family over rc.112's layer machinery — `Layer.effect`,
`Layer.buildWithMemoMap`, `Layer.fresh` and the memo map of `Layer.ts` — with
the Lean handler that is a **memo table**: the model of what a *program* can
observe of a build, and nothing more.

The census rows this family is built against are `layer.memo-build-once`,
`layer.memo-finalizer-last-observer`, `layer.memo-reuse-observer-count`,
`layer.memo-get-or-else`, `layer.from-build-child-scope` and
`layer.fresh-drops-memoization` in `generated/effect-runtime-census.tsv`. Every
one was read off the pinned install first and written down here second;
`harness/trace/layer-tail.ts` and the goldens under `generated/traces/layer/`
are the standing evidence, and nothing here is a theorem about the host.

This module is the *traced face* of layer building and nothing else.
`Effect4/Layer/Memo.lean` remains the (still empty) owner of build identity,
sharing and local acquisition as semantic objects; a family is a signature, a
first-order handler and the rows that render it, and it declares no semantic
object on that stub's behalf.

## The four operations, and why they are these four

* `build layer` answers the layer's **service handle**. rc.112's memo entry
  stores the built context and replays it (`layer.memo-build-once`,
  `layer.memo-get-or-else`), so a memoized rebuild answers the *same service
  object* and constructs nothing. The handle is `Handle "Ref.Ref<number>"`:
  each declared layer constructs one `Ref`, the only thing the wire says about
  it is its index in first-seen order, and object identity across builds is
  exactly what a memo hit looks like from a program.

  The `Context` the build returns is *not* the identity: `buildWithMemoMap`
  maps `Context.add(CurrentMemoMap, memoMap)` over it
  (`layer.build-with-memo-map-service`), so the context wrapper is a fresh
  object on every build while the service inside it is not. Probed on the
  pinned install before this family was written.

* `provideCount layer` is how many times that layer's construction effect ran.
  A `Layer.fresh` wrapper is a *distinct layer identity* that builds the
  wrapped layer through a private memo map (`layer.fresh-drops-memoization`),
  so it constructs on every build and its constructions are counted against
  the layer it wraps.

* `scopeOf service` is the layer scope owning that construction's resources.
  `memoMapBuild` allocates one scope per construction, and the construction
  effect runs with it in context, so this separates a memoized rebuild (the
  same scope) from a fresh one (a new scope).

* `close` closes the enclosing scope and answers **the services it released,
  in release order**. That is the M1 `Scopes` shape, for the M1 reason: a
  `finalizer` row is not available to this family. `Family.Service.traced` is
  an around-wrapper over a handler in `M` — it writes one `op` and one
  `answer` per operation and has no access to `M`'s state — so region and
  finalizer events cannot be emitted without abandoning the derived tracer.
  The release order is carried as an answer instead, exactly as
  `Scopes.close` carries the keys it ran.

## The two facts the release answer carries

* **Reverse construction order.** `memoMapBuild` registers the memo entry's
  finalizer on the caller scope *before* running the construction, and a scope
  runs its finalizers in reverse registration order, so the last layer built
  is the first released.
* **Close is terminal.** A closed scope forks closed
  (`internal/effect.ts`, `scopeForkUnsafe`), so a build after `close`
  constructs into an already-closed layer scope: it is released inside its own
  build, it is not memoized, and the next `close` answers the empty order.

## Refusals, recorded here rather than discovered later

* **Observer counting is invisible.** A memoized rebuild registers the memo
  entry's finalizer a second time (`layer.memo-reuse-observer-count`); at close
  that finalizer decrements the observer count and releases nothing
  (`layer.memo-finalizer-last-observer`). One release per *construction*
  reaches the wire, never one per build, so the model keeps one live entry per
  construction. counterexample: E4-SEM-CE-013
* **Concurrent memo identity is out of reach.** `memoMapBuild` installs the
  entry and a `Deferred` before the construction runs, so a second fiber
  awaits the first fiber's result instead of constructing. This handler is a
  single-fiber state machine and the corpus is single-fiber; no event of this
  alphabet separates "awaited another fiber's build" from "answered the memo
  table". counterexample: E4-SEM-CE-014
* **Layer composition is not an operation.** `Layer.provide`, `Layer.merge`
  and the parent-chain lookup of a forked memo map
  (`layer.memo-map-parent-lookup`, `layer.provide-dependency-first`,
  `layer.merge-parallel-scopes`) are refused at this alphabet: they need a
  layer *value* on the wire, and a layer is a build function, not a handle.
  counterexample: E4-SEM-CE-015
-/

namespace Effect4.LayerFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

effect_signature Layers where
  | build (layer : Nat) : Handle "Ref.Ref<number>"
      ⟪ "build the layer", "provide it", "get the service" ⟫
  | provideCount (layer : Nat) : Nat
      ⟪ "how many times this layer's construction effect ran" ⟫
  | scopeOf (service : Handle "Ref.Ref<number>") : Handle "Scope.Closeable"
      ⟪ "the layer scope that owns this service" ⟫
  | close : List (Handle "Ref.Ref<number>")
      ⟪ "close the enclosing scope", "the services it released, in release order" ⟫

/-- The declared layers of the corpus. Layers `0`, `1` and `2` are ordinary
`Layer.effect` layers; layer `3` is `Layer.fresh` of layer `1`, a distinct
layer identity whose constructions are counted against layer `1`. -/
def freshOf : Nat → Option Nat
  | 3 => some 1
  | _ => none

/-- The layer whose construction effect actually runs. -/
def layerBase (n : Nat) : Nat := (freshOf n).getD n

/-- The memo table and construction ledger a `Layers` run carries.

`next` is the one handle counter: services and layer scopes share it, in
first-seen order, exactly as `handleIndex` in `harness/trace/tracer.ts` does on
the host. A construction takes its service index when it happens; a layer scope
takes its index the first time `scopeOf` asks for it. -/
structure LayerStore where
  /-- layer id → the service handle its memo entry answers -/
  memo : List (Nat × Nat) := []
  /-- layer id → how many times its construction effect ran -/
  counts : List (Nat × Nat) := []
  /-- service handle → its layer scope's handle, once one was asked for -/
  scopes : List (Nat × Nat) := []
  /-- service handles of the live constructions, in construction order -/
  live : List Nat := []
  /-- the next handle index -/
  next : Nat := 0
  /-- whether the enclosing scope has been closed -/
  closed : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- First value bound to a key. -/
def assocGet (table : List (Nat × Nat)) (key : Nat) : Option Nat :=
  (table.find? (·.1 == key)).map (·.2)

/-- Bind a key, keeping the position of one already bound. -/
def assocPut (table : List (Nat × Nat)) (key value : Nat) : List (Nat × Nat) :=
  if table.any (·.1 == key) then table.map (fun p => if p.1 == key then (key, value) else p)
  else table ++ [(key, value)]

/-- The Lean handler: the memo table, and no layer semantics beyond it. -/
def layersLive : Layers.Service (StateT LayerStore Id) := fun name =>
  match name with
  | .build => fun layer => do
      let store ← get
      -- A memo hit needs an open scope and an ordinary layer: a closed scope
      -- keeps nothing, and a `Layer.fresh` wrapper is never memoized.
      match (if store.closed || (freshOf layer).isSome then Option.none
             else assocGet store.memo layer) with
      | Option.some service => pure ⟨service⟩
      | Option.none =>
          let service := store.next
          let base := layerBase layer
          set { store with
                memo := if store.closed || (freshOf layer).isSome then store.memo
                        else assocPut store.memo layer service
                counts := assocPut store.counts base ((assocGet store.counts base).getD 0 + 1)
                -- A construction into a closed scope is released inside its own
                -- build, so it never joins the live set.
                live := if store.closed then store.live else store.live ++ [service]
                next := service + 1 }
          pure ⟨service⟩
  | .provideCount => fun layer => do
      let store ← get
      pure ((assocGet store.counts layer).getD 0)
  | .scopeOf => fun service => do
      let store ← get
      match assocGet store.scopes service.index with
      | Option.some scope => pure ⟨scope⟩
      | Option.none =>
          let scope := store.next
          set { store with scopes := assocPut store.scopes service.index scope, next := scope + 1 }
          pure ⟨scope⟩
  | .close => fun _ => do
      let store ← get
      set { store with memo := [], live := [], closed := true }
      pure (store.live.reverse.map fun service => ⟨service⟩)

-- One build: the layer is constructed once.
effect_program layerBuildOnce (n : Nat) over Layers : Nat :=
  let _ ← Layers.build(0)
  let c ← Layers.provideCount(0)
  return c

-- Two builds of one layer: the memo entry answers the same service and the
-- construction count stays one.
effect_program layerBuildMemo (n : Nat) over Layers : Nat :=
  let _ ← Layers.build(0)
  let _ ← Layers.build(0)
  let c ← Layers.provideCount(0)
  return c

-- Two layers, then close: the services come back last constructed first.
effect_program layerReleaseOrder (n : Nat) over Layers : List (Handle "Ref.Ref<number>") :=
  let _ ← Layers.build(0)
  let _ ← Layers.build(1)
  let r ← Layers.close()
  return r

-- A construction owns a layer scope of its own, and close releases it.
effect_program layerScopedRelease (n : Nat) over Layers : Handle "Scope.Closeable" :=
  let h ← Layers.build(2)
  let s ← Layers.scopeOf(h)
  let _ ← Layers.close()
  return s

-- `Layer.fresh` is never memoized: two builds construct twice, and both count
-- against the layer it wraps.
effect_program layerFreshRebuild (n : Nat) over Layers : Nat :=
  let _ ← Layers.build(3)
  let _ ← Layers.build(3)
  let c ← Layers.provideCount(1)
  return c

-- The memoized layer and its fresh wrapper are different identities, so the
-- fresh build takes a layer scope of its own.
effect_program layerFreshRegion (n : Nat) over Layers : Handle "Scope.Closeable" :=
  let _ ← Layers.build(1)
  let h ← Layers.build(3)
  let s ← Layers.scopeOf(h)
  return s

-- A fresh construction is released on the same rule as any other.
effect_program layerFreshRelease (n : Nat) over Layers : List (Handle "Ref.Ref<number>") :=
  let _ ← Layers.build(1)
  let _ ← Layers.build(3)
  let r ← Layers.close()
  return r

-- Close is terminal: the rebuild is a new construction (a new service, and the
-- count rises), and it is released inside its own build, so the second close
-- answers the empty order.
effect_program layerRebuildAfterClose (n : Nat) over Layers : Nat :=
  let _ ← Layers.build(0)
  let _ ← Layers.close()
  let _ ← Layers.build(0)
  let _ ← Layers.close()
  let c ← Layers.provideCount(0)
  return c

/-- The traced run of a layer program from the empty memo table, with its
outcome appended. -/
def layerGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program Layers.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × LayerStore :=
    ((interpret (Layers.traced layersLive).toHandler program).run []).run {}
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

/-- One layer program: its script and its golden log. -/
structure LayerEntry where
  name : String
  script : Script
  log : Effect4.Trace.Log

def layerEntry {α : Type} [Effects.Trace.ToVal α] (name : String) (script : Script)
    (program : Program Layers.Sig α) : LayerEntry :=
  { name := name, script := script, log := layerGoldenLog program }

/-- The eight programs of the corpus. -/
def layerPrograms : List LayerEntry :=
  [ layerEntry "buildOnce" layerBuildOnce.script (layerBuildOnce 0)
  , layerEntry "buildMemo" layerBuildMemo.script (layerBuildMemo 0)
  , layerEntry "releaseOrder" layerReleaseOrder.script (layerReleaseOrder 0)
  , layerEntry "scopedRelease" layerScopedRelease.script (layerScopedRelease 0)
  , layerEntry "freshRebuild" layerFreshRebuild.script (layerFreshRebuild 0)
  , layerEntry "freshRegion" layerFreshRegion.script (layerFreshRegion 0)
  , layerEntry "freshRelease" layerFreshRelease.script (layerFreshRelease 0)
  , layerEntry "rebuildAfterClose" layerRebuildAfterClose.script (layerRebuildAfterClose 0) ]

/-! ## The clauses of the memo table

Five equations, each `rfl`, so the projection above is not only prose. Their
axiom receipts are in `Effect4Test/Flow/LayersAxiomReport.lean`. -/

/-- A build of an ordinary layer into an open scope with nothing memoized takes
the next handle and joins the live set. -/
theorem build_constructs (store : LayerStore) :
    (layersLive Layers.Name.build 0 { store with closed := false, memo := [] }).2.live
      = store.live ++ [store.next] := rfl

/-- The same build memoizes the layer under that handle. -/
theorem build_memoizes (store : LayerStore) :
    (layersLive Layers.Name.build 0 { store with closed := false, memo := [] }).2.memo
      = [(0, store.next)] := rfl

/-- A second build of a memoized layer answers the memo entry and changes
nothing: no new handle, no new construction, no new live entry. -/
theorem build_memo_hit (store : LayerStore) (service : Nat) :
    layersLive Layers.Name.build 0 { store with closed := false, memo := [(0, service)] }
      = (⟨service⟩, { store with closed := false, memo := [(0, service)] }) := rfl

/-- A `Layer.fresh` wrapper is never answered from the memo table: layer 3
constructs even when it is bound there. -/
theorem build_fresh_ignores_memo (store : LayerStore) (service : Nat) :
    (layersLive Layers.Name.build 3
        { store with closed := false, memo := [(3, service)] }).1 = ⟨store.next⟩ := rfl

/-- A build after `close` still constructs, and never joins the live set: it is
released inside its own build. -/
theorem build_after_close_is_not_live (layer : Nat) (store : LayerStore) :
    (layersLive Layers.Name.build layer { store with closed := true }).2.live = store.live := rfl

/-- A build after `close` is not memoized either. -/
theorem build_after_close_is_not_memoized (layer : Nat) (store : LayerStore) :
    (layersLive Layers.Name.build layer { store with closed := true }).2.memo = store.memo := rfl

/-- `close` answers the live services in reverse construction order. -/
theorem close_releases_in_reverse (store : LayerStore) :
    (layersLive Layers.Name.close () store).1 =
      store.live.reverse.map (fun service => (⟨service⟩ : Handle "Ref.Ref<number>")) := rfl

/-- `close` is terminal, and leaves nothing live to release again. -/
theorem close_is_terminal (store : LayerStore) :
    ((layersLive Layers.Name.close () store).2.closed = true) ∧
      ((layersLive Layers.Name.close () store).2.live = []) := ⟨rfl, rfl⟩

end Effect4.LayerFamily
