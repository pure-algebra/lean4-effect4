import Effect4.Meta.Derive

/-!
# Layer.LayerFamily

`Layers`: a traced family over rc.112's layer machinery (`Layer.ts`,
`internal/layer.ts`), with the Lean handler that is a **memo-map store**: the
layer descriptions, the memo maps with their parent chain and observer counts,
the built contexts, the construction ledger and the live set.

This module is the *traced face* of layer building and nothing else.
`Effect4/Layer/Memo.lean` remains the (still empty) owner of build identity,
sharing and local acquisition as semantic objects; a family is a signature, a
first-order handler and the rows that render it, and it declares no semantic
object on that stub's behalf.

## A layer is a handle now, and that is what unlocks composition

The previous family named a layer by a `Nat` and rowed four operations, and
recorded `E4-SEM-CE-019` as a refusal: `Layer.provide`, `Layer.merge` and the
parent-chain lookup "need a layer *value* on the wire, and a layer is a build
function, not a handle". That refusal is **lifted**. A layer never crosses the
wire as a value here either — it crosses as a `Handle "Layer.Layer<number>"`
answered by the operation that *made* it, exactly as a `Ref` or a `Scope` does.
`succeed`, `effect`, `scoped`, `provide`, `provideMerge`, `merge`, `mergeAll`,
`fresh`, `memoize`, `orDie` and `unwrap` are the constructors; every one
answers a handle, and every consumer takes one.

`Layer.MemoMap` and `Context.Context<never>` are handles on the same terms, so
`buildWithMemoMap`, `forkMemoMap` and the parent lookup are rows and not prose.

## The two divergences that are *not* refusals of a row

Re-read against the store model (deep plan §0 ruling 4, the state note §4.3):

* **Observer counting is a model fact the host cannot see.** `E4-SEM-CE-017`
  said observer counting is "invisible", because a memoized rebuild registers
  the memo entry's finalizer a second time and at close that finalizer only
  decrements (`Layer.ts:401-410`), so one release per *construction* reaches
  the wire and never one per build. The store counts observers exactly
  (`memoMapReuse`'s `entry.observers++` at `:245`), and the `observers` row
  reads them. What the *host* cannot report without instrumenting the memo map
  is the count itself — the join from this model to a host trace forgets it.
  That is the forgetful direction of the join, not a refusal of the row: the
  row exists, the model is exact, and `harness/trace/layer-tail.ts` owes an
  observer counter of its own if the row is to be compared.
* **Concurrent memo identity is out of reach for the same reason it always
  was.** `memoMapBuild` installs the entry and a `Deferred` before the
  construction runs (`Layer.ts:390-419`), so a second fiber awaits the first
  fiber's result instead of constructing. This handler is a single-fiber state
  machine and the corpus is single-fiber; no event of this alphabet separates
  "awaited another fiber's build" from "answered the memo table". The model
  says the two are the same answer, and that is again forgetful rather than
  wrong. counterexample: E4-SEM-CE-018

## What the rows are, with their rc.112 lines

| row | rc.112 |
| --- | --- |
| `succeed` | `Layer.ts:1012` |
| `effect` | `Layer.ts:1347` |
| `scoped` | `Layer.ts:1347` over `internal/effect.ts:3938-3947` |
| `provide` | `Layer.ts:2008`, `provideWith` `:1907-1926` |
| `provideMerge` | `Layer.ts:2436`, `provideWith` `:1907-1926` |
| `merge` | `Layer.ts:1705` |
| `mergeAll` | `Layer.ts:1652`, `mergeAllEffect` `:1587-1602` |
| `fresh` | `Layer.ts:3850-3851` |
| `memoize` | `fromBuildMemo`, `Layer.ts:380-388` |
| `orDie` | `Layer.ts:3327` |
| `unwrap` | `Layer.ts:1580` |
| `makeMemoMap` | `Layer.ts:492`, `:545` |
| `forkMemoMap` | `Layer.ts:511`, `:564` |
| `build` | `Layer.ts:800-809` |
| `buildWithScope` | `Layer.ts:863`, `:970-980` |
| `buildWithMemoMap` | `Layer.ts:645`, `:756-765` |
| `launch` | `Layer.ts:3897-3898` |
| `servicesOf` | the built `Context`, read by tag |
| `scopeOf` | the layer scope `memoMapBuild` allocates, `Layer.ts:390-419` |
| `provideCount` | the construction ledger |
| `observers` | `Layer.ts:245`, `:403` |
| `close` | the enclosing scope, and the services it released |

rc.112 exports **no** `Layer.scoped` and **no** `Layer.memoize`. The `scoped`
row names `Layer.effect` of a construction that acquires in the layer scope
(`Layer.ts:1347` over `internal/effect.ts:3938-3947`), and `memoize` names
`fromBuildMemo` (`:380-388`), which is what `Layer.effect` already goes through
— so `memoize` is idempotent here, and says so.

Two refusals ride on that, both found by the host lane
(`docs/research/2026-09-03-lowering-l2-host-tails.md` §12.2, §12.3):

* **A `Layer`'s raw builder is not a public API.** `Layer.build(memoMap, scope)`
  is a member of the exported interface at `Layer.ts:56`, carries `@internal`,
  and is stripped from `dist/Layer.d.ts`. So `fresh`'s own one-line spelling at
  `:3851` cannot be written by a consumer, and this family models what `fresh`
  *does* — build through a private memo map — rather than how rc.112 spells it.
  The `build` row is the exported `Layer.build(self)` (`:800-809`), which is a
  different declaration and is public.
* **`memoize` on the host carries one extra service.** Because of the previous
  point the only builder a consumer can hand `fromBuildMemo` is
  `Layer.buildWithMemoMap`, which is `self.build(memoMap, scope)` **plus**
  installing the memo map as the `CurrentMemoMap` service and adding it to the
  produced context (`:761-765`). This row therefore does not claim
  `fromBuildMemo ∘ build`: the model's `memoize` is the identity on the memo
  behaviour, and the extra `CurrentMemoMap` binding the host tail's `memoize`
  leaves in the built context is not on this wire.

## Refusals kept

* **`launch` answers `Unit` and rc.112's never-returning `Effect<never>` is not
  on the wire.** `launch` is `scoped(andThen(build(self), never))`
  (`Layer.ts:3898`) and `never` is `callback<never>(constVoid)`
  (`internal/effect.ts:1172`): on the host the method does not return, so no
  golden of this lane can carry its answer. The row builds the layer — the
  construction ledger moves — and answers unit, and the park is refused.
* **A `close` answers the services released, not a finalizer stream.**
  `Family.Service.traced` is an around-wrapper over a handler in `M`: it writes
  one `op` and one `answer` per operation and has no access to `M`'s state, so
  region and finalizer events cannot be emitted without abandoning the derived
  tracer. Release order is carried as an answer instead, exactly as
  `Scopes.close` carries the keys it ran.
* **Reverse construction order and close-is-terminal** are the two facts that
  answer carries: `memoMapBuild` registers the memo entry's finalizer on the
  caller scope *before* running the construction and a scope runs finalizers in
  reverse registration order, so the last layer built is released first; and a
  closed scope forks closed (`internal/effect.ts` `scopeForkUnsafe`), so a
  build after `close` is released inside its own build, is not memoized, and
  the next `close` answers the empty order.
-/

set_option linter.unusedVariables false

namespace Effect4.LayerFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-! ## Handles -/

/-- A layer: answered by the constructor that made it, taken by every consumer.
The wire value is the index and nothing else. -/
abbrev LayerHandle := Handle "Layer.Layer<number>"

/-- A memo map (`Layer.ts:421-458`). -/
abbrev MemoMapHandle := Handle "Layer.MemoMap"

/-- A built context (`Layer.ts:54-60`: `build` answers `Context.Context<ROut>`). -/
abbrev ContextHandle := Handle "Context.Context<never>"

/-- A constructed service. Each declared layer constructs one `Ref`, and object
identity across builds is exactly what a memo hit looks like from a program. -/
abbrev ServiceHandle := Handle "Ref.Ref<number>"

/-- The layer scope `memoMapBuild` allocates per construction. -/
abbrev LayerScopeHandle := Handle "Scope.Closeable"

/-! ## The signature -/

effect_signature Layers where
  | succeed (service : Nat) : Handle "Layer.Layer<number>"
      ⟪ "a layer whose service is already a value" ⟫
  | effect (service : Nat) : Handle "Layer.Layer<number>"
      ⟪ "a layer built by an effect", "memoized through the memo map" ⟫
  | «scoped» (service : Nat) : Handle "Layer.Layer<number>"
      ⟪ "a layer whose construction acquires in its layer scope" ⟫
  | provide (layer : Handle "Layer.Layer<number>") (dependency : Handle "Layer.Layer<number>")
      : Handle "Layer.Layer<number>"
      ⟪ "build the dependency first and provide it", "its services do not reach the caller" ⟫
  | provideMerge (layer : Handle "Layer.Layer<number>")
      (dependency : Handle "Layer.Layer<number>") : Handle "Layer.Layer<number>"
      ⟪ "provide the dependency and keep it in the result" ⟫
  | merge (left : Handle "Layer.Layer<number>") (right : Handle "Layer.Layer<number>")
      : Handle "Layer.Layer<number>"
      ⟪ "both layers, one memo map" ⟫
  | mergeAll (layers : List (Handle "Layer.Layer<number>")) : Handle "Layer.Layer<number>"
      ⟪ "every layer, one parallel scope and one memo map" ⟫
  | fresh (layer : Handle "Layer.Layer<number>") : Handle "Layer.Layer<number>"
      ⟪ "a distinct identity that builds through a private memo map" ⟫
  | memoize (layer : Handle "Layer.Layer<number>") : Handle "Layer.Layer<number>"
      ⟪ "build through the caller's memo map", "what an effect layer already does" ⟫
  | orDie (layer : Handle "Layer.Layer<number>") : Handle "Layer.Layer<number>"
      ⟪ "the same layer with its error channel died" ⟫
  | unwrap (layer : Handle "Layer.Layer<number>") : Handle "Layer.Layer<number>"
      ⟪ "the layer an effect produces" ⟫
  | makeMemoMap : Handle "Layer.MemoMap" ⟪ "a fresh memo map with no parent" ⟫
  | forkMemoMap (parent : Handle "Layer.MemoMap") : Handle "Layer.MemoMap"
      ⟪ "a child memo map", "hits fall through to the parent" ⟫
  | build (layer : Handle "Layer.Layer<number>") : Handle "Context.Context<never>"
      ⟪ "build the layer into the ambient memo map", "the context it produced" ⟫
  | buildWithScope (layer : Handle "Layer.Layer<number>") (scope : Handle "Scope.Closeable")
      : Handle "Context.Context<never>"
      ⟪ "build into the given scope", "the memo map is still the ambient one" ⟫
  | buildWithMemoMap (layer : Handle "Layer.Layer<number>") (memoMap : Handle "Layer.MemoMap")
      (scope : Handle "Scope.Closeable") : Handle "Context.Context<never>"
      ⟪ "build with the given memo map and scope" ⟫
  | launch (layer : Handle "Layer.Layer<number>") : Unit
      ⟪ "build the layer and never return", "the park is not on this wire" ⟫
  | servicesOf (context : Handle "Context.Context<never>") : List (Handle "Ref.Ref<number>")
      ⟪ "the services the context holds, in order" ⟫
  | scopeOf (service : Handle "Ref.Ref<number>") : Handle "Scope.Closeable"
      ⟪ "the layer scope that owns this service" ⟫
  | provideCount (layer : Handle "Layer.Layer<number>") : Nat
      ⟪ "how many times this layer's construction effect ran" ⟫
  | observers (layer : Handle "Layer.Layer<number>") : Nat
      ⟪ "the memo entry's observer count" ⟫
  | close : List (Handle "Ref.Ref<number>")
      ⟪ "close the enclosing scope", "the services it released, in release order" ⟫

/-! ## The store -/

/-- What a layer handle describes. A `List Nat` field is admissible; a
`List LayerDesc` one would make this a *nested* inductive whose `DecidableEq`
handler refuses (state note §3.5). -/
inductive LayerDesc
  | succeed (service : Nat)
  | effect (service : Nat)
  | scopedIn (service : Nat)
  | provide (layer dependency : Nat)
  | provideMerge (layer dependency : Nat)
  | merge (left right : Nat)
  | mergeAll (layers : List Nat)
  | fresh (layer : Nat)
  | memoize (layer : Nat)
  | orDie (layer : Nat)
  | unwrap (layer : Nat)
deriving DecidableEq, Repr, Inhabited

/-- One memo entry (`Layer.ts:235-239`): the built service, its layer scope,
and the observer count `memoMapReuse` increments and the entry finalizer
decrements. -/
structure MemoEntry where
  layer : Nat
  service : Nat
  scope : Nat
  observers : Nat
deriving DecidableEq, Repr, Inhabited

/-- One memo map (`MemoMapImpl`, `Layer.ts:421-458`): a parent and a table. -/
structure MemoMap where
  parent : Option Nat := Option.none
  entries : List MemoEntry := []
deriving DecidableEq, Repr, Inhabited

/-- The store a `Layers` run carries.

`next` is the one handle counter: layers, memo maps, services, layer scopes and
contexts share it, in first-seen order, exactly as `handleIndex` in
`harness/trace/tracer.ts` does on the host. -/
structure LayerStore where
  /-- layer handle → its description -/
  layers : List (Nat × LayerDesc) := []
  /-- memo map handle → the map -/
  maps : List (Nat × MemoMap) := []
  /-- context handle → the services it holds, in order -/
  contexts : List (Nat × List Nat) := []
  /-- layer handle → how many times its construction effect ran -/
  counts : List (Nat × Nat) := []
  /-- service handle → its layer scope's handle -/
  scopes : List (Nat × Nat) := []
  /-- service handles of the live constructions, in construction order -/
  live : List Nat := []
  /-- the memo map `build` uses, created on first use
  (`CurrentMemoMap.forkOrCreate`, `Layer.ts:585-588`) -/
  ambient : Option Nat := Option.none
  /-- the next handle index -/
  next : Nat := 0
  /-- whether the enclosing scope has been closed -/
  closed : Bool := false
deriving Repr, DecidableEq, Inhabited

/-- First value bound to a key. -/
def assocGet {α : Type} (table : List (Nat × α)) (key : Nat) : Option α :=
  (table.find? (·.1 == key)).map (·.2)

/-- Bind a key, keeping the position of one already bound. -/
def assocPut {α : Type} (table : List (Nat × α)) (key : Nat) (value : α) : List (Nat × α) :=
  if table.any (·.1 == key) then table.map (fun p => if p.1 == key then (key, value) else p)
  else table ++ [(key, value)]

namespace LayerStore

/-- The description a layer handle names; an unbound handle is a frontier read
as an empty merge, which builds nothing. -/
def descOf (self : LayerStore) (layer : Nat) : LayerDesc :=
  (assocGet self.layers layer).getD (LayerDesc.mergeAll [])

/-- Allocate a handle for a new description. -/
def declare (self : LayerStore) (desc : LayerDesc) : LayerHandle × LayerStore :=
  (⟨self.next⟩,
    { self with layers := assocPut self.layers self.next desc, next := self.next + 1 })

/-- `makeMemoMapUnsafe` (`Layer.ts:492`) and `forkMemoMapUnsafe` (`:511`). -/
def declareMap (self : LayerStore) (parent : Option Nat) : MemoMapHandle × LayerStore :=
  (⟨self.next⟩,
    { self with
      maps := assocPut self.maps self.next { parent := parent, entries := [] }
      next := self.next + 1 })

/-- The memo maps `MemoMapImpl.get` consults, own map first then the parent
chain (`Layer.ts:434-443`). The sweep is bounded by the number of maps, so it
is a `foldl` and reduces in the kernel. -/
def memoChain (self : LayerStore) (map : Nat) : List Nat :=
  (List.range self.maps.length).foldl
    (fun acc _ =>
      match acc.getLast? with
      | Option.none => acc
      | Option.some current =>
          match (assocGet self.maps current).bind MemoMap.parent with
          | Option.some parent => if acc.contains parent then acc else acc ++ [parent]
          | Option.none => acc)
    [map]

/-- The map that holds an entry for `layer`, and the entry, following the
parent chain. `memoMapReuse` runs in the map the hit came from
(`Layer.ts:241-250`, `:442`). -/
def lookupMemo (self : LayerStore) (map : Nat) (layer : Nat) : Option (Nat × MemoEntry) :=
  (self.memoChain map).foldl
    (fun found current =>
      match found with
      | Option.some _ => found
      | Option.none =>
          match (assocGet self.maps current) with
          | Option.none => Option.none
          | Option.some m => (m.entries.find? (·.layer == layer)).map (fun e => (current, e)))
    Option.none

/-- `memoMapReuse` (`Layer.ts:241-250`): `entry.observers++` in the map the hit
came from. -/
def bumpObservers (self : LayerStore) (map : Nat) (layer : Nat) : LayerStore :=
  match assocGet self.maps map with
  | Option.none => self
  | Option.some m =>
      { self with
        maps := assocPut self.maps map
          { m with
            entries := m.entries.map fun e =>
              if e.layer == layer then { e with observers := e.observers + 1 } else e } }

/-- `memoMapBuild` (`Layer.ts:390-419`): `map.set` the entry with
`observers: 1`. -/
def installEntry (self : LayerStore) (map : Nat) (entry : MemoEntry) : LayerStore :=
  match assocGet self.maps map with
  | Option.none => self
  | Option.some m =>
      { self with maps := assocPut self.maps map { m with entries := m.entries ++ [entry] } }

/-- The observer count recorded for a layer, in the first map that holds it. -/
def observersOf (self : LayerStore) (layer : Nat) : Nat :=
  (self.maps.foldl
    (fun found entry =>
      match found with
      | Option.some _ => found
      | Option.none => (entry.2.entries.find? (·.layer == layer)).map MemoEntry.observers)
    Option.none).getD 0

end LayerStore

/-! ## The build

One function over a worklist of layers: `merge` and `mergeAll` flatten into it,
which is exactly what context concatenation is, and every other arm makes a
direct recursive call, so the recursion is structural on the fuel and reduces
in the kernel. Running out of fuel answers the empty context — a frontier of
the *model*, and one the corpus never reaches. -/

def buildMany : Nat → Nat → List Nat → LayerStore → List Nat × LayerStore
  | 0, _, _, store => ([], store)
  | _, _, [], store => ([], store)
  | Nat.succ fuel, map, layer :: rest, store =>
      match store.descOf layer with
      | .merge left right => buildMany fuel map (left :: right :: rest) store
      | .mergeAll layers => buildMany fuel map (layers ++ rest) store
      | .memoize inner => buildMany fuel map (inner :: rest) store
      | .orDie inner => buildMany fuel map (inner :: rest) store
      | .unwrap inner => buildMany fuel map (inner :: rest) store
      | .fresh inner =>
          -- `fresh` calls `self.build` directly with a brand new memo map
          -- (`Layer.ts:3851`), so nothing it builds is memoized in the caller's.
          let (privateMap, allocated) := store.declareMap Option.none
          let built := buildMany fuel privateMap.index [inner] allocated
          let tail := buildMany fuel map rest built.2
          (built.1 ++ tail.1, tail.2)
      | .provide inner dependency =>
          -- dependency first, and its services do not reach the caller
          -- (`Layer.ts:1915-1925`, combiner `identity`).
          let dep := buildMany fuel map [dependency] store
          let own := buildMany fuel map [inner] dep.2
          let tail := buildMany fuel map rest own.2
          (own.1 ++ tail.1, tail.2)
      | .provideMerge inner dependency =>
          -- `provideWith(self, that, (self, that) => Context.merge(that, self))`
          -- (`Layer.ts:2797-2805`): the dependency stays in the result.
          let dep := buildMany fuel map [dependency] store
          let own := buildMany fuel map [inner] dep.2
          let tail := buildMany fuel map rest own.2
          (dep.1 ++ own.1 ++ tail.1, tail.2)
      | .succeed _ =>
          let head := buildBase fuel map layer store
          (head.1 ++ (buildMany fuel map rest head.2).1, (buildMany fuel map rest head.2).2)
      | .effect _ =>
          let head := buildBase fuel map layer store
          (head.1 ++ (buildMany fuel map rest head.2).1, (buildMany fuel map rest head.2).2)
      | .scopedIn _ =>
          let head := buildBase fuel map layer store
          (head.1 ++ (buildMany fuel map rest head.2).1, (buildMany fuel map rest head.2).2)
  where
    /-- `getOrElseMemoize` (`Layer.ts:445-457`): the map first, then
    `memoMapBuild`. -/
    buildBase (fuel : Nat) (map : Nat) (layer : Nat) (store : LayerStore) :
        List Nat × LayerStore :=
      match store.lookupMemo map layer with
      | Option.some (owner, entry) => ([entry.service], store.bumpObservers owner layer)
      | Option.none =>
          let service := store.next
          let scope := store.next + 1
          let constructed : LayerStore :=
            { store with
              next := store.next + 2
              counts := assocPut store.counts layer ((assocGet store.counts layer).getD 0 + 1)
              scopes := assocPut store.scopes service scope
              -- A construction into a closed scope is released inside its own
              -- build, so it never joins the live set.
              live := if store.closed then store.live else store.live ++ [service] }
          -- A closed scope keeps nothing, so the entry is not installed either.
          ([service],
            if store.closed then constructed
            else constructed.installEntry map
              { layer := layer, service := service, scope := scope, observers := 1 })

/-- The fuel a build of one layer needs: every arm either shortens the worklist
or replaces a head by its immediate children, and the description graph is
acyclic because a description can only name handles that already existed. -/
def buildFuel (store : LayerStore) : Nat := (store.layers.length + 1) * (store.layers.length + 2)

/-! ## The handler -/

/-- The ambient memo map, created on first use: `CurrentMemoMap.forkOrCreate`
answers the one in context, or makes one (`Layer.ts:585-588`). This projection
keeps one for the whole run, which is what providing a single program does. -/
def ambientMap (store : LayerStore) : Nat × LayerStore :=
  match store.ambient with
  | Option.some map => (map, store)
  | Option.none =>
      let (handle, allocated) := store.declareMap Option.none
      (handle.index, { allocated with ambient := Option.some handle.index })

/-- Build a layer into a memo map and record the context it produced. -/
def buildInto (store : LayerStore) (map : Nat) (layer : Nat) : ContextHandle × LayerStore :=
  let built := buildMany (buildFuel store) map [layer] store
  let context := built.2.next
  (⟨context⟩,
    { built.2 with
      contexts := assocPut built.2.contexts context built.1
      next := context + 1 })

/-- The Lean handler: the memo-map store, and no layer semantics beyond it. -/
def layersLive : Layers.Service (StateT LayerStore Id) := fun name =>
  match name with
  | .succeed => fun service => do
      let store ← get
      let (handle, store') := store.declare (.succeed service)
      set store'; pure handle
  | .effect => fun service => do
      let store ← get
      let (handle, store') := store.declare (.effect service)
      set store'; pure handle
  | .«scoped» => fun service => do
      let store ← get
      let (handle, store') := store.declare (.scopedIn service)
      set store'; pure handle
  | .provide => fun (layer, dependency) => do
      let store ← get
      let (handle, store') := store.declare (.provide layer.index dependency.index)
      set store'; pure handle
  | .provideMerge => fun (layer, dependency) => do
      let store ← get
      let (handle, store') := store.declare (.provideMerge layer.index dependency.index)
      set store'; pure handle
  | .merge => fun (left, right) => do
      let store ← get
      let (handle, store') := store.declare (.merge left.index right.index)
      set store'; pure handle
  | .mergeAll => fun layers => do
      let store ← get
      let (handle, store') := store.declare (.mergeAll (layers.map Handle.index))
      set store'; pure handle
  | .fresh => fun layer => do
      let store ← get
      let (handle, store') := store.declare (.fresh layer.index)
      set store'; pure handle
  | .memoize => fun layer => do
      let store ← get
      let (handle, store') := store.declare (.memoize layer.index)
      set store'; pure handle
  | .orDie => fun layer => do
      let store ← get
      let (handle, store') := store.declare (.orDie layer.index)
      set store'; pure handle
  | .unwrap => fun layer => do
      let store ← get
      let (handle, store') := store.declare (.unwrap layer.index)
      set store'; pure handle
  | .makeMemoMap => fun _ => do
      let store ← get
      let (handle, store') := store.declareMap Option.none
      set store'; pure handle
  | .forkMemoMap => fun parent => do
      let store ← get
      let (handle, store') := store.declareMap (Option.some parent.index)
      set store'; pure handle
  | .build => fun layer => do
      let store ← get
      let (map, withMap) := ambientMap store
      let (context, store') := buildInto withMap map layer.index
      set store'; pure context
  | .buildWithScope => fun (layer, scope) => do
      -- Only the scope argument is replaced; the memo map is still the
      -- ambient one (`Layer.ts:974-979`).
      let store ← get
      let (map, withMap) := ambientMap store
      let (context, store') := buildInto withMap map layer.index
      set store'; pure context
  | .buildWithMemoMap => fun (layer, memoMap, scope) => do
      let store ← get
      let (context, store') := buildInto store memoMap.index layer.index
      set store'; pure context
  | .launch => fun layer => do
      let store ← get
      let (map, withMap) := ambientMap store
      let (_, store') := buildInto withMap map layer.index
      set store'
  | .servicesOf => fun context => do
      let store ← get
      pure (((assocGet store.contexts context.index).getD []).map fun service => ⟨service⟩)
  | .scopeOf => fun service => do
      let store ← get
      pure ⟨(assocGet store.scopes service.index).getD service.index⟩
  | .provideCount => fun layer => do
      let store ← get
      pure ((assocGet store.counts layer.index).getD 0)
  | .observers => fun layer => do
      let store ← get
      pure (store.observersOf layer.index)
  | .close => fun _ => do
      let store ← get
      set { store with
            maps := store.maps.map
              (fun (entry : Nat × MemoMap) => (entry.1, { entry.2 with entries := [] }))
            live := []
            closed := true }
      pure (store.live.reverse.map fun service => ⟨service⟩)

/-! ## The clauses of the memo-map store

Each is `rfl` or `decide` at the store, so the projection above is not only
prose. Their axiom receipts are in
`Effect4Test/Flow/LayersAxiomReport.lean`. -/

/-- A declared layer takes the next handle and binds its description. -/
theorem declare_takes_the_next_handle (store : LayerStore) (desc : LayerDesc) :
    store.declare desc =
      (⟨store.next⟩,
        { store with layers := assocPut store.layers store.next desc, next := store.next + 1 }) :=
  rfl

/-- `MemoMapImpl.get` looks in its own map first and then walks the parent
chain (`Layer.ts:434-443`); the chain starts at the map itself.
census: layer.memo-map-parent-lookup -/
theorem memoChain_starts_at_the_map (store : LayerStore) (map : Nat)
    (h : store.maps = []) : store.memoChain map = [map] := by
  simp [LayerStore.memoChain, h]

/-- A memo hit answers the entry's service and increments the observer count in
the map the hit came from; nothing is constructed.
census: layer.memo-get-or-else, layer.memo-reuse-observer-count -/
theorem buildBase_memo_hit (fuel map layer : Nat) (store : LayerStore) (owner : Nat)
    (entry : MemoEntry) (h : store.lookupMemo map layer = Option.some (owner, entry)) :
    buildMany.buildBase fuel map layer store =
      ([entry.service], store.bumpObservers owner layer) := by
  simp [buildMany.buildBase, h]

/-- A miss constructs: the service takes the next handle, its layer scope the
one after it, and the construction is counted.
census: layer.memo-build-once -/
theorem buildBase_miss_constructs (fuel map layer : Nat) (store : LayerStore)
    (h : store.lookupMemo map layer = Option.none) :
    (buildMany.buildBase fuel map layer store).1 = [store.next] := by
  simp [buildMany.buildBase, h]

/-- A build after `close` still constructs, and never joins the live set: it is
released inside its own build. -/
theorem buildBase_after_close_is_not_live (fuel map layer : Nat) (store : LayerStore)
    (h : (LayerStore.lookupMemo { store with closed := true } map layer) = Option.none) :
    (buildMany.buildBase fuel map layer { store with closed := true }).2.live = store.live := by
  simp [buildMany.buildBase, h]

/-- `close` answers the live services in reverse construction order. -/
theorem close_releases_in_reverse (store : LayerStore) :
    (layersLive Layers.Name.close () store).1 =
      store.live.reverse.map (fun service => (⟨service⟩ : ServiceHandle)) := rfl

/-- `close` is terminal, and leaves nothing live to release again. -/
theorem close_is_terminal (store : LayerStore) :
    ((layersLive Layers.Name.close () store).2.closed = true) ∧
      ((layersLive Layers.Name.close () store).2.live = []) := ⟨rfl, rfl⟩

private theorem all_entries_empty (maps : List (Nat × MemoMap)) :
    (maps.map (fun (entry : Nat × MemoMap) => (entry.1, { entry.2 with entries := [] }))).all
      (fun entry => entry.2.entries.isEmpty) = true := by
  induction maps with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- `close` empties every memo map, so no build after it can hit one: the
rebuild is a new construction. -/
theorem close_empties_every_memo_map (store : LayerStore) :
    (layersLive Layers.Name.close () store).2.maps.all
      (fun entry => entry.2.entries.isEmpty) = true :=
  all_entries_empty store.maps

/-! ## The programs

`layerServices 0` is the pure atom that reads the first service out of a built
context, because `scopeOf` takes one handle and `servicesOf` answers a list. -/

effect_atoms LayerAtoms importing handles [Ref] from "effect" where
  | firstService (services : List (Handle "Ref.Ref<number>")) : Handle "Ref.Ref<number>"
      ⟪ "services[0]" ⟫ := (services.head?.getD ⟨0⟩)
  | twoLayers (left : Handle "Layer.Layer<number>") (right : Handle "Layer.Layer<number>")
      : List (Handle "Layer.Layer<number>") ⟪ "[left, right]" ⟫ := [left, right]

-- One build: the layer is constructed once.
effect_program layerBuildOnce (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let _ ← Layers.build(l)
  let c ← Layers.provideCount(l)
  return c

-- Two builds of one layer: the memo entry answers the same service, the
-- construction count stays one, and the observer count rises to two.
effect_program layerBuildMemo (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let _ ← Layers.build(l)
  let _ ← Layers.build(l)
  let c ← Layers.provideCount(l)
  return c

-- The observer count is a model fact: one construction, two builds, two
-- observers.
effect_program layerObserverCount (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let _ ← Layers.build(l)
  let _ ← Layers.build(l)
  let o ← Layers.observers(l)
  return o

-- Two layers, then close: the services come back last constructed first.
effect_program layerReleaseOrder (n : Nat) over Layers : List (Handle "Ref.Ref<number>") :=
  let a ← Layers.effect(0)
  let b ← Layers.effect(1)
  let _ ← Layers.build(a)
  let _ ← Layers.build(b)
  let r ← Layers.close()
  return r

-- A construction owns a layer scope of its own, and close releases it.
effect_program layerScopedRelease (n : Nat) over Layers : Handle "Scope.Closeable" :=
  let l ← Layers.«scoped»(2)
  let ctx ← Layers.build(l)
  let ss ← Layers.servicesOf(ctx)
  let s ← Layers.scopeOf(firstService ss)
  let _ ← Layers.close()
  return s

-- `Layer.fresh` is never memoized: two builds construct twice, and both count
-- against the layer it wraps.
effect_program layerFreshRebuild (n : Nat) over Layers : Nat :=
  let base ← Layers.effect(1)
  let f ← Layers.fresh(base)
  let _ ← Layers.build(f)
  let _ ← Layers.build(f)
  let c ← Layers.provideCount(base)
  return c

-- A fresh construction is released on the same rule as any other.
effect_program layerFreshRelease (n : Nat) over Layers : List (Handle "Ref.Ref<number>") :=
  let base ← Layers.effect(1)
  let f ← Layers.fresh(base)
  let _ ← Layers.build(base)
  let _ ← Layers.build(f)
  let r ← Layers.close()
  return r

-- Close is terminal: the rebuild is a new construction (a new service, and the
-- count rises), it is released inside its own build, and the second close
-- answers the empty order.
effect_program layerRebuildAfterClose (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let _ ← Layers.build(l)
  let _ ← Layers.close()
  let _ ← Layers.build(l)
  let _ ← Layers.close()
  let c ← Layers.provideCount(l)
  return c

-- `provide` builds the dependency first and keeps it out of the result;
-- `provideMerge` keeps it in. E4-SEM-CE-019, lifted.
effect_program layerProvideDependencyFirst (n : Nat) over Layers
    : List (Handle "Ref.Ref<number>") :=
  let dep ← Layers.effect(0)
  let l ← Layers.effect(1)
  let p ← Layers.provide(l, dep)
  let ctx ← Layers.build(p)
  let ss ← Layers.servicesOf(ctx)
  return ss

effect_program layerProvideMergeKeepsDependency (n : Nat) over Layers
    : List (Handle "Ref.Ref<number>") :=
  let dep ← Layers.effect(0)
  let l ← Layers.effect(1)
  let p ← Layers.provideMerge(l, dep)
  let ctx ← Layers.build(p)
  let ss ← Layers.servicesOf(ctx)
  return ss

-- `merge` and `mergeAll` share one memo map, so a layer named twice is built
-- once.
effect_program layerMergeAllSharesMemo (n : Nat) over Layers : Nat :=
  let a ← Layers.effect(0)
  let m ← Layers.mergeAll(twoLayers a a)
  let _ ← Layers.build(m)
  let c ← Layers.provideCount(a)
  return c

-- A forked memo map hits the parent's entry: nothing is constructed a second
-- time, and the parent's observer count is what rises.
effect_program layerMemoMapParentLookup (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let ctx ← Layers.build(l)
  let ss ← Layers.servicesOf(ctx)
  let s ← Layers.scopeOf(firstService ss)
  let parent ← Layers.makeMemoMap()
  let child ← Layers.forkMemoMap(parent)
  let _ ← Layers.buildWithMemoMap(l, parent, s)
  let _ ← Layers.buildWithMemoMap(l, child, s)
  let c ← Layers.provideCount(l)
  return c

-- `launch` builds the layer; rc.112 then parks forever, which is not on this
-- wire.
effect_program layerLaunchBuilds (n : Nat) over Layers : Nat :=
  let l ← Layers.effect(0)
  let _ ← Layers.launch(l)
  let c ← Layers.provideCount(l)
  return c

/-- The traced run of a layer program from the empty store, with its outcome
appended. -/
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

/-- The corpus. -/
def layerPrograms : List LayerEntry :=
  [ layerEntry "buildOnce" layerBuildOnce.script (layerBuildOnce 0)
  , layerEntry "buildMemo" layerBuildMemo.script (layerBuildMemo 0)
  , layerEntry "observerCount" layerObserverCount.script (layerObserverCount 0)
  , layerEntry "releaseOrder" layerReleaseOrder.script (layerReleaseOrder 0)
  , layerEntry "scopedRelease" layerScopedRelease.script (layerScopedRelease 0)
  , layerEntry "freshRebuild" layerFreshRebuild.script (layerFreshRebuild 0)
  , layerEntry "freshRelease" layerFreshRelease.script (layerFreshRelease 0)
  , layerEntry "rebuildAfterClose" layerRebuildAfterClose.script (layerRebuildAfterClose 0)
  , layerEntry "provideDependencyFirst" layerProvideDependencyFirst.script
      (layerProvideDependencyFirst 0)
  , layerEntry "provideMergeKeepsDependency" layerProvideMergeKeepsDependency.script
      (layerProvideMergeKeepsDependency 0)
  , layerEntry "mergeAllSharesMemo" layerMergeAllSharesMemo.script (layerMergeAllSharesMemo 0)
  , layerEntry "memoMapParentLookup" layerMemoMapParentLookup.script (layerMemoMapParentLookup 0)
  , layerEntry "launchBuilds" layerLaunchBuilds.script (layerLaunchBuilds 0) ]

/-- The pure atoms the layer scripts call. -/
def layerAtomNames : List String := ["firstService", "twoLayers"]

end Effect4.LayerFamily
