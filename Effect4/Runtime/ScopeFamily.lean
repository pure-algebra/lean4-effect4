import Effect4.Meta.Derive
import Effect4.Runtime.Scope

/-!
# Runtime.ScopeFamily

`Scopes`: a traced family over rc.112's `Scope`, with the Lean handler that is
the *projection of the scope store* — spike S2's `ScopeStore`
(`docs/research/2026-09-03-spike-s2-stores-witnesses.md` §1.4) at this family's
alphabet, over the frozen `Effect4/Runtime/Scope.lean` state machine.

`Scope.lean` itself is untouched: this module is beside it, uses `Scope.make`,
`Scope.addExit`, `Scope.removeUnsafe`, `Scope.fork`, `Scope.close` and
`Scope.closeOrder` unchanged, and adds no scope semantics of its own.

## One declaration site

The four-row `Scopes` family used to be declared inside
`harness/trace/Generate.lean`, which is a script and not a library, so nothing
under `Effect4/` could state a theorem about it. It is declared here now and
the script imports it.

## The rows

The first four keep their spelling, their order and their answers exactly, so
the goldens under `generated/traces/scope/` are unchanged. Twelve rows follow.

| row | rc.112 | what it does |
| --- | --- | --- |
| `make` | `Scope.ts:240`, `internal/effect.ts:3915-3922` | a new scope at the default `"sequential"` strategy |
| `addFinalizer` | `Scope.ts:456`, `internal/effect.ts:3867-3888` | register, or run now on a closed scope |
| `remove` | `internal/effect.ts:3891-3904` | unregister a key |
| `close` | `Scope.ts:567`, `internal/effect.ts:3779-3798` | close with the void exit; answers the keys it ran |
| `makeWith` | `internal/effect.ts:3915-3922` | the same `make`, with the strategy given |
| `fork` | `Scope.ts:489`, `internal/effect.ts:3834-3844` | a child scope, linked by one shared key |
| `addFinalizerExit` | `Scope.ts:422`, `internal/effect.ts:3847-3858` | register a finalizer that receives the closing exit |
| `closeExit` | `internal/effect.ts:3779-3798` | close with a given exit |
| `isClosed` | `Scope.ts:99-187` | the state is `Closed` |
| `closedWith` | `Scope.ts:99-187` | `none` while open, else whether the closing exit succeeded |
| `provide` | `Scope.ts:310` | run with the scope in context and **do not** close it |
| `use` | `Scope.ts:616` | run with the scope in context and close it on exit |
| `forkIn` | `internal/effect.ts:5355-5379` | link a fiber to the scope, with the self-interrupt guard |
| `runIn` | `internal/effect.ts:5447-5461` | the same without the guard |
| `linked` | — | the fibers linked to the scope, in link order |
| `exitFiber` | `internal/effect.ts:5377`, `:5459` | the observer that removes an exited fiber's key |

Two spellings need saying out loud:

* rc.112 v4 has **no `Scope.extend`**. The v3 operation that provides a scope
  to an effect without closing it is `Scope.provide` (`Scope.ts:310`), and the
  row is named after the v4 spelling.
* `make` stays nullary and takes rc.112's own `"sequential"` default
  (`internal/effect.ts:3915`); `makeWith` is the same entry point with the
  optional argument supplied. Splitting it is what keeps the existing goldens
  byte-identical, and it costs nothing: the two rows are one rc.112 call.

## What the store carries

`ScopeCarrier` is `Effect4.Scope` keyed by the handle's own index, with the
finalizer alphabet `FinName`. That alphabet is the point: `SCOPE-FB-FINALIZER-MEANING`
(`docs/SCOPE-DAG.md:228`) is open because `Scope.lean` registers *nominal*
finalizers and nothing says what a fork's two names mean. Here they are
`closeChildScope child` and `detachFromParent parent`, so `fork` registers the
pair rc.112 registers (`internal/effect.ts:3834-3844`) and
`fork_registers_the_linkage_names` states it.

`close` runs the child scopes its order names, so `closeChildScope` *means*
`scopeClose(child, exit)` here and not only on paper. What `close` **answers**
is still this scope's own keys in run order — the answer the goldens carry —
so a cascade is visible through `isClosed` of the child and never by a longer
answer.

## Refusals

- **The parallel strategy is recorded, not run.** `makeWith 1` stores
  `FinalizerStrategy.parallel` and `close` still runs the order sequentially:
  the parallel close forks one daemon fiber per finalizer
  (`internal/effect.ts:3819-3826`) and this lane has no fiber machine. The
  strategy is therefore observable in the store and not in a golden.
  census: scope.close-parallel
- **A finalizer's own exit is nominal.** `addFinalizer` and `addFinalizerExit`
  are the same store operation here, because `scopeRun` is the void exit for
  every name: what a finalizer *does* is DB-02's supplied `run` argument, not
  canonical content. The two rows differ on the host and not in this model.
- **A fresh linkage key is a counter, not an identity.** rc.112 mints a key
  object per `forkIn`; this store mints `100, 101, …`, above the corpus's own
  keys, and `SCOPE-FB-KEY-IDENTITY` (`Effect4/Runtime/Scope.lean`
  `key_freshness_refused`) is the standing refusal that an index is only a
  stand-in for an identity.
- **`remove` has no rc.112 entry point.** `effect`'s package exports map
  `"./internal/*"` to `null`, so `scopeRemoveFinalizerUnsafe` is unreachable;
  the host service performs the same two-arm removal over the *public* mutable
  `Scope.state`. The `remove` golden pins the public state shape and the model,
  not an rc.112 call.
-/

set_option linter.unusedVariables false

namespace Effect4.ScopeFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-- The handle every operation takes and returns: rc.112's own opaque
`Scope.Closeable`. -/
abbrev ScopeHandle := Handle "Scope.Closeable"

/-! ## The finalizer alphabet

A finalizer is a *name*: DB-02 keeps Lean functions out of canonical content,
and `Effect4.Scope` takes what a name does as its `run` argument. Every arm
carries the key it was registered under, because that key is what `close`
answers. -/

/-- What a registered finalizer is. The three linkage arms are the ones
`SCOPE-FB-FINALIZER-MEANING` asks for. -/
inductive FinName
  /-- An ordinary program finalizer, registered by `addFinalizer`. -/
  | release (key : Nat)
  /-- The parent side of a fork: `scopeClose(child, exit)`
  (`internal/effect.ts:3836-3841`). -/
  | closeChildScope (key : Nat) (child : Nat)
  /-- The child side of a fork: `scopeRemoveFinalizerUnsafe(parent, key)`
  (`internal/effect.ts:3842`). -/
  | detachFromParent (key : Nat) (parent : Nat)
  /-- A linked fiber: `forkIn` guards against the interruptor being the fiber
  itself (`internal/effect.ts:5368-5372`), `fiberRunIn` does not (`:5455`). -/
  | interruptFiber (key : Nat) (fiber : Nat) (skipSelf : Bool)
deriving DecidableEq, Repr, Inhabited

/-- The key a finalizer was registered under; this is what `close` answers. -/
def FinName.key : FinName → Nat
  | .release key => key
  | .closeChildScope key _ => key
  | .detachFromParent key _ => key
  | .interruptFiber key _ _ => key

/-! ## The store -/

/-- The exit a close carries at this alphabet: a value carrying nothing, or a
typed failure. -/
abbrev ScopeExit := Exit Unit Nat Unit Unit Unit

/-- One scope: the frozen `Effect4.Scope` state machine over the finalizer
alphabet, keyed by `Nat`. -/
abbrev ScopeCarrier := Effect4.Scope Nat FinName Unit Nat Unit Unit Unit

/-- The nominal finalizer's effect. Nothing in this family observes a
finalizer's own exit, so it is the void exit; a fallible release is the packet
that settles the cause-merge divergence, and is refused here. -/
def scopeRun : FinName → ScopeExit → Exit Unit Nat Unit Unit Unit :=
  fun _ _ => Exit.void

/-- The scope store: every live scope in creation order (a `Handle` indexes
into it), the fibers linked to each, and the counter linkage keys are minted
from. -/
structure ScopeStore where
  /-- Every scope, in creation order. -/
  scopes : List ScopeCarrier := []
  /-- `(scope index, fiber id)` for every live link, in link order. -/
  links : List (Nat × Nat) := []
  /-- The next linkage key. It starts above the corpus's own keys so a golden
  can tell a program's finalizer from a linkage one. -/
  nextKey : Nat := 100
deriving Inhabited

namespace ScopeStore

/-- The scope under a handle; `none` is a frontier. -/
def scopeAt (self : ScopeStore) (handle : ScopeHandle) : Option ScopeCarrier :=
  self.scopes[handle.index]?

/-- Replace one scope. -/
def setScope (self : ScopeStore) (handle : ScopeHandle) (scope : ScopeCarrier) : ScopeStore :=
  { self with scopes := self.scopes.set handle.index scope }

/-- `scopeMakeUnsafe` (`internal/effect.ts:3915-3922`). -/
def make (self : ScopeStore) (strategy : FinalizerStrategy) : ScopeHandle × ScopeStore :=
  (⟨self.scopes.length⟩, { self with scopes := self.scopes ++ [Effect4.Scope.make strategy] })

/-- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`): register while
open, run now when closed. The answer is whether it was registered. -/
def addFinalizer (self : ScopeStore) (handle : ScopeHandle) (key : Nat) (finalizer : FinName) :
    ScopeStore × Bool :=
  match self.scopeAt handle with
  | Option.none => (self, false)
  | Option.some scope =>
      (self.setScope handle (Effect4.Scope.addExit scopeRun scope key finalizer).1,
        !scope.isClosed)

/-- `scopeRemoveFinalizerUnsafe` (`internal/effect.ts:3891-3904`). -/
def removeFinalizer (self : ScopeStore) (handle : ScopeHandle) (key : Nat) : ScopeStore :=
  match self.scopeAt handle with
  | Option.none => self
  | Option.some scope => self.setScope handle (scope.removeUnsafe key)

/-- `scopeForkUnsafe` (`internal/effect.ts:3833-3844`): one shared key links a
parent finalizer closing the child to a child finalizer removing itself from
the parent. -/
def forkChild (self : ScopeStore) (parent : ScopeHandle) (strategy : FinalizerStrategy) :
    ScopeHandle × ScopeStore :=
  match self.scopeAt parent with
  | Option.none => (parent, self)
  | Option.some parentScope =>
      let child : Nat := self.scopes.length
      let key := self.nextKey
      let forked :=
        Effect4.Scope.fork parentScope strategy key
          (FinName.closeChildScope key child) (FinName.detachFromParent key parent.index)
      (⟨child⟩,
        { self with
          scopes := (self.setScope parent forked.1).scopes ++ [forked.2]
          nextKey := key + 1 })

/-- The keys a close would run, in run order (`internal/effect.ts:3815`). -/
def closeOrderOf (self : ScopeStore) (handle : ScopeHandle) : List Nat :=
  match self.scopeAt handle with
  | Option.none => []
  | Option.some scope => scope.closeOrder.map FinName.key

/-- The child scopes a scope's close order names (`internal/effect.ts:3841`). -/
def childrenOf (self : ScopeStore) (index : Nat) : List Nat :=
  match self.scopes[index]? with
  | Option.none => []
  | Option.some scope =>
      scope.closeOrder.filterMap fun finalizer =>
        match finalizer with
        | .closeChildScope _ child => Option.some child
        | _ => Option.none

/-- One round of the reachability sweep: every child a scope already in the set
names, added once. -/
def expand (self : ScopeStore) (acc : List Nat) : List Nat :=
  acc.foldl
    (fun current index =>
      (self.childrenOf index).foldl
        (fun reached child => if reached.contains child then reached else reached ++ [child])
        current)
    acc

/-- The scopes a close of `index` reaches: itself, and the children its order
names, to a fixed point. The sweep is bounded by the number of scopes, which is
the length of the longest possible chain, so it is a `foldl` and not a
recursion — and therefore reduces in the kernel. -/
def reach (self : ScopeStore) (index : Nat) : List Nat :=
  (List.range self.scopes.length).foldl (fun acc _ => self.expand acc) [index]

/-- `scopeCloseUnsafe` (`internal/effect.ts:3779-3798`) on one scope: the state
is written first, so it cannot depend on what a finalizer does. -/
def closeOne (self : ScopeStore) (index : Nat) (exit : ScopeExit) : ScopeStore :=
  match self.scopes[index]? with
  | Option.none => self
  | Option.some scope =>
      { self with
        scopes := self.scopes.set index (Effect4.Scope.close scopeRun scope exit).1 }

/-- Close a scope, and every child scope its order names, with the same exit.
The reachable set is read off the store *before* any state is written, which is
what makes the cascade a consequence of the registration order and not of the
close itself. -/
def close (self : ScopeStore) (handle : ScopeHandle) (exit : ScopeExit) : ScopeStore :=
  (self.reach handle.index).foldl (fun current index => current.closeOne index exit) self

/-- Link a fiber to a scope. An open scope registers `interruptFiber` under a
fresh key and answers `true`; a closed one interrupts the fiber at once and
answers `false` (`internal/effect.ts:5364-5378`). -/
def linkFiber (self : ScopeStore) (handle : ScopeHandle) (fiber : Nat) (skipSelf : Bool) :
    ScopeStore × Bool :=
  match self.scopeAt handle with
  | Option.none => (self, false)
  | Option.some scope =>
      if scope.isClosed then (self, false)
      else
        let key := self.nextKey
        let registered :=
          self.setScope handle
            (Effect4.Scope.addExit scopeRun scope key
              (FinName.interruptFiber key fiber skipSelf)).1
        ({ registered with
            links := self.links ++ [(handle.index, fiber)]
            nextKey := key + 1 }, true)

/-- The fibers linked to a scope, in link order. -/
def linkedTo (self : ScopeStore) (handle : ScopeHandle) : List Nat :=
  (self.links.filter (fun link => link.1 == handle.index)).map Prod.snd

/-- The observer a linked fiber installs: on exit it removes its own key from
the scope (`internal/effect.ts:5377`, `:5459`). -/
def dropLink (self : ScopeStore) (handle : ScopeHandle) (fiber : Nat) : ScopeStore :=
  match self.scopeAt handle with
  | Option.none => self
  | Option.some scope =>
      let keys : List Nat :=
        scope.finalizers.filterMap fun entry =>
          match entry.2 with
          | .interruptFiber key linked _ => if linked == fiber then Option.some key else Option.none
          | _ => Option.none
      { keys.foldl (fun current key => current.removeFinalizer handle key) self with
        links := self.links.filter (fun link => !(link.1 == handle.index && link.2 == fiber)) }

end ScopeStore

/-! ## The signature -/

effect_signature Scopes where
  | make : Handle "Scope.Closeable" ⟪ "open a new scope", "acquire a lifetime" ⟫
  | addFinalizer (scope : Handle "Scope.Closeable") (key : Nat) : Bool
      ⟪ "register a finalizer under a key", "true when it was registered, false when the scope had closed and it ran now" ⟫
  | remove (scope : Handle "Scope.Closeable") (key : Nat) : Unit
      ⟪ "unregister the finalizer under a key" ⟫
  | close (scope : Handle "Scope.Closeable") : List Nat
      ⟪ "close the scope", "the keys the close ran, in order" ⟫
  | makeWith (strategy : Nat) : Handle "Scope.Closeable"
      ⟪ "open a new scope with the finalizer strategy", "0 sequential, 1 parallel" ⟫
  | fork (parent : Handle "Scope.Closeable") (strategy : Nat) : Handle "Scope.Closeable"
      ⟪ "fork a child scope", "one shared key links the two" ⟫
  | addFinalizerExit (scope : Handle "Scope.Closeable") (key : Nat) : Bool
      ⟪ "register a finalizer that receives the closing exit" ⟫
  | closeExit (scope : Handle "Scope.Closeable") (exit : Except Nat Nat) : List Nat
      ⟪ "close the scope with an exit", "the keys the close ran, in order" ⟫
  | isClosed (scope : Handle "Scope.Closeable") : Bool ⟪ "has the scope closed" ⟫
  | closedWith (scope : Handle "Scope.Closeable") : Option Bool
      ⟪ "none while open", "whether the closing exit succeeded" ⟫
  | provide (scope : Handle "Scope.Closeable") (key : Nat) : Bool
      ⟪ "run with the scope in context and do not close it", "true when it is still open" ⟫
  | use (scope : Handle "Scope.Closeable") (key : Nat) : List Nat
      ⟪ "run with the scope in context and close it on exit", "the keys the close ran" ⟫
  | forkIn (scope : Handle "Scope.Closeable") (fiber : Nat) : Bool
      ⟪ "link a fiber to the scope", "false when the scope had closed and the fiber was interrupted now" ⟫
  | runIn (scope : Handle "Scope.Closeable") (fiber : Nat) : Bool
      ⟪ "link an existing fiber to the scope, with no self-interrupt guard" ⟫
  | linked (scope : Handle "Scope.Closeable") : List Nat
      ⟪ "the fibers linked to the scope, in link order" ⟫
  | exitFiber (scope : Handle "Scope.Closeable") (fiber : Nat) : Unit
      ⟪ "the exited fiber's observer removes its key from the scope" ⟫

/-- The strategy a request names: rc.112's optional argument defaults to
`"sequential"` (`internal/effect.ts:3915`). -/
def strategyOf : Nat → FinalizerStrategy
  | 0 => FinalizerStrategy.sequential
  | _ => FinalizerStrategy.parallel

/-- The exit a `closeExit` request names. -/
def exitOf : Except Nat Nat → ScopeExit
  | .ok _ => Exit.void
  | .error error => Exit.failure (Cause.fail error)

/-! ## The handler, as the projection of the store -/

/-- The Lean handler: `ScopeStore` and nothing else. -/
def scopesLive : Scopes.Service (StateT ScopeStore Id) := fun name =>
  match name with
  | .make => fun _ => do
      let store ← get
      let (handle, store') := store.make FinalizerStrategy.sequential
      set store'
      pure handle
  | .makeWith => fun strategy => do
      let store ← get
      let (handle, store') := store.make (strategyOf strategy)
      set store'
      pure handle
  | .fork => fun (parent, strategy) => do
      let store ← get
      let (handle, store') := store.forkChild parent (strategyOf strategy)
      set store'
      pure handle
  | .addFinalizer => fun (handle, key) => do
      let store ← get
      let (store', answer) := store.addFinalizer handle key (FinName.release key)
      set store'
      pure answer
  | .addFinalizerExit => fun (handle, key) => do
      let store ← get
      let (store', answer) := store.addFinalizer handle key (FinName.release key)
      set store'
      pure answer
  | .remove => fun (handle, key) => do
      modify fun store => store.removeFinalizer handle key
  | .close => fun handle => do
      let store ← get
      let order := store.closeOrderOf handle
      set (store.close handle Exit.void)
      pure order
  | .closeExit => fun (handle, exit) => do
      let store ← get
      let order := store.closeOrderOf handle
      set (store.close handle (exitOf exit))
      pure order
  | .isClosed => fun handle => do
      let store ← get
      pure (((store.scopeAt handle).map Effect4.Scope.isClosed).getD false)
  | .closedWith => fun handle => do
      let store ← get
      pure (((store.scopeAt handle).bind Effect4.Scope.closingExit?).map Exit.isSuccess)
  | .provide => fun (handle, key) => do
      let store ← get
      let (store', _) := store.addFinalizer handle key (FinName.release key)
      set store'
      pure (!((store'.scopeAt handle).map Effect4.Scope.isClosed).getD false)
  | .use => fun (handle, key) => do
      let store ← get
      let (registered, _) := store.addFinalizer handle key (FinName.release key)
      let order := registered.closeOrderOf handle
      set (registered.close handle Exit.void)
      pure order
  | .forkIn => fun (handle, fiber) => do
      let store ← get
      let (store', answer) := store.linkFiber handle fiber true
      set store'
      pure answer
  | .runIn => fun (handle, fiber) => do
      let store ← get
      let (store', answer) := store.linkFiber handle fiber false
      set store'
      pure answer
  | .linked => fun handle => do
      let store ← get
      pure (store.linkedTo handle)
  | .exitFiber => fun (handle, fiber) => do
      modify fun store => store.dropLink handle fiber

/-! ### The clauses the store makes statable -/

/-- `scope.fork-linkage`: a fork registers exactly the two names rc.112
registers, under one shared key — the parent closes the child, the child
detaches from the parent (`internal/effect.ts:3834-3844`). This is the open
half of `SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`), closed.
census: scope.fork-linkage -/
theorem fork_registers_the_linkage_names (store : ScopeStore) (parent : ScopeHandle)
    (strategy : FinalizerStrategy) (parentScope : ScopeCarrier)
    (h : store.scopeAt parent = Option.some parentScope) (hopen : parentScope.closingExit? = none) :
    (store.forkChild parent strategy).2.scopes =
      ((store.setScope parent
          (parentScope.addUnsafe store.nextKey
            (FinName.closeChildScope store.nextKey store.scopes.length))).scopes) ++
        [(Effect4.Scope.make strategy : ScopeCarrier).addUnsafe store.nextKey
          (FinName.detachFromParent store.nextKey parent.index)] := by
  simp [ScopeStore.forkChild, Effect4.Scope.fork, h, hopen]

/-- A parent scope and the child forked out of it. -/
def forkedPair : ScopeStore :=
  ((({} : ScopeStore).make FinalizerStrategy.sequential).2.forkChild
    ⟨0⟩ FinalizerStrategy.sequential).2

/-- `scope.fork-linkage`: closing the parent closes the child scope its order
names, so `closeChildScope` *means* `scopeClose(child, exit)` in this store and
not only on paper. census: scope.fork-linkage -/
theorem close_cascades_to_the_child :
    (forkedPair.close ⟨0⟩ Exit.void).scopes.map Effect4.Scope.isClosed = [true, true] := by
  decide

/-- `scope.close-state-first`: the parent's own close is written before any
finalizer runs, and the child's close is a *consequence* of the order, not of
the answer. The parent is closed whatever the cascade does.
census: scope.close-state-first -/
theorem close_writes_the_parent_state_first :
    ((forkedPair.close ⟨0⟩ Exit.void).scopeAt ⟨0⟩).map Effect4.Scope.state =
      ((forkedPair.scopeAt ⟨0⟩).map
        (fun scope => (Effect4.Scope.closeState scope (Exit.void : ScopeExit)).state)) := by
  decide

/-- `close` answers this scope's own keys in run order: the materialised
registration list, backwards (`internal/effect.ts:3815`).
census: scope.close-sequential -/
theorem closeOrder_is_the_keys (store : ScopeStore) (handle : ScopeHandle)
    (scope : ScopeCarrier) (h : store.scopeAt handle = Option.some scope) :
    store.closeOrderOf handle = scope.closeOrder.map FinName.key := by
  simp [ScopeStore.closeOrderOf, h]

/-- `forkIn` on a closed scope links nothing and answers `false`: rc.112
interrupts the child at once instead of registering it
(`internal/effect.ts:5374`). census: scope.fork-linkage -/
theorem linkFiber_closed_scope (store : ScopeStore) (handle : ScopeHandle) (fiber : Nat)
    (skipSelf : Bool) (scope : ScopeCarrier) (h : store.scopeAt handle = Option.some scope)
    (hclosed : scope.isClosed = true) :
    store.linkFiber handle fiber skipSelf = (store, false) := by
  simp [ScopeStore.linkFiber, h, hclosed]

/-- `forkIn` and `fiberRunIn` register the same name at different guards: the
fork guards against the interruptor being the fiber itself (`:5368-5372`) and
`fiberRunIn` does not (`:5455`). census: scope.fork-linkage -/
theorem linkFiber_names (store : ScopeStore) (handle : ScopeHandle) (fiber : Nat)
    (skipSelf : Bool) (scope : ScopeCarrier) (h : store.scopeAt handle = Option.some scope)
    (hopen : scope.isClosed = false) :
    (store.linkFiber handle fiber skipSelf).1.scopes =
      (store.setScope handle
        (Effect4.Scope.addExit scopeRun scope store.nextKey
          (FinName.interruptFiber store.nextKey fiber skipSelf)).1).scopes := by
  simp [ScopeStore.linkFiber, ScopeStore.setScope, h, hopen]

/-! ## The programs

The first four are the corpus the goldens under `generated/traces/scope/` were
generated from; their rows are unchanged.

The one pure atom the scope scripts call: a typed-failure exit for
`closeExit`, since the DSL's pure fragment has no `Result` former. -/

effect_atoms ScopeAtoms where
  | errorOf (error : Nat) : Except Nat Nat ⟪ "Result.fail(error)" ⟫ := (Except.error error)

-- Three finalizers, closed once: the keys come back last registered first.
effect_program scopeLifo (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.addFinalizer(s, 3)
  let r ← Scopes.close(s)
  return r

-- Registering on a closed scope runs the finalizer now and answers `false`.
effect_program scopeAddAfterClosed (n : Nat) over Scopes : Bool :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.close(s)
  let a ← Scopes.addFinalizer(s, 2)
  return a

-- A removed key does not run.
effect_program scopeRemove (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.remove(s, 1)
  let r ← Scopes.close(s)
  return r

-- The second close runs nothing and answers the empty order.
effect_program scopeCloseTwice (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.close(s)
  let r ← Scopes.close(s)
  return r

-- A fork registers one shared key on the parent, and closing the parent closes
-- the child: `isClosed` of the child is the cascade, not a longer answer.
effect_program scopeForkLinkage (n : Nat) over Scopes : Bool :=
  let parent ← Scopes.make()
  let child ← Scopes.fork(parent, 0)
  let _ ← Scopes.addFinalizer(child, 1)
  let _ ← Scopes.close(parent)
  let closed ← Scopes.isClosed(child)
  return closed

-- `provide` leaves the scope open; `use` closes it. Same registration, two
-- lifetimes.
effect_program scopeProvideThenUse (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.provide(s, 1)
  let r ← Scopes.use(s, 2)
  return r

-- A closed scope refuses the link and rc.112 interrupts the fiber at once.
effect_program scopeForkInClosed (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.forkIn(s, 1)
  let _ ← Scopes.runIn(s, 2)
  let _ ← Scopes.exitFiber(s, 1)
  let live ← Scopes.linked(s)
  return live

-- A close with a typed failure exit: the order is the same, and `closedWith`
-- says the exit failed.
effect_program scopeCloseWithExit (n : Nat) over Scopes : Option Bool :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizerExit(s, 1)
  let _ ← Scopes.closeExit(s, errorOf n)
  let state ← Scopes.closedWith(s)
  return state

example : ((interpret scopesLive.toHandler (scopeLifo 0)).run {} : List Nat × ScopeStore).1
    = [3, 2, 1] := rfl
example : ((interpret scopesLive.toHandler (scopeAddAfterClosed 0)).run {} : Bool × ScopeStore).1
    = false := rfl
example : ((interpret scopesLive.toHandler (scopeRemove 0)).run {} : List Nat × ScopeStore).1
    = [2] := rfl
example : ((interpret scopesLive.toHandler (scopeCloseTwice 0)).run {} : List Nat × ScopeStore).1
    = [] := rfl
example : ((interpret scopesLive.toHandler (scopeForkLinkage 0)).run {} : Bool × ScopeStore).1
    = true := rfl
example : ((interpret scopesLive.toHandler (scopeForkInClosed 0)).run {} : List Nat × ScopeStore).1
    = [2] := rfl

/-- The traced run of a scope program, with its outcome appended. -/
def scopeGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program Scopes.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × ScopeStore :=
    ((interpret (Scopes.traced scopesLive).toHandler program).run []).run {}
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

/-- One scope program: its script and its golden log. -/
structure ScopeEntry where
  name : String
  script : Script
  log : Effect4.Trace.Log

def scopePrograms : List ScopeEntry :=
  [ { name := "lifo", script := scopeLifo.script, log := scopeGoldenLog (scopeLifo 0) }
  , { name := "addAfterClosed", script := scopeAddAfterClosed.script,
      log := scopeGoldenLog (scopeAddAfterClosed 0) }
  , { name := "remove", script := scopeRemove.script, log := scopeGoldenLog (scopeRemove 0) }
  , { name := "closeTwice", script := scopeCloseTwice.script,
      log := scopeGoldenLog (scopeCloseTwice 0) }
  , { name := "forkLinkage", script := scopeForkLinkage.script,
      log := scopeGoldenLog (scopeForkLinkage 0) }
  , { name := "provideThenUse", script := scopeProvideThenUse.script,
      log := scopeGoldenLog (scopeProvideThenUse 0) }
  , { name := "forkInClosed", script := scopeForkInClosed.script,
      log := scopeGoldenLog (scopeForkInClosed 0) }
  , { name := "closeWithExit", script := scopeCloseWithExit.script,
      log := scopeGoldenLog (scopeCloseWithExit 4) } ]

/-- The pure atoms the scope scripts call. -/
def scopeAtomNames : List String := ["errorOf"]

end Effect4.ScopeFamily
