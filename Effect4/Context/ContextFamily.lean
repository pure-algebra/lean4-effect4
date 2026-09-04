import Effect4.Meta.Derive
import Effect4.Context.Key

/-!
# Context.ContextFamily

`Contexts`: a traced family over rc.112's `Context` and the `Reference`
defaults the runtime reads off it, with the Lean handler that is a store of
**`Effect4.ServiceKey`-keyed bindings**.

## Keys are `Effect4.ServiceKey`, and that is the point

`Effect4/Context/Key.lean` owns the first-order key: a `ServiceName` paired
with a `ServiceTypeCode`, both `Nat` carriers, whose *identity is the pair*
(`ServiceKey`, and `ServiceKey.Conflict` for two keys that share a name and
differ in code). Its own docstring records that "Effect's `Context.Tag`
identity is the tag string alone and cannot express the colliding pair, so no
compatibility with it is claimed here".

This family is where that claim gets a wire. A key crosses as
`Handle "Context.Key<never, number>"` — an index into the store's key table —
and the store binds values by the `ServiceKey` the index names, never by the
index. Two `key` operations with the same name and code therefore answer two
handles that read the same binding, and two with the same name and different
codes do not: `keyConflict` is `ServiceKey.Conflict` on the wire.

## The rows

| row | rc.112 |
| --- | --- |
| `empty` | `Context.empty()` (`Layer.ts:1155` uses it) |
| `key` | a `Context.Service`/`Context.Reference` tag |
| `referenceKey` | the four `Reference`s the runtime reads |
| `make` | `Context.make(key, value)` |
| `add` | `Context.add` (`Layer.ts:762` uses it) |
| `get` | `Context.getUnsafe` (`Layer.ts:806`), which throws when missing |
| `getOption` | `Context.getOrUndefined` (`Layer.ts:586`) |
| `merge` | `Context.merge` (`Layer.ts:2797-2805` uses it) |
| `pick` | `Context.pick` |
| `omit` | `Context.omit` |
| `provideContext` | `internal/effect.ts:2180` |
| `updateContext` | `internal/effect.ts:2073` |
| `withContext` | `internal/effect.ts:2152-2153` (`Effect.context`) |
| `keyConflict` | `Effect4.ServiceKey.Conflict` |
| `maxOpsBeforeYield` | `Scheduler.ts:269-272`, default `2048` |
| `preventSchedulerYield` | `Scheduler.ts:295-298`, default `false` |
| `currentMemoMap` | `Layer.ts:584-588` |
| `currentScope` | `Scope.ts:215`, `internal/effect.ts:3772` |

## The ambient context

`provideContext`, `updateContext` and `withContext` are about the *fiber's*
context, which rc.112 keeps on the fiber and `withFiber` reads
(`internal/effect.ts:726-727`). This family keeps one ambient handle, created
empty on first use, and `provideContext`/`updateContext` answer the context
they replaced — which is what makes the restore observable at all: rc.112's
`provideContext` restores the previous context when the inner effect finishes,
and a family whose operations are points cannot see the restore, only the two
contexts.

## Refusals

- **A `Reference`'s default is a Lean function on the host**
  (`defaultValue: () => 2048`, `Scheduler.ts:271`). DB-02 keeps functions out of
  canonical content, so the defaults are *values* here: `2048` and `false`, read
  off the pinned source and written down. A reference whose default is an
  object — `CurrentMemoMap`, `Scope` — has no value to write down, so those two
  rows answer `Option` and are `none` until something binds them, which is
  `Context.getOrUndefined`'s own answer (`Layer.ts:586`).
- **A context value is a number.** rc.112 stores arbitrary service objects; the
  answer profile spells a number, and `servicesOf`-style identity questions
  belong to the `Layers` family, which names services by handles.
- **`provideContext`'s restore is not an operation.** The row answers the
  replaced context, and the *scoping* — that the previous context comes back
  when the provided effect finishes — is a frame fact, not a service call.
  counterexample: owed, see the report.
-/

set_option linter.unusedVariables false

namespace Effect4.ContextFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-- A context key. The Lean carrier is an index into the store's key table; the
`ServiceKey` it names is what a binding is keyed by. -/
abbrev KeyHandle := Handle "Context.Key<never, number>"

/-- A context. -/
abbrev ContextHandle := Handle "Context.Context<never>"

/-! ## The signature -/

effect_signature Contexts where
  | empty : Handle "Context.Context<never>" ⟪ "the empty context" ⟫
  | key (name : Nat) (service : Nat) : Handle "Context.Key<never, number>"
      ⟪ "a key", "its identity is the name and the type code together" ⟫
  | referenceKey (reference : Nat) : Handle "Context.Key<never, number>"
      ⟪ "one of the runtime's own references",
        "0 MaxOpsBeforeYield, 1 PreventSchedulerYield, 2 CurrentMemoMap, 3 Scope" ⟫
  | make (key : Handle "Context.Key<never, number>") (value : Nat)
      : Handle "Context.Context<never>"
      ⟪ "a context holding one binding" ⟫
  | add (context : Handle "Context.Context<never>") (key : Handle "Context.Key<never, number>")
      (value : Nat) : Handle "Context.Context<never>"
      ⟪ "the context with one more binding", "a later add wins" ⟫
  | get (context : Handle "Context.Context<never>") (key : Handle "Context.Key<never, number>")
      : Nat !! Nat
      ⟪ "the bound value", "throws when the key is missing" ⟫
  | getOption (context : Handle "Context.Context<never>")
      (key : Handle "Context.Key<never, number>") : Option Nat
      ⟪ "the bound value, or none" ⟫
  | merge (left : Handle "Context.Context<never>") (right : Handle "Context.Context<never>")
      : Handle "Context.Context<never>" ⟪ "both, the right winning a shared key" ⟫
  | pick (context : Handle "Context.Context<never>") (key : Handle "Context.Key<never, number>")
      : Handle "Context.Context<never>" ⟪ "only this key's binding" ⟫
  | «omit» (context : Handle "Context.Context<never>") (key : Handle "Context.Key<never, number>")
      : Handle "Context.Context<never>" ⟪ "everything but this key's binding" ⟫
  | provideContext (context : Handle "Context.Context<never>")
      : Handle "Context.Context<never>"
      ⟪ "make this the fiber's context", "the context it replaced" ⟫
  | updateContext (key : Handle "Context.Key<never, number>") (value : Nat)
      : Handle "Context.Context<never>"
      ⟪ "bind a key in the fiber's context", "the context it replaced" ⟫
  | withContext : Handle "Context.Context<never>" ⟪ "the fiber's context" ⟫
  | keyConflict (left : Handle "Context.Key<never, number>")
      (right : Handle "Context.Key<never, number>") : Bool
      ⟪ "do the two keys share a name and differ in type code" ⟫
  | maxOpsBeforeYield : Nat ⟪ "the operation budget between yields", "2048 by default" ⟫
  | preventSchedulerYield : Bool ⟪ "whether the yield check is bypassed", "false by default" ⟫
  | currentMemoMap : Option (Handle "Layer.MemoMap")
      ⟪ "the memo map in the fiber's context, if any" ⟫
  | currentScope : Option (Handle "Scope.Closeable")
      ⟪ "the scope in the fiber's context, if any" ⟫

/-! ## The store -/

/-- The four `Reference`s the runtime reads off a context, in the order
`referenceKey` names them. -/
inductive Reference
  /-- `Scheduler.MaxOpsBeforeYield` (`Scheduler.ts:269-272`). -/
  | maxOpsBeforeYield
  /-- `Scheduler.PreventSchedulerYield` (`Scheduler.ts:295-298`). -/
  | preventSchedulerYield
  /-- `Layer.CurrentMemoMap` (`Layer.ts:584-588`). -/
  | currentMemoMap
  /-- `Scope.Scope` (`Scope.ts:215`, `internal/effect.ts:3772`). -/
  | scope
deriving DecidableEq, Repr, Inhabited

namespace Reference

/-- The reference a numbered request names; anything past the table reads as
the scheduler budget, which is a frontier of the *name* alphabet. -/
def ofIndex : Nat → Reference
  | 0 => .maxOpsBeforeYield
  | 1 => .preventSchedulerYield
  | 2 => .currentMemoMap
  | _ => .scope

/-- The service name a reference reserves. The four take the first four names,
so a key a program mints is offset past them: rc.112's tags are strings like
`effect/Scheduler/MaxOpsBeforeYield` and cannot collide with a user tag, and
the offset is this alphabet's stand-in for that. -/
def name : Reference → Nat
  | .maxOpsBeforeYield => 0
  | .preventSchedulerYield => 1
  | .currentMemoMap => 2
  | .scope => 3

/-- The key a reference is read under. -/
def serviceKey (reference : Reference) : ServiceKey := ⟨⟨reference.name⟩, ⟨0⟩⟩

end Reference

/-- How many names the references reserve. -/
def referenceCount : Nat := 4

/-- The key a `key` request mints: the program's name, offset past the
references, paired with the type code it gave. -/
def mintedKey (name service : Nat) : ServiceKey := ⟨⟨name + referenceCount⟩, ⟨service⟩⟩

/-- The store: the key table, the contexts, the fiber's context, and one handle
counter shared by keys and contexts, as `handleIndex` is on the host. -/
structure ContextStore where
  /-- key handle → the `ServiceKey` it names -/
  keys : List (Nat × ServiceKey) := []
  /-- context handle → its bindings, in insertion order -/
  contexts : List (Nat × List (ServiceKey × Nat)) := []
  /-- the fiber's context, created empty on first use -/
  ambient : Option Nat := Option.none
  /-- the next handle index -/
  next : Nat := 0
deriving Repr, Inhabited

namespace ContextStore

/-- The `ServiceKey` a handle names; an unminted handle is a frontier read as
the zero key. -/
def keyOf (self : ContextStore) (handle : KeyHandle) : ServiceKey :=
  ((self.keys.find? (·.1 == handle.index)).map (·.2)).getD ⟨⟨0⟩, ⟨0⟩⟩

/-- The bindings a context handle names. -/
def bindingsOf (self : ContextStore) (handle : ContextHandle) : List (ServiceKey × Nat) :=
  ((self.contexts.find? (·.1 == handle.index)).map (·.2)).getD []

/-- Bind a key in a binding list, a later `add` replacing an earlier one in
place. -/
def bind (bindings : List (ServiceKey × Nat)) (key : ServiceKey) (value : Nat) :
    List (ServiceKey × Nat) :=
  if bindings.any (·.1 == key) then
    bindings.map (fun entry => if entry.1 == key then (key, value) else entry)
  else bindings ++ [(key, value)]

/-- The value bound to a key, if any. `Context.getOrUndefined`. -/
def lookup (bindings : List (ServiceKey × Nat)) (key : ServiceKey) : Option Nat :=
  (bindings.find? (·.1 == key)).map (·.2)

/-- Allocate a key handle for a `ServiceKey`. A key already in the table keeps
its handle, so two `key` calls with the same name and code answer the same
index — which is what makes key identity the *pair* and not the call. -/
def declareKey (self : ContextStore) (key : ServiceKey) : KeyHandle × ContextStore :=
  match self.keys.find? (·.2 == key) with
  | Option.some entry => (⟨entry.1⟩, self)
  | Option.none =>
      (⟨self.next⟩, { self with keys := self.keys ++ [(self.next, key)], next := self.next + 1 })

/-- Allocate a context handle for a binding list. -/
def declareContext (self : ContextStore) (bindings : List (ServiceKey × Nat)) :
    ContextHandle × ContextStore :=
  (⟨self.next⟩,
    { self with contexts := self.contexts ++ [(self.next, bindings)], next := self.next + 1 })

/-- The fiber's context, created empty on first use. -/
def ambientContext (self : ContextStore) : ContextHandle × ContextStore :=
  match self.ambient with
  | Option.some handle => (⟨handle⟩, self)
  | Option.none =>
      let (handle, allocated) := self.declareContext []
      (handle, { allocated with ambient := Option.some handle.index })

/-- The value a reference reads off the fiber's context, or nothing. -/
def referenceValue (self : ContextStore) (reference : Reference) : Option Nat :=
  match self.ambient with
  | Option.none => Option.none
  | Option.some handle => lookup (self.bindingsOf ⟨handle⟩) reference.serviceKey

end ContextStore

/-! ## The handler -/

/-- The monad the handler runs in: `get` aborts with the key it could not find
(`Context.getUnsafe` throws), over the store. One aborting row makes the whole
handler `ExceptT`, which is what `effect_signature`'s `!! E` reading asks for. -/
abbrev ContextM := ExceptT Nat (StateT ContextStore Id)

/-- The Lean handler: the key table, the contexts, and the fiber's context. -/
def contextsLive : Contexts.Service ContextM := fun name =>
  match name with
  | .empty => fun _ => do
      let store ← get
      let (handle, store') := store.declareContext []
      set store'; pure handle
  | .key => fun (name, service) => do
      let store ← get
      let (handle, store') := store.declareKey (mintedKey name service)
      set store'; pure handle
  | .referenceKey => fun reference => do
      let store ← get
      let (handle, store') := store.declareKey (Reference.ofIndex reference).serviceKey
      set store'; pure handle
  | .make => fun (key, value) => do
      let store ← get
      let (handle, store') := store.declareContext [(store.keyOf key, value)]
      set store'; pure handle
  | .add => fun (context, key, value) => do
      let store ← get
      let (handle, store') :=
        store.declareContext (ContextStore.bind (store.bindingsOf context) (store.keyOf key) value)
      set store'; pure handle
  | .get => fun (context, key) => do
      let store ← get
      match ContextStore.lookup (store.bindingsOf context) (store.keyOf key) with
      | Option.some value => pure value
      | Option.none => throw key.index
  | .getOption => fun (context, key) => do
      let store ← get
      pure (ContextStore.lookup (store.bindingsOf context) (store.keyOf key))
  | .merge => fun (left, right) => do
      let store ← get
      let merged :=
        (store.bindingsOf right).foldl
          (fun current entry => ContextStore.bind current entry.1 entry.2)
          (store.bindingsOf left)
      let (handle, store') := store.declareContext merged
      set store'; pure handle
  | .pick => fun (context, key) => do
      let store ← get
      let picked := (store.bindingsOf context).filter (·.1 == store.keyOf key)
      let (handle, store') := store.declareContext picked
      set store'; pure handle
  | .«omit» => fun (context, key) => do
      let store ← get
      let kept := (store.bindingsOf context).filter (fun entry => !(entry.1 == store.keyOf key))
      let (handle, store') := store.declareContext kept
      set store'; pure handle
  | .provideContext => fun context => do
      let store ← get
      let (previous, withAmbient) := store.ambientContext
      set { withAmbient with ambient := Option.some context.index }
      pure previous
  | .updateContext => fun (key, value) => do
      let store ← get
      let (previous, withAmbient) := store.ambientContext
      let (handle, store') :=
        withAmbient.declareContext
          (ContextStore.bind (withAmbient.bindingsOf previous) (withAmbient.keyOf key) value)
      set { store' with ambient := Option.some handle.index }
      pure previous
  | .withContext => fun _ => do
      let store ← get
      let (handle, store') := store.ambientContext
      set store'; pure handle
  | .keyConflict => fun (left, right) => do
      let store ← get
      pure (decide (ServiceKey.Conflict (store.keyOf left) (store.keyOf right)))
  | .maxOpsBeforeYield => fun _ => do
      let store ← get
      pure ((store.referenceValue .maxOpsBeforeYield).getD 2048)
  | .preventSchedulerYield => fun _ => do
      let store ← get
      pure (((store.referenceValue .preventSchedulerYield).getD 0) != 0)
  | .currentMemoMap => fun _ => do
      let store ← get
      pure ((store.referenceValue .currentMemoMap).map fun handle => ⟨handle⟩)
  | .currentScope => fun _ => do
      let store ← get
      pure ((store.referenceValue .scope).map fun handle => ⟨handle⟩)

/-! ### The clauses -/

/-- A key's identity is the pair, so two `key` requests with the same name and
the same code answer the same handle and read the same binding. -/
theorem declareKey_is_by_the_pair (store : ContextStore) (name service : Nat) :
    (store.declareKey (mintedKey name service)).1 =
      ((store.declareKey (mintedKey name service)).2.declareKey (mintedKey name service)).1 := by
  cases h : store.keys.find? (·.2 == mintedKey name service) with
  | some entry => simp [ContextStore.declareKey, h]
  | none => simp [ContextStore.declareKey, h]

/-- Two keys that share a name and differ in type code are in conflict, and no
binding of one is a binding of the other. -/
theorem minted_keys_conflict (name left right : Nat) (h : left ≠ right) :
    ServiceKey.Conflict (mintedKey name left) (mintedKey name right) :=
  ⟨rfl, fun contra => h (congrArg ServiceTypeCode.value contra)⟩

/-- `add` binds in place, so a later `add` of the same key wins. -/
theorem bind_replaces_in_place (key : ServiceKey) (first second : Nat) :
    ContextStore.bind (ContextStore.bind [] key first) key second = [(key, second)] := by
  simp [ContextStore.bind]

/-- A binding is read back by the key that made it. -/
theorem lookup_bind_self (key : ServiceKey) (value : Nat) :
    ContextStore.lookup (ContextStore.bind [] key value) key = Option.some value := by
  simp [ContextStore.bind, ContextStore.lookup]

/-- A key that is not bound reads as nothing, which is `Context.getOrUndefined`. -/
theorem lookup_other (key other : ServiceKey) (value : Nat) (h : other ≠ key) :
    ContextStore.lookup (ContextStore.bind [] key value) other = Option.none := by
  simp [ContextStore.bind, ContextStore.lookup, Ne.symm h]

/-- `MaxOpsBeforeYield` answers rc.112's own default until something binds it
(`Scheduler.ts:271`). -/
theorem maxOps_default (store : ContextStore) (h : store.ambient = Option.none) :
    (store.referenceValue .maxOpsBeforeYield).getD 2048 = 2048 := by
  simp [ContextStore.referenceValue, h]

/-- `PreventSchedulerYield` answers `false` until something binds it
(`Scheduler.ts:297`). -/
theorem preventYield_default (store : ContextStore) (h : store.ambient = Option.none) :
    (((store.referenceValue .preventSchedulerYield).getD 0) != 0) = false := by
  simp [ContextStore.referenceValue, h]

/-- `CurrentMemoMap` and `Scope` have no writable default: `getOrUndefined`
answers nothing until a build or a `scoped` binds them (`Layer.ts:586`). -/
theorem objectReferences_have_no_default (store : ContextStore) (h : store.ambient = Option.none) :
    store.referenceValue .currentMemoMap = Option.none ∧
      store.referenceValue .scope = Option.none := by
  constructor <;> simp [ContextStore.referenceValue, h]

/-! ## The programs -/

-- A key, a binding, and the read that finds it.
effect_program contextAddGet (n : Nat) over Contexts : Nat :=
  let c ← Contexts.empty()
  let k ← Contexts.key(0, 0)
  let c2 ← Contexts.add(c, k, n)
  let v ← Contexts.get(c2, k)
  return v

-- A missing key aborts: `Context.getUnsafe` throws, and the error channel is
-- the key that was not there.
effect_program contextGetMissing (n : Nat) over Contexts : Nat :=
  let c ← Contexts.empty()
  let k ← Contexts.key(0, 0)
  let v ← Contexts.get(c, k)
  return v

-- The same name at two type codes is two keys: `keyConflict` says so, and the
-- binding under one is invisible under the other.
effect_program contextKeyConflict (n : Nat) over Contexts : Option Nat :=
  let a ← Contexts.key(0, 0)
  let b ← Contexts.key(0, 1)
  let _ ← Contexts.keyConflict(a, b)
  let c ← Contexts.make(a, n)
  let v ← Contexts.getOption(c, b)
  return v

-- `merge` lets the right win a shared key; `pick` and `omit` are the two
-- halves of a key's binding.
effect_program contextMergePickOmit (n : Nat) over Contexts : Option Nat :=
  let k ← Contexts.key(0, 0)
  let left ← Contexts.make(k, n)
  let right ← Contexts.make(k, 9)
  let m ← Contexts.merge(left, right)
  let picked ← Contexts.pick(m, k)
  let dropped ← Contexts.«omit»(picked, k)
  let v ← Contexts.getOption(dropped, k)
  return v

-- `provideContext` answers the context it replaced, and `withContext` answers
-- the one it installed.
effect_program contextProvideThenRead (n : Nat) over Contexts : Option Nat :=
  let k ← Contexts.key(0, 0)
  let c ← Contexts.make(k, n)
  let _ ← Contexts.provideContext(c)
  let now ← Contexts.withContext()
  let v ← Contexts.getOption(now, k)
  return v

-- The reference defaults, read off a context that binds neither.
effect_program contextReferenceDefaults (n : Nat) over Contexts : Nat :=
  let _ ← Contexts.preventSchedulerYield()
  let ops ← Contexts.maxOpsBeforeYield()
  return ops

-- `updateContext` binds a reference in the fiber's context, and the read after
-- it answers the bound value instead of the default.
effect_program contextUpdateReference (n : Nat) over Contexts : Nat :=
  let k ← Contexts.referenceKey(0)
  let _ ← Contexts.updateContext(k, n)
  let ops ← Contexts.maxOpsBeforeYield()
  return ops

-- `CurrentMemoMap` is absent until something binds it.
effect_program contextMemoMapAbsent (n : Nat) over Contexts : Option (Handle "Layer.MemoMap") :=
  let _ ← Contexts.withContext()
  let m ← Contexts.currentMemoMap()
  return m

/-! ## Golden logs -/

/-- The traced run of a context program from the empty store, with its outcome
appended. -/
def contextGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program Contexts.Sig α) :
    Effect4.Trace.Log :=
  let result : (Except Nat α × Effect4.Trace.Log) × ContextStore :=
    ((interpret (Contexts.tracedExcept contextsLive).toHandler program).run.run []).run {}
  result.1.2 ++ [.done (match result.1.1 with
    | .ok value => .success (Effects.Trace.ToVal.toVal value)
    | .error error => .failure (.nat error))]

/-- One context program: its script and its golden log. -/
structure ContextEntry where
  name : String
  script : Script
  log : Effect4.Trace.Log

def contextEntry {α : Type} [Effects.Trace.ToVal α] (name : String) (script : Script)
    (program : Program Contexts.Sig α) : ContextEntry :=
  { name := name, script := script, log := contextGoldenLog program }

def contextPrograms : List ContextEntry :=
  [ contextEntry "addGet" contextAddGet.script (contextAddGet 7)
  , contextEntry "getMissing" contextGetMissing.script (contextGetMissing 7)
  , contextEntry "keyConflict" contextKeyConflict.script (contextKeyConflict 7)
  , contextEntry "mergePickOmit" contextMergePickOmit.script (contextMergePickOmit 7)
  , contextEntry "provideThenRead" contextProvideThenRead.script (contextProvideThenRead 7)
  , contextEntry "referenceDefaults" contextReferenceDefaults.script (contextReferenceDefaults 0)
  , contextEntry "updateReference" contextUpdateReference.script (contextUpdateReference 3)
  , contextEntry "memoMapAbsent" contextMemoMapAbsent.script (contextMemoMapAbsent 0) ]

end Effect4.ContextFamily
