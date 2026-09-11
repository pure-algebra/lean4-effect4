import Effect4.Machine.Key
import Effect4.Machine.Value

/-!
# Machine.ContextMap — the service map, its keys and its codec

rc.112's `Context` (`Context.ts`) as pure first-order data: the insertion-ordered map with
unique keys, its operations and laws (the M4b half of `Machine/Context.lean`, moved here in the
join — `docs/research/2026-09-07-join-dispatch.md` §2, dependency cut L9 — a move, not a
rewrite), the machine's constant universe `ValU` over the shared carrier, `Ctx := Context ValU`,
the four reserved keys, the budget references, the hooks the fiber machine reads off a context
(`ambientScope`, `budgetOf`), and the spine codec (`encode`/`decode`: `Value.serviceContext`
over `pair key value` entries) with its exactness, so the map is an `Image` of the carrier
(`contextImage`). Imports only the key and value foundations: `Machine/Stores.lean` holds one
inside the fiber context without inheriting `Effects.Algebra.Program`. `Machine/Context.lean`
imports this module — every name keeps its namespace, so its readers are unchanged — and adds
the requirement rows, the service programs, the alphabets and the counterexamples.
-/

set_option autoImplicit false

namespace Effect4.Machine.Env

open Effect4
open Effect4.Store (Image)

universe u

/-! ## `Context/Service` (L1, fence F-SVC): a key bound to a value of its carrier -/

/-- A service: a key and a value of the key's carrier under `U`. -/
structure Service (U : ServiceUniverse.{u}) : Type u where
  /-- The identity, a nominal name paired with a first-order type code. -/
  key : ServiceKey
  /-- The value, typed by the code through `U` and never by the name. -/
  value : ServiceKey.Carrier U key

/-! ## `Context/Environment` (L2, fence F-ENV): the first-order environment

An insertion-ordered map from `ServiceKey` to values with unique keys, rc.112's `Context` as a
JavaScript `Map` keyed by the tag. The uniqueness invariant is a proof field, as
`Effect4.ReasonAnnotations` (`src/Effect4/Machine/Cause.lean:28-33`) does it, so no operation can
build a duplicate. -/

/-- The environment. -/
structure Context (U : ServiceUniverse.{u}) : Type u where
  /-- The bound services, in insertion order. -/
  entries : List (Service U)
  /-- No key is bound twice. -/
  keysNodup : (entries.map Service.key).Nodup

/-- `Option` right bias: the right operand wins when present. `Context.merge`'s lookup law is
spelled with it. -/
def rightBiased {A : Type u} : Option A → Option A → Option A
  | some value, _ => some value
  | none, fallback => fallback

namespace Context

variable {U : ServiceUniverse.{u}}

/-- `Context.empty()` (`internal/effect.ts:627`, `:5467`, `:5491`). -/
def empty : Context U := ⟨[], List.nodup_nil⟩

/-- Lookup in the entry list: the first entry under the key, transported along the code
equality the key equality yields — `ServiceKey.transport`, never a cast. -/
def lookup (key : ServiceKey) : List (Service U) → Option (ServiceKey.Carrier U key)
  | [] => none
  | s :: rest =>
    if h : s.key = key then
      some (ServiceKey.transport U (congrArg ServiceKey.service h) s.value)
    else lookup key rest

/-- `Context.getOption` / `getOrUndefined` (`Layer.ts:586`): the value under a key, if bound. -/
def get? (self : Context U) (key : ServiceKey) : Option (ServiceKey.Carrier U key) :=
  lookup key self.entries

/-- The bound keys, in insertion order. -/
def keys (self : Context U) : List ServiceKey := self.entries.map Service.key

/-- JavaScript `Map.prototype.set`: an existing key keeps its position and takes the new value; a
new key is appended. The same shape as `Effect4.Scope.tableInsert`. -/
def setEntries (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    List (Service U) → List (Service U)
  | [] => [⟨key, value⟩]
  | s :: rest => if s.key = key then ⟨key, value⟩ :: rest else s :: setEntries key value rest

/-! ### Lookup and set, entry by entry -/

theorem lookup_nil (key : ServiceKey) : lookup (U := U) key [] = none := rfl

/-- A hit at the head. -/
theorem lookup_cons_hit (s : Service U) (key : ServiceKey) (rest : List (Service U))
    (h : s.key = key) :
    lookup key (s :: rest) =
      some (ServiceKey.transport U (congrArg ServiceKey.service h) s.value) := by
  show (if h : s.key = key then
      some (ServiceKey.transport U (congrArg ServiceKey.service h) s.value)
    else lookup key rest) = _
  rw [dif_pos h]

/-- A hit at the head under the key itself: the transport is the identity
(`ServiceKey.transport_rfl`). -/
theorem lookup_cons_same (key : ServiceKey) (value : ServiceKey.Carrier U key)
    (rest : List (Service U)) : lookup key (⟨key, value⟩ :: rest) = some value := by
  show (if h : key = key then
      some (ServiceKey.transport U (congrArg ServiceKey.service h) value)
    else lookup key rest) = some value
  rw [dif_pos rfl]
  rfl

/-- A miss at the head continues. -/
theorem lookup_cons_other (s : Service U) (key : ServiceKey) (rest : List (Service U))
    (hne : s.key ≠ key) : lookup key (s :: rest) = lookup key rest := by
  show (if h : s.key = key then
      some (ServiceKey.transport U (congrArg ServiceKey.service h) s.value)
    else lookup key rest) = lookup key rest
  rw [dif_neg hne]

theorem setEntries_nil (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    setEntries key value [] = [⟨key, value⟩] := rfl

theorem setEntries_cons_same (s : Service U) (key : ServiceKey)
    (value : ServiceKey.Carrier U key) (rest : List (Service U)) (h : s.key = key) :
    setEntries key value (s :: rest) = ⟨key, value⟩ :: rest := by
  show (if s.key = key then ⟨key, value⟩ :: rest else s :: setEntries key value rest) = _
  rw [if_pos h]

theorem setEntries_cons_other (s : Service U) (key : ServiceKey)
    (value : ServiceKey.Carrier U key) (rest : List (Service U)) (h : s.key ≠ key) :
    setEntries key value (s :: rest) = s :: setEntries key value rest := by
  show (if s.key = key then ⟨key, value⟩ :: rest else s :: setEntries key value rest) = _
  rw [if_neg h]

/-- `Map.set` then `Map.get` at the same key answers the new value. -/
theorem lookup_setEntries_same (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    ∀ es : List (Service U), lookup key (setEntries key value es) = some value
  | [] => by
    rw [setEntries_nil]
    exact lookup_cons_same key value []
  | s :: rest => by
    by_cases h : s.key = key
    · rw [setEntries_cons_same s key value rest h]
      exact lookup_cons_same key value rest
    · rw [setEntries_cons_other s key value rest h, lookup_cons_other s key _ h]
      exact lookup_setEntries_same key value rest

/-- `Map.set` at one key leaves every other key's lookup alone. -/
theorem lookup_setEntries_other (key key' : ServiceKey) (value : ServiceKey.Carrier U key)
    (hne : key' ≠ key) :
    ∀ es : List (Service U), lookup key' (setEntries key value es) = lookup key' es
  | [] => by
    rw [setEntries_nil, lookup_cons_other ⟨key, value⟩ key' [] (fun h => hne h.symm)]
  | s :: rest => by
    by_cases h : s.key = key
    · rw [setEntries_cons_same s key value rest h,
        lookup_cons_other ⟨key, value⟩ key' rest (fun h' => hne h'.symm),
        lookup_cons_other s key' rest (fun h' => hne (h.symm.trans h').symm)]
    · rw [setEntries_cons_other s key value rest h]
      by_cases h' : s.key = key'
      · rw [lookup_cons_hit s key' _ h', lookup_cons_hit s key' rest h']
      · rw [lookup_cons_other s key' _ h', lookup_cons_other s key' rest h']
        exact lookup_setEntries_other key key' value hne rest

/-- An unbound key looks up to nothing. -/
theorem lookup_none_of_not_mem (key : ServiceKey) :
    ∀ es : List (Service U), key ∉ es.map Service.key → lookup key es = none
  | [], _ => rfl
  | s :: rest, h => by
    have hs : s.key ≠ key := fun e => h (by rw [List.map_cons, e]; exact List.mem_cons_self)
    have hrest : key ∉ rest.map Service.key :=
      fun m => h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ m)
    rw [lookup_cons_other s key rest hs]
    exact lookup_none_of_not_mem key rest hrest

/-- A lookup answers exactly when the key is bound. -/
theorem lookup_isSome_iff_mem (key : ServiceKey) :
    ∀ es : List (Service U), (lookup key es).isSome = true ↔ key ∈ es.map Service.key
  | [] => ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | s :: rest => by
    rw [List.map_cons, List.mem_cons]
    by_cases h : s.key = key
    · rw [lookup_cons_hit s key rest h]
      exact ⟨fun _ => Or.inl h.symm, fun _ => rfl⟩
    · rw [lookup_cons_other s key rest h, lookup_isSome_iff_mem key rest]
      exact ⟨Or.inr, fun m => m.elim (fun e => absurd e.symm h) id⟩

/-! ### Key uniqueness through `set` -/

/-- Setting a bound key does not move it. -/
theorem setEntries_keys_of_mem (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    ∀ es : List (Service U), key ∈ es.map Service.key →
      (setEntries key value es).map Service.key = es.map Service.key
  | [], h => absurd h List.not_mem_nil
  | s :: rest, h => by
    by_cases hs : s.key = key
    · rw [setEntries_cons_same s key value rest hs]
      show key :: rest.map Service.key = s.key :: rest.map Service.key
      rw [hs]
    · rw [setEntries_cons_other s key value rest hs]
      have hmem : key ∈ rest.map Service.key := by
        rw [List.map_cons] at h
        rcases List.mem_cons.mp h with heq | hmem
        · exact absurd heq.symm hs
        · exact hmem
      show s.key :: (setEntries key value rest).map Service.key = s.key :: rest.map Service.key
      exact congrArg (fun l => s.key :: l) (setEntries_keys_of_mem key value rest hmem)

/-- Setting a new key appends it. -/
theorem setEntries_keys_of_not_mem (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    ∀ es : List (Service U), key ∉ es.map Service.key →
      (setEntries key value es).map Service.key = es.map Service.key ++ [key]
  | [], _ => rfl
  | s :: rest, h => by
    have hs : s.key ≠ key := fun e => h (by rw [List.map_cons, e]; exact List.mem_cons_self)
    have hrest : key ∉ rest.map Service.key :=
      fun m => h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ m)
    rw [setEntries_cons_other s key value rest hs]
    show s.key :: (setEntries key value rest).map Service.key =
      (s.key :: rest.map Service.key) ++ [key]
    exact congrArg (fun l => s.key :: l) (setEntries_keys_of_not_mem key value rest hrest)

private theorem nodup_single {γ : Type u} (value : γ) : ([value] : List γ).Nodup :=
  List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- `Map.set` preserves key uniqueness. -/
theorem setEntries_nodup (key : ServiceKey) (value : ServiceKey.Carrier U key)
    (es : List (Service U)) (h : (es.map Service.key).Nodup) :
    ((setEntries key value es).map Service.key).Nodup := by
  by_cases hmem : key ∈ es.map Service.key
  · rw [setEntries_keys_of_mem key value es hmem]
    exact h
  · rw [setEntries_keys_of_not_mem key value es hmem]
    refine List.nodup_append.mpr ⟨h, nodup_single key, ?_⟩
    intro left hleft right hright hcontra
    rw [List.mem_singleton] at hright
    exact hmem (by rw [← hright, ← hcontra]; exact hleft)

/-! ### The operations -/

/-- `Context.add(self, key, value)` (`internal/effect.ts:2136`, `:2232`, `:3942`): `Map.set`. -/
def add (self : Context U) (key : ServiceKey) (value : ServiceKey.Carrier U key) : Context U :=
  ⟨setEntries key value self.entries, setEntries_nodup key value self.entries self.keysNodup⟩

/-- `Context.merge(self, that)`'s fold: `that`'s entries set into `self`, in `that`'s order. -/
def mergeEntries (self : Context U) : List (Service U) → Context U
  | [] => self
  | s :: rest => mergeEntries (self.add s.key s.value) rest

/-- `Context.merge(self, that)`, right-biased: `that` wins at a shared key
(`provideContext(self, context) = updateContext(self, Context.merge(context))`,
`internal/effect.ts:2197`: the provided services shadow the fiber's). -/
def merge (self that : Context U) : Context U := mergeEntries self that.entries

/-- `Context.mergeAll(...contexts)` (`Layer.ts:1600`): a left fold of `merge`, so a later
context wins. -/
def mergeAll : List (Context U) → Context U
  | [] => empty
  | c :: rest => rest.foldl merge c

/-- Pointwise agreement of lookups: what a program can observe of two environments. -/
def Equiv (a b : Context U) : Prop := ∀ key, a.get? key = b.get? key

/-- rc.112 `Context.Reference` (`Scheduler.ts:269-272`, `:295-298`): a key with a default. -/
structure Reference (U : ServiceUniverse.{u}) : Type u where
  key : ServiceKey
  default : ServiceKey.Carrier U key

/-- `fiber.getRef(ref)` (`internal/effect.ts:715-727`): the bound value or the default. -/
def getRef (self : Context U) (r : Reference U) : ServiceKey.Carrier U r.key :=
  (self.get? r.key).getD r.default

/-- Which keys are references, with their defaults. In rc.112 this is a property of the key
*object* (`Context.ts:404-406`, `isReference` `:838`), so it lives beside the universe as a
supplied boundary, never inside a key. -/
abbrev References (U : ServiceUniverse.{u}) : Type u := List (Reference U)

/-- The default a reference table gives a key, transported along the key equality. -/
def References.default? (refs : References U) (key : ServiceKey) :
    Option (ServiceKey.Carrier U key) :=
  match refs.find? fun r => r.key = key with
  | none => none
  | some r =>
    if h : r.key = key then some (ServiceKey.transport U (congrArg ServiceKey.service h) r.default)
    else none

/-- `Context.getOption` (`Context.ts:1708`): the bound value; else, for a reference key, its
default; else `none`. This is the lookup a program observes; `get?` is the raw map read. -/
def getOption (refs : References U) (self : Context U) (key : ServiceKey) :
    Option (ServiceKey.Carrier U key) :=
  rightBiased (self.get? key) (refs.default? key)

/-- `Context.getOrElse` (`Context.ts:1293`): a reference's default beats the fallback, which is
evaluated only for a missing non-reference key. -/
def getOrElse (refs : References U) (self : Context U) (key : ServiceKey)
    (orElse : ServiceKey.Carrier U key) : ServiceKey.Carrier U key :=
  (getOption refs self key).getD orElse

/-- `Context.get`/`getUnsafe` (`Context.ts:1480`) as a partial read: `none` is the thrown
"service not found" of a missing non-reference key. -/
def getUnsafe? (refs : References U) (self : Context U) (key : ServiceKey) :
    Option (ServiceKey.Carrier U key) :=
  getOption refs self key

theorem getOption_of_get? (refs : References U) (self : Context U) (key : ServiceKey)
    (value : ServiceKey.Carrier U key) (h : self.get? key = some value) :
    getOption refs self key = some value := by
  simp [getOption, rightBiased, h]

/-- An unbound reference key reads its default (`Context.ts:1708`). -/
theorem getOption_reference_default (refs : References U) (self : Context U) (key : ServiceKey)
    (hmiss : self.get? key = none) :
    getOption refs self key = refs.default? key := by
  simp [getOption, rightBiased, hmiss]

/-- An unbound non-reference key reads `none` (`Context.ts:1708`, the `Option.none()` arm). -/
theorem getOption_plain_none (refs : References U) (self : Context U) (key : ServiceKey)
    (hmiss : self.get? key = none) (hplain : refs.default? key = none) :
    getOption refs self key = none := by
  simp [getOption, rightBiased, hmiss, hplain]

/-- The fallback is not evaluated for a reference key (`Context.ts:1293`). -/
theorem getOrElse_reference (refs : References U) (self : Context U) (key : ServiceKey)
    (orElse dflt : ServiceKey.Carrier U key) (hmiss : self.get? key = none)
    (href : refs.default? key = some dflt) :
    getOrElse refs self key orElse = dflt := by
  simp [getOrElse, getOption, rightBiased, hmiss, href]

/-- `getRef` is `getOption` at the reference's own table entry: the transport along the
reflexive key equality is the identity (`ServiceKey.transport_rfl`). -/
theorem getRef_eq_getOption (self : Context U) (r : Reference U) :
    self.getRef r = (getOption [r] self r.key).getD r.default := by
  cases h : self.get? r.key with
  | none =>
    simp only [getRef, getOption, rightBiased, References.default?, h, List.find?_cons_of_pos,
      decide_true, dif_pos, Option.getD_some, Option.getD_none]
    rfl
  | some value =>
    simp [getRef, getOption, rightBiased, h]

/-- Law 1, the value half: `Equiv` is pointwise equality of `get?`, by definition. -/
theorem equiv_iff (a b : Context U) : Equiv a b ↔ ∀ key, a.get? key = b.get? key := Iff.rfl

/-- The empty environment binds nothing. -/
theorem get?_empty (key : ServiceKey) : (empty : Context U).get? key = none := rfl

/-- Law 2 (lookup at the same key): `add` then `get?` at that key answers the new value. -/
theorem get?_add_same (self : Context U) (key : ServiceKey) (value : ServiceKey.Carrier U key) :
    (self.add key value).get? key = some value :=
  lookup_setEntries_same key value self.entries

/-- Law 3 (lookup at a distinct key): `add` leaves every other key's lookup alone. -/
theorem get?_add_other (self : Context U) (key : ServiceKey) (value : ServiceKey.Carrier U key)
    (key' : ServiceKey) (hne : key' ≠ key) :
    (self.add key value).get? key' = self.get? key' :=
  lookup_setEntries_other key key' value hne self.entries

/-- The merge fold, entry by entry: the right operand's lookup wins where it answers. -/
theorem get?_mergeEntries (key : ServiceKey) :
    ∀ (es : List (Service U)), (es.map Service.key).Nodup → ∀ self : Context U,
      (mergeEntries self es).get? key = rightBiased (lookup key es) (self.get? key)
  | [], _, _ => rfl
  | s :: rest, hnodup, self => by
    rw [List.map_cons] at hnodup
    have htail : (rest.map Service.key).Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : s.key ∉ rest.map Service.key := (List.nodup_cons.mp hnodup).1
    show (mergeEntries (self.add s.key s.value) rest).get? key =
      rightBiased (lookup key (s :: rest)) (self.get? key)
    rw [get?_mergeEntries key rest htail (self.add s.key s.value)]
    by_cases h : s.key = key
    · subst h
      rw [lookup_none_of_not_mem s.key rest hhead, lookup_cons_hit s s.key rest rfl]
      show (self.add s.key s.value).get? s.key = some s.value
      exact get?_add_same self s.key s.value
    · rw [lookup_cons_other s key rest h,
        get?_add_other self s.key s.value key (fun e => h e.symm)]

/-- The merge lookup law: right-biased. -/
theorem get?_merge (a b : Context U) (key : ServiceKey) :
    (a.merge b).get? key = rightBiased (b.get? key) (a.get? key) :=
  get?_mergeEntries key b.entries b.keysNodup a

/-- `rightBiased` is associative. -/
theorem rightBiased_assoc {A : Type u} (x y z : Option A) :
    rightBiased (rightBiased x y) z = rightBiased x (rightBiased y z) := by
  cases x <;> cases y <;> rfl

/-- Law 4 (merge associativity), pointwise: `Equiv` is what a program observes. The data-level
equality is `merge_assoc_eq` below. -/
theorem merge_assoc (a b c : Context U) : Equiv ((a.merge b).merge c) (a.merge (b.merge c)) := by
  intro key
  rw [get?_merge, get?_merge, get?_merge, get?_merge, rightBiased_assoc]

/-! ### The entry list itself

`Equiv` cannot see insertion order; the three lemmas below can. An environment is its entry
list (`ext_entries`); an entry list with unique keys is determined by its key order and its
lookups (`entries_ext`); and a merge's key order is the left operand's, with the right operand's
new keys appended in its own order (`keys_mergeEntries`, `Map.set` on a copy of the left map,
`Context.ts:1819`). Together they lift Law 4 from the lookups to the data. -/

/-- Two environments with the same entry list are the same environment: the key-uniqueness proof
is a proposition. -/
theorem ext_entries {a b : Context U} (h : a.entries = b.entries) : a = b := by
  cases a; cases b
  cases h
  rfl

/-- Two entry lists with unique keys, the same key order and the same lookups are the same list:
under uniqueness, a key's position and the value under it determine the entry. -/
theorem entries_ext :
    ∀ (l₁ l₂ : List (Service U)), (l₁.map Service.key).Nodup → (l₂.map Service.key).Nodup →
      l₁.map Service.key = l₂.map Service.key → (∀ key, lookup key l₁ = lookup key l₂) → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, hk, _ => by simp at hk
  | ⟨sk, sv⟩ :: r₁, ⟨tk, tv⟩ :: r₂, hn₁, hn₂, hk, hl => by
    rw [List.map_cons] at hk hn₁ hn₂
    rw [List.map_cons] at hk
    have hkey : sk = tk := (List.cons.inj hk).1
    have hrest : r₁.map Service.key = r₂.map Service.key := (List.cons.inj hk).2
    subst hkey
    have hval : sv = tv := by
      have h := hl sk
      rw [lookup_cons_same sk sv r₁, lookup_cons_same sk tv r₂] at h
      exact Option.some.inj h
    subst hval
    have htail : ∀ key, lookup key r₁ = lookup key r₂ := by
      intro key
      by_cases h : sk = key
      · subst h
        rw [lookup_none_of_not_mem sk r₁ (List.nodup_cons.mp hn₁).1,
          lookup_none_of_not_mem sk r₂ (List.nodup_cons.mp hn₂).1]
      · have h' := hl key
        rw [lookup_cons_other ⟨sk, sv⟩ key r₁ h, lookup_cons_other ⟨sk, sv⟩ key r₂ h] at h'
        exact h'
    rw [entries_ext r₁ r₂ (List.nodup_cons.mp hn₁).2 (List.nodup_cons.mp hn₂).2 hrest htail]

/-- The merge fold's keys: the left operand's keys keep their positions, and the right operand's
keys not already bound are appended in the right operand's order. -/
theorem keys_mergeEntries :
    ∀ (es : List (Service U)), (es.map Service.key).Nodup → ∀ self : Context U,
      (mergeEntries self es).keys =
        self.keys ++ (es.map Service.key).filter (fun key => !decide (key ∈ self.keys))
  | [], _, self => by
    show self.keys = self.keys ++ []
    rw [List.append_nil]
  | s :: rest, hnodup, self => by
    rw [List.map_cons] at hnodup
    have htail : (rest.map Service.key).Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : s.key ∉ rest.map Service.key := (List.nodup_cons.mp hnodup).1
    show (mergeEntries (self.add s.key s.value) rest).keys = _
    rw [keys_mergeEntries rest htail (self.add s.key s.value), List.map_cons]
    by_cases hmem : s.key ∈ self.keys
    · have hkeys : (self.add s.key s.value).keys = self.keys :=
        setEntries_keys_of_mem s.key s.value self.entries hmem
      rw [hkeys, List.filter_cons_of_neg (by simp [hmem])]
    · have hkeys : (self.add s.key s.value).keys = self.keys ++ [s.key] :=
        setEntries_keys_of_not_mem s.key s.value self.entries hmem
      rw [hkeys, List.filter_cons_of_pos (by simp [hmem]), List.append_assoc,
        List.singleton_append]
      congr 2
      apply List.filter_congr
      intro key hkey
      have hne : key ≠ s.key := fun e => hhead (e ▸ hkey)
      simp [hne]

/-- `merge`'s keys: `self`'s in place, then `that`'s new keys in `that`'s order. -/
theorem keys_merge (a b : Context U) :
    (a.merge b).keys = a.keys ++ b.keys.filter (fun key => !decide (key ∈ a.keys)) :=
  keys_mergeEntries b.entries b.keysNodup a

/-- Law 4 on the data: the same entry list, not only the same lookups. Both sides keep `a`'s keys
in place and append the new keys of `b` and then of `c` in operand order (`keys_merge`), and the
lookups agree by `merge_assoc`. -/
theorem merge_assoc_eq (a b c : Context U) : (a.merge b).merge c = a.merge (b.merge c) := by
  apply ext_entries
  apply entries_ext _ _ ((a.merge b).merge c).keysNodup (a.merge (b.merge c)).keysNodup
  · show ((a.merge b).merge c).keys = (a.merge (b.merge c)).keys
    simp only [keys_merge, List.filter_append, List.append_assoc]
    congr 2
    rw [List.filter_filter]
    apply List.filter_congr
    intro key _
    by_cases ha : key ∈ a.keys <;> by_cases hb : key ∈ b.keys <;> simp [ha, hb]
  · exact merge_assoc a b c

/-- Law 5 (left identity), pointwise. -/
theorem merge_empty_left (a : Context U) : Equiv (empty.merge a) a := by
  intro key
  rw [get?_merge, get?_empty]
  cases a.get? key <;> rfl

/-- Law 5 (right identity), on the data. -/
theorem merge_empty_right (a : Context U) : a.merge empty = a := rfl

/-- Law 6 (shadowing): a service provided on the right shadows the same key on the left. -/
theorem merge_shadows (a b : Context U) (key : ServiceKey) (value : ServiceKey.Carrier U key)
    (h : b.get? key = some value) : (a.merge b).get? key = some value := by
  rw [get?_merge, h]
  rfl

/-- Law 6, the `add` form: a second `add` at the same key replaces the first, pointwise. -/
theorem add_add_same (self : Context U) (key : ServiceKey) (w v : ServiceKey.Carrier U key) :
    Equiv ((self.add key w).add key v) (self.add key v) := by
  intro key'
  by_cases h : key' = key
  · subst h
    rw [get?_add_same, get?_add_same]
  · rw [get?_add_other (self.add key w) key v key' h, get?_add_other self key w key' h,
      get?_add_other self key v key' h]

/-- A reference read of the empty environment is the default: the "hidden defaults" class. -/
theorem getRef_empty (r : Reference U) : (empty : Context U).getRef r = r.default := rfl

/-- A reference read of a bound key is the bound value. -/
theorem getRef_of_get? (self : Context U) (r : Reference U) (value : ServiceKey.Carrier U r.key)
    (h : self.get? r.key = some value) : self.getRef r = value := by
  show (self.get? r.key).getD r.default = value
  rw [h]
  rfl

/-- Transport of a whole environment across two universes needs their agreement on *every* code:
the "mixed universes" class. Without `h` there is no map `Context U → Context V`; this is the
consumer `ENV-KEY-INTERP` is waiting for, and it is a parameter here, never derived. -/
def transportAll (U V : ServiceUniverse.{u}) (h : ∀ code, U.Carrier code = V.Carrier code)
    (self : Context U) : Context V where
  entries := self.entries.map fun s => ⟨s.key, Eq.mp (h s.key.service) s.value⟩
  keysNodup := by
    rw [List.map_map]
    exact self.keysNodup

end Context

/-! ## The machine's `χ`: the one first-order value alphabet and `Ctx := Context ValU`

`ValU` is the constant universe: every code reads as `Val`. It is the
`ServiceUniverse.exists_carrier_collision` witness — the first-order price paid in full, on
purpose: a machine value alphabet has one carrier, and code identity is what `get?` compares. -/

/-- `ServiceKey` (`Machine/Key.lean`) at the generated rule: the pair of the two one-field
structures, each `ctor 0 [nat]` (the generator's own instance for the same declaration writes
`ctor 0 [ctor 0 [nat], ctor 0 [nat]]`, `ocaml/eff/eff_wire.ml` `emit_service_key`). -/
def serviceKeyImage : Image ServiceKey :=
  (Image.ctor2 (Image.nat.ctor1 0) (Image.nat.ctor1 0) 0).equiv
    (fun p => ⟨⟨p.1⟩, ⟨p.2⟩⟩) (fun k => (k.name.value, k.service.value))
    (fun _ => rfl) (fun _ => rfl)

theorem serviceKeyImage_toVal (k : ServiceKey) :
    serviceKeyImage.toVal k =
      .ctor 0 [.ctor 0 [.nat k.name.value], .ctor 0 [.nat k.service.value]] := rfl

theorem serviceKeyImage_handleFree : Image.HandleFree serviceKeyImage :=
  Image.equiv_handleFree _ _ _ _ _
    (Image.ctor2_handleFree _ _ _ (Image.ctor1_handleFree _ _ Image.nat_handleFree)
      (Image.ctor1_handleFree _ _ Image.nat_handleFree))

/-- The one value alphabet: the shared carrier (U1b). rc.112's values at this instantiation are
numbers, booleans and `undefined` (`exitVoid`, `internal/effect.ts:988`); the handles the
Layer machine mints — a `Scope`, a `MemoMap` (`Layer.ts:421-458`), a `Deferred`
(`Deferred.ts:140-145`), a `FiberImpl` (the handle a fork answers); `fiber.context` as the
service spine (`Value.serviceContext`, so `getContext` answers a value `decode` reads back
exactly, `decode_encode`, and `provideContext(context())` round-trips); a reified `Exit`; and
the two-field answer a memo hit yields (`Layer.ts:438-440`: the entry's Deferred and the map
that owns it), the carrier's `pair`. The spellings below are those shapes at the old argument
types, as `Machine/Stores.lean` spells `Machine.Val`'s; a pattern on a fiber handle writes
`Val.fiber ⟨id⟩`. -/
abbrev Val := Effect4.Store.Val

namespace Val

export Effect4.Store.Val (unit nat bool str bytes list pair ctor ref handle)
export Value (exitOk resultFailure resultSuccess exitNil)

/-- The handle a fork answers (`Value.fiber`, kind 1). -/
@[match_pattern] abbrev fiber (id : FiberId) : Val := Value.fiber id.value
/-- A `Scope` handle: a key of the scope store (`Value.scope`, kind 4). -/
@[match_pattern] abbrev scopeHandle (scope : Nat) : Val := Value.scope scope
/-- A `MemoMap` handle (`Layer.ts:421-458`; `Value.memoMap`, kind 5). -/
@[match_pattern] abbrev memoMap (id : Nat) : Val := Value.memoMap id
/-- A `Deferred` handle (`Deferred.ts:140-145`; `Value.promise`, kind 3). -/
@[match_pattern] abbrev promise (cell : Nat) : Val := Value.promise cell
/-- `awaitAllChildren`'s snapshot: the fiber handles under `Value.fiberSnapshot`. -/
abbrev fibers (ids : List FiberId) : Val :=
  Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)

end Val

abbrev ValU : ServiceUniverse.{0} := ⟨fun _ => Val⟩

/-- Every carrier of `ValU` is `Val`, definitionally. -/
theorem ValU_carrier (key : ServiceKey) : ServiceKey.Carrier ValU key = Val := rfl

/-- `ValU` is a carrier collision on every pair of codes: the first-order price, exhibited. -/
theorem ValU_collides (a b : ServiceTypeCode) : ValU.Carrier a = ValU.Carrier b := rfl

instance (key : ServiceKey) : DecidableEq (ServiceKey.Carrier ValU key) :=
  inferInstanceAs (DecidableEq Val)

/-- A `ValU` service's value, as the `Val` it is. -/
def Service.valueVal (s : Service ValU) : Val := s.value

instance : DecidableEq (Service ValU) := fun a b =>
  if hk : a.key = b.key then
    if hv : a.valueVal = b.valueVal then
      isTrue (by
        obtain ⟨ka, va⟩ := a
        obtain ⟨kb, vb⟩ := b
        have hk' : ka = kb := hk
        subst hk'
        have hv' : va = vb := hv
        subst hv'
        rfl)
    else isFalse (fun h => hv (congrArg Service.valueVal h))
  else isFalse (fun h => hk (congrArg Service.key h))

/-- The machine's `χ`. -/
abbrev Ctx := Context ValU

instance : DecidableEq Ctx := fun a b =>
  if h : a.entries = b.entries then
    isTrue (by
      obtain ⟨ea, pa⟩ := a
      obtain ⟨eb, pb⟩ := b
      have h' : ea = eb := h
      subst h'
      rfl)
  else isFalse (fun e => h (congrArg Context.entries e))

/-! ### `Ctx` operations at `Val`

`Carrier ValU key` unfolds to `Val` at default transparency and not below it, so a statement that
passes a `Val` where `add` expects a `Carrier ValU key` is type-correct for the elaborator but not
for `rw`'s motive check or `decide`'s instance search. These wrappers state the same operations
at `Val`; each lemma is the generic one, read at `ValU`. -/

/-- `Context.add` at `Val`. -/
def Context.addV (self : Ctx) (key : ServiceKey) (value : Val) : Ctx := self.add key value

/-- `Context.get?` at `Val`. -/
def Context.getV (self : Ctx) (key : ServiceKey) : Option Val := self.get? key

theorem Context.getV_empty (key : ServiceKey) : (Context.empty : Ctx).getV key = none := rfl

theorem Context.getV_addV_same (self : Ctx) (key : ServiceKey) (value : Val) :
    (self.addV key value).getV key = some value :=
  Context.get?_add_same self key value

theorem Context.getV_addV_other (self : Ctx) (key : ServiceKey) (value : Val)
    (key' : ServiceKey) (hne : key' ≠ key) : (self.addV key value).getV key' = self.getV key' :=
  Context.get?_add_other self key value key' hne

theorem Context.getV_merge (a b : Ctx) (key : ServiceKey) :
    (a.merge b).getV key = rightBiased (b.getV key) (a.getV key) :=
  Context.get?_merge a b key

/-- `Equiv` at `Val`: the same pointwise statement. -/
theorem Context.equivV_iff (a b : Ctx) : Context.Equiv a b ↔ ∀ key, a.getV key = b.getV key :=
  Iff.rfl

/-! ### The well-known keys and references

rc.112 tags are strings; here a tag is a `ServiceKey` with a fixed name and code. -/

/-- `Scope.Scope` (`internal/effect.ts:3772`, `Context.Service("effect/Scope")`). -/
def scopeKey : ServiceKey := ⟨⟨0⟩, ⟨0⟩⟩

/-- `Scheduler.MaxOpsBeforeYield` (`Scheduler.ts:269-272`). -/
def maxOpsKey : ServiceKey := ⟨⟨1⟩, ⟨1⟩⟩

/-- `Scheduler.PreventSchedulerYield` (`Scheduler.ts:295-298`). -/
def preventYieldKey : ServiceKey := ⟨⟨2⟩, ⟨2⟩⟩

/-- `Layer.CurrentMemoMap` (`Layer.ts:584`, `Context.Service("effect/Layer/CurrentMemoMap")`),
a plain service: `forkOrCreate` reads it with `getOrUndefined` and has no default. -/
def currentMemoMapKey : ServiceKey := ⟨⟨3⟩, ⟨3⟩⟩

/-- `MaxOpsBeforeYield`'s reference: `defaultValue: () => 2048` (`Scheduler.ts:271`). -/
def maxOpsRef : Context.Reference ValU := ⟨maxOpsKey, Val.nat 2048⟩

/-- `PreventSchedulerYield`'s reference: `defaultValue: () => false` (`Scheduler.ts:297`). -/
def preventYieldRef : Context.Reference ValU := ⟨preventYieldKey, Val.bool false⟩

/-! ### The hooks `Deep.Fibers` reads off `χ` -/

/-- A scope handle read off an optional value. -/
def scopeOfVal : Option Val → Option Nat
  | some (Val.scopeHandle scope) => some scope
  | _ => none

/-- A `Nat` read off a value, with a default for the wrong shape. -/
def natOfVal (default : Nat) : Val → Nat
  | Val.nat n => n
  | _ => default

/-- A `Bool` read off a value, with a default for the wrong shape. -/
def boolOfVal (default : Bool) : Val → Bool
  | Val.bool b => b
  | _ => default

/-- `RunInterp.ambientScope`: the `Scope` service, when bound to a scope handle (`forkScoped`,
`internal/effect.ts:5406`: `flatMap(scope, …)`). -/
def ambientScope (c : Ctx) : Option Nat := scopeOfVal (c.getV scopeKey)

/-- `RunInterp.budgetOf`: `setContext`'s two cached reference reads (`internal/effect.ts:726-727`),
with rc.112's defaults where the key is unbound or bound to a value of the wrong shape. -/
def budgetOf (c : Ctx) : Nat × Bool :=
  (natOfVal 2048 (c.getRef maxOpsRef), boolOfVal false (c.getRef preventYieldRef))

/-- One context entry, written: the key at `serviceKeyImage`, paired with the value. -/
def entryStore (key : ServiceKey) (value : Val) : Val :=
  .pair (serviceKeyImage.toVal key) value

/-- One context entry, read: a `pair` of a key and a value; `none` on any other shape. -/
def ofEntry : Val → Option (ServiceKey × Val)
  | .pair k v => (serviceKeyImage.ofVal k).map fun key => (key, v)
  | _ => none

/-- The context as a value: the written entries, in binding order, under
`Value.serviceContext` (`RuntimeCtor.serviceContext`). -/
def encodeEntries (es : List (Service ValU)) : Val :=
  Value.serviceContext (es.map fun s => entryStore s.key s.valueVal)

/-- `RunInterp.contextValue`: `getContext`'s answer (`internal/effect.ts:2153`). -/
def encode (c : Ctx) : Val := encodeEntries c.entries

/-- The members of a spine read back as entries; `none` at the first member that is no entry. -/
def entriesOf : List Val → Option (List (Service ValU))
  | [] => some []
  | e :: rest =>
    match ofEntry e, entriesOf rest with
    | some (key, value), some es => some ((⟨key, value⟩ : Service ValU) :: es)
    | _, _ => none

/-- The spine read back as entries; `none` off a non-spine value. -/
def spine : Val → Option (List (Service ValU))
  | Value.serviceContext es => entriesOf es
  | _ => none

/-- A value read back as a context: a spine with unique keys. -/
def decode (v : Val) : Option Ctx :=
  (spine v).bind fun es => if h : (es.map Service.key).Nodup then some ⟨es, h⟩ else none

theorem ofEntry_entryStore (key : ServiceKey) (value : Val) :
    ofEntry (entryStore key value) = some (key, value) := by
  show (serviceKeyImage.ofVal (serviceKeyImage.toVal key)).map (fun key => (key, value)) =
    some (key, value)
  rw [Image.ofVal_toVal]
  rfl

theorem entriesOf_entryStore :
    ∀ es : List (Service ValU), entriesOf (es.map fun s => entryStore s.key s.valueVal) = some es
  | [] => rfl
  | s :: rest => by
    show (match ofEntry (entryStore s.key s.valueVal),
        entriesOf (rest.map fun s => entryStore s.key s.valueVal) with
      | some (key, value), some es => some ((⟨key, value⟩ : Service ValU) :: es)
      | _, _ => none) = some (s :: rest)
    rw [ofEntry_entryStore, entriesOf_entryStore rest]
    rfl

theorem spine_encodeEntries (es : List (Service ValU)) : spine (encodeEntries es) = some es :=
  entriesOf_entryStore es

/-- The context value round-trips: `provideContext(self, yield* context())` is the identity on
the map, as it is on the host. -/
theorem decode_encode (c : Ctx) : decode (encode c) = some c := by
  show (spine (encodeEntries c.entries)).bind
    (fun es => if h : (es.map Service.key).Nodup then some (⟨es, h⟩ : Ctx) else none) = some c
  rw [spine_encodeEntries c.entries]
  exact dif_pos c.keysNodup

/-- The empty context's hooks are rc.112's defaults: no ambient scope, `2048`, `false`. -/
theorem hooks_empty :
    ambientScope Context.empty = none ∧ budgetOf Context.empty = (2048, false) := ⟨rfl, rfl⟩

/-- `scoped`'s install (`internal/effect.ts:3942`, `Context.add(fiber.context, scopeTag, scope)`)
is what `ambientScope` reads back. -/
theorem ambientScope_add_scope (c : Ctx) (scope : Nat) :
    ambientScope (c.addV scopeKey (Val.scopeHandle scope)) = some scope := by
  show scopeOfVal ((c.addV scopeKey (Val.scopeHandle scope)).getV scopeKey) = some scope
  rw [Context.getV_addV_same]
  rfl

/-! ### The reserved keys

`scopeKey`, `maxOpsKey`, `preventYieldKey`, `currentMemoMapKey` are names `0`–`3`
(`docs/research/2026-09-04-provision-algebra.md`, finding 1: a name table that lands on
`maxOpsKey` sets the budget to its value). Any key table a program or a reader mints starts
at `firstFreeName`. -/

/-- The first name no reserved key uses. -/
def firstFreeName : Nat := 4

#guard [scopeKey, maxOpsKey, preventYieldKey, currentMemoMapKey].map (·.name.value) = [0, 1, 2, 3]
#guard [scopeKey, maxOpsKey, preventYieldKey, currentMemoMapKey].all fun k => k.name.value < firstFreeName

/-! ### Instances the fiber context needs -/

instance : Repr Ctx :=
  ⟨fun c p => reprPrec (c.entries.map fun s => (s.key, s.valueVal)) p⟩

instance : Inhabited Ctx := ⟨Context.empty⟩

/-! ### Lookups name entries -/

/-- A scope handle read off a value is that value. -/
theorem scopeOfVal_some {v : Val} {scope : Nat} (h : scopeOfVal (some v) = some scope) :
    v = Val.scopeHandle scope := by
  unfold scopeOfVal at h
  split at h
  · rename_i scope' heq
    injection h with h
    injection heq with heq
    subst h
    exact heq
  · exact nomatch h

/-- A lookup that answers names an entry: the key's, holding the value. -/
theorem Context.lookup_mem {key : ServiceKey} {v : Val} :
    ∀ {es : List (Service ValU)}, Context.lookup key es = some v →
      ∃ s ∈ es, s.key = key ∧ s.valueVal = v
  | [], h => nomatch h
  | s :: rest, h => by
    by_cases hk : s.key = key
    · rw [Context.lookup_cons_hit s key rest hk] at h
      injection h with h
      exact ⟨s, List.mem_cons_self, hk, h⟩
    · rw [Context.lookup_cons_other s key rest hk] at h
      obtain ⟨t, ht, hkey, hv⟩ := Context.lookup_mem h
      exact ⟨t, List.mem_cons_of_mem s ht, hkey, hv⟩

theorem Context.getV_mem {c : Ctx} {key : ServiceKey} {v : Val} (h : c.getV key = some v) :
    ∃ s ∈ c.entries, s.key = key ∧ s.valueVal = v :=
  Context.lookup_mem h

/-- What `Map.set` contributes to a fold over the entries: the new entry's share, and the old
entries' — the replaced entry's share is dropped, never added. -/
theorem Context.flatMap_setEntries_subset {γ : Type} (g : Service ValU → List γ) (key : ServiceKey)
    (value : ServiceKey.Carrier ValU key) :
    ∀ es : List (Service ValU),
      (Context.setEntries key value es).flatMap g ⊆ g ⟨key, value⟩ ++ es.flatMap g
  | [] => by
    rw [Context.setEntries_nil, List.flatMap_cons, List.flatMap_nil]
    exact List.Subset.refl _
  | s :: rest => by
    intro x hx
    by_cases h : s.key = key
    · rw [Context.setEntries_cons_same s key value rest h, List.flatMap_cons] at hx
      rw [List.flatMap_cons, List.mem_append, List.mem_append]
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
    · rw [Context.setEntries_cons_other s key value rest h, List.flatMap_cons] at hx
      rw [List.flatMap_cons, List.mem_append, List.mem_append]
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · rcases List.mem_append.mp (Context.flatMap_setEntries_subset g key value rest hx) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

/-! ### Exactness of the codec: the map is an image of the carrier -/

theorem ofEntry_exact {e : Val} {key : ServiceKey} {value : Val}
    (h : ofEntry e = some (key, value)) : e = entryStore key value := by
  unfold ofEntry at h
  split at h
  · next k v =>
    obtain ⟨key', hk, hj⟩ := Image.map_eq_some_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hj
    show Store.Val.pair k v = Store.Val.pair (serviceKeyImage.toVal key') v
    rw [serviceKeyImage.ofVal_exact hk]
  · exact nomatch h

theorem entriesOf_exact :
    ∀ {es : List Val} {ss : List (Service ValU)}, entriesOf es = some ss →
      es = ss.map fun s => entryStore s.key s.valueVal
  | [], ss, h => by
    have h' : some ([] : List (Service ValU)) = some ss := h
    injection h' with h'
    rw [← h']
    rfl
  | e :: rest, ss, h => by
    simp only [entriesOf] at h
    split at h
    · next key value es he hes =>
      injection h with h
      subst h
      rw [List.map_cons, ← entriesOf_exact hes, ofEntry_exact he]
      rfl
    · exact nomatch h

theorem spine_exact {v : Val} {ss : List (Service ValU)} (h : spine v = some ss) :
    v = encodeEntries ss := by
  unfold spine at h
  split at h
  · next es =>
    show Store.Val.ctor 5 es = Store.Val.ctor 5 (ss.map fun s => entryStore s.key s.valueVal)
    rw [← entriesOf_exact h]
  · exact nomatch h

theorem decode_exact {v : Val} {c : Ctx} (h : decode v = some c) : v = encode c := by
  unfold decode at h
  cases hs : spine v with
  | none =>
    rw [hs] at h
    exact nomatch h
  | some es =>
    rw [hs] at h
    change (if hn : (es.map Service.key).Nodup then some (⟨es, hn⟩ : Ctx) else none) = some c at h
    split at h
    · next hn =>
      injection h with h
      subst h
      exact spine_exact hs
    · exact nomatch h

/-- The map as an image of the carrier: the spine codec, exact. -/
def contextImage : Image Ctx := ⟨encode, decode, decode_encode, fun h => decode_exact h⟩

end Effect4.Machine.Env
