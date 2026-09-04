import Effect4.Machine.Fibers
import Effect4.Machine.Key
import Effect4.Data.Row
import Effects.Algebra.Program

/-!
# Deep spike S5, part 1: the Context carrier (M4a, M4b) and the machine's `χ`

Status: design spike, 2026-09-03. Module `Deep.Context` of the non-default `Deep` library
(`lakefile.toml`, `srcDir = "workshop"`); built with `lake build Deep.Context`. Plan:
`docs/research/2026-09-03-deep-plan.md` row S5, rows M4a/M4b of §2 as split by
`docs/research/2026-09-03-deep-plan-review.md` findings 6 and 7. Order:
`docs/ENVIRONMENT-DAG.md` L1 (`Context/Requirement`, `Context/Service`) then L2
(`Context/Environment`). Report: `docs/research/2026-09-03-spike-s5-context-layer.md`.

Reused, never re-declared: `Effect4.ServiceKey`, `ServiceUniverse`, `ServiceKey.Carrier`,
`ServiceKey.transport`, `ServiceUniverse.exists_carrier_collision` (`Effect4/Context/Key.lean`),
`Effect4.Row` (`Effect4/Data/Row.lean`), `Effects.Program` (`.lake/packages/effects`).

**Source.** rc.112's `Context.ts` and `Result.ts` are not in the vendored tree
(`vendor/effect-4.0.0-rc.112/src/` has neither). The `Context` model below is read off its
*uses* in `internal/effect.ts` and `Layer.ts` and off the census summaries: `Context.empty()`
(`internal/effect.ts:627`), `Context.add(ctx, key, value)` (`:2136`, `:2232`, `:3942`),
`Context.merge(self, that)` right-biased (`:2197`, `provideContext` is
`updateContext(self, Context.merge(context))`), `Context.getUnsafe` throwing on a missing key
(`:2134`, `Layer.ts:807`), `Context.getOrUndefined` (`Layer.ts:586`), `Context.Reference` with a
`defaultValue` read through `fiber.getRef` (`:715-727`, `Scheduler.ts:269-298`), and
`Context.mergeAll` (`Layer.ts:1600`). Insertion order is the JavaScript `Map` order the host
keeps; only `mergeAll`'s fold observes it. Where the model chooses (the `Map.set` position of an
existing key; identity versus data equality in `updateContext`'s `prevContext === nextContext`,
`:2090`), the docstring says so.

**Two levels.** Everything up to `Context.interpret_agree` is generic in a supplied
`ServiceUniverse U`, as `docs/ENVIRONMENT-DAG.md` requires. The machine instantiation is at
`ValU`, the constant universe whose every carrier is the one first-order value alphabet `Val` —
which is exactly the `exists_carrier_collision` witness, so type identity recovers nothing here
by construction. `Ctx := Context ValU` is the `χ` of `Deep.Fibers`; `ambientScope`, `budgetOf`,
`encode` are the values of `RunInterp.ambientScope`, `budgetOf`, `contextValue`, and
`Context.empty` is `emptyContext`. The one instantiation of the machine's alphabets `ν σ St`
over this `χ` is `Deep.Layer` (S2's `Deep.Stores` alphabets are closed inductives and cannot be
extended from outside; the landing merges them).

The error channel is `Cause`/`Exit` everywhere; a missing service is a *defect*
(`Context.getUnsafe` throws, `runLoop` catches at `:670-674` and re-enters with `exitDie`), never
a typed error and never a hidden default.
-/

set_option autoImplicit false

namespace Effect4.Machine.Env

open Effect4

universe u

/-! ## M4a — `Context/Requirement` (L1, fence F-REQ)

`PLAN.md` §"environment" row 4: "Make `Requirement` an alias or named view of `Row ServiceKey`",
no second row carrier. `docs/ENVIRONMENT-DAG.md` open question 2 is settled the same way. -/

/-- A requirement row: the canonical set of service keys a program needs. An alias of the one
row carrier, so every `Row` law is a `Requirement` law with no restatement. -/
abbrev Requirement : Type := Row ServiceKey

namespace Requirement

/-- No requirement. -/
def empty : Requirement := Row.empty

/-- One key. -/
def single (key : ServiceKey) : Requirement := Row.singleton key

/-- Both rows' keys (`Row.union`, canonical). -/
def union (r s : Requirement) : Requirement := Row.union r s

/-- A raw key list, normalised (`Row.normalize`): the only way a list becomes a row. -/
def ofList (keys : List ServiceKey) : Requirement := Row.normalize keys

end Requirement

/-! ## M4a — `Context/Service` (L1, fence F-SVC)

The edge `Context/Key → Context/Service` carries the interpretation triple `ServiceUniverse`,
`ServiceKey.Carrier`, `ServiceKey.transport` (`docs/ENVIRONMENT-DAG.md` edge table). A service is
a key bound to a value of its carrier under a *supplied* universe: first-order at the key, with
the universe in the trusted-boundary position `Effect4.FlowAlphabet` occupies. -/

/-- A service: a key and a value of the key's carrier under `U`. -/
structure Service (U : ServiceUniverse.{u}) : Type u where
  /-- The identity, a nominal name paired with a first-order type code. -/
  key : ServiceKey
  /-- The value, typed by the code through `U` and never by the name. -/
  value : ServiceKey.Carrier U key

/-- The service-access signature: one operation per key, rc.112's `Effect.service(tag)` /
`Context.Tag` as an effect (`internal/effect.ts:2069-2070`: `withFiber(fiber =>
fromOption(Context.getOption(fiber.context, service)))`), whose answer is the key's carrier.
`PLAN.md:207`: "Prefer a derived `ServiceSignature U` and `request = Program.perform` over a
duplicate service program." -/
abbrev serviceSig (U : ServiceUniverse.{u}) : Effects.Signature.{0, u} where
  Op := ServiceKey
  Answer := fun key => ServiceKey.Carrier U key

/-- A program over the service-access signature: the reused `Effects.Program`. -/
abbrev ServiceProgram (U : ServiceUniverse.{u}) (A : Type u) : Type u :=
  Effects.Program (serviceSig U) A

/-- `Program.UsesOnly r p`: every operation `p` can perform, along every answer, names a key of
`r`. A predicate over the well-founded tree, not a computed row: `PLAN.md:207` forbids claiming a
finite `Program.requirements` for higher-order continuations. -/
inductive UsesOnly {U : ServiceUniverse.{u}} {A : Type u} (r : Requirement) :
    ServiceProgram U A → Prop
  /-- A finished program uses nothing. -/
  | pure (value : A) : UsesOnly r (.pure value)
  /-- A visit uses its key and whatever every continuation uses. -/
  | vis (key : ServiceKey) (next : ServiceKey.Carrier U key → ServiceProgram U A)
      (hkey : key ∈ r) (hnext : ∀ answer, UsesOnly r (next answer)) : UsesOnly r (.vis key next)

section UsesOnlyLaws

variable {U : ServiceUniverse.{u}} {A B : Type u}

/-- Law 1 (pure): `pure` uses only the empty row, hence only any row. -/
theorem usesOnly_pure (r : Requirement) (value : A) :
    UsesOnly (U := U) r (Effects.Program.pure value) :=
  UsesOnly.pure value

/-- Law 2 (visit): a visit whose key is in the row and whose continuations use only the row uses
only the row. -/
theorem usesOnly_visit (r : Requirement) (key : ServiceKey)
    (next : ServiceKey.Carrier U key → ServiceProgram U A) (hkey : key ∈ r)
    (hnext : ∀ answer, UsesOnly r (next answer)) :
    UsesOnly r (Effects.Program.vis key next) :=
  UsesOnly.vis key next hkey hnext

/-- Law 3 (perform): `Program.perform key` uses only a row containing `key`. -/
theorem usesOnly_perform (r : Requirement) (key : ServiceKey) (hkey : key ∈ r) :
    UsesOnly r (Effects.Program.perform (S := serviceSig U) key) :=
  UsesOnly.vis key Effects.Program.pure hkey (fun answer => UsesOnly.pure answer)

/-- Law 5 (weakening): a program that uses only `r` uses only any superset row. -/
theorem usesOnly_weaken {r s : Requirement} {p : ServiceProgram U A}
    (hp : UsesOnly r p) (hrs : Row.Subset r s) : UsesOnly s p := by
  induction hp with
  | pure value => exact UsesOnly.pure value
  | vis key next hkey _ ih => exact UsesOnly.vis key next (hrs key hkey) ih

/-- Law 4 (bind by union): sequencing a program using only `r` with continuations using only `s`
uses only `r ∪ s`. -/
theorem usesOnly_bind_union {r s : Requirement} {p : ServiceProgram U A}
    {f : A → ServiceProgram U B} (hp : UsesOnly r p) (hf : ∀ value, UsesOnly s (f value)) :
    UsesOnly (Requirement.union r s) (Effects.Program.bind p f) := by
  induction hp with
  | pure value =>
    show UsesOnly (Requirement.union r s) (f value)
    exact usesOnly_weaken (hf value) (Row.subset_union_right r s)
  | vis key next hkey _ ih =>
    show UsesOnly (Requirement.union r s)
      (Effects.Program.vis key (fun answer => Effects.Program.bind (next answer) f))
    exact UsesOnly.vis key _ ((Row.mem_union key r s).mpr (Or.inl hkey)) ih

end UsesOnlyLaws

/-- **`ENV-KEY-INTERP`, the open edge.** Every typing statement about a service value is relative
to a supplied universe, and nothing forces two callers to agree on one. `UniverseAgreement U V r`
is what agreement on a row *would* be; no declaration of this module, and none of `Deep.Layer`,
proves an instance of it or consumes one. It is named so the edge stays visible, not to close it
(`docs/ENVIRONMENT-DAG.md:23-25`, `Effect4/Context/Key.lean:35-38`). -/
def UniverseAgreement (U V : ServiceUniverse.{u}) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → ServiceKey.Carrier U key = ServiceKey.Carrier V key

/-! ## M4b — `Context/Environment` (L2, fence F-ENV): the first-order environment

An insertion-ordered map from `ServiceKey` to values with unique keys, rc.112's `Context` as a
JavaScript `Map` keyed by the tag. The uniqueness invariant is a proof field, as
`Effect4.ReasonAnnotations` (`Effect4/Semantics/Cause.lean:28-33`) does it, so no operation can
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

/-- The requirement row an environment answers: its keys, canonical. -/
def keysRow (self : Context U) : Requirement := Row.normalize self.keys

/-- `Satisfies self r`: every key of the row is bound. -/
def Satisfies (self : Context U) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → (self.get? key).isSome = true

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

/-- The interpretation of a service program under an environment: every `vis key` is answered
by `get?`; a missing key stops the run with `none` — the frontier `Context.getUnsafe` throws at.
Total on `UsesOnly` programs under a satisfying environment (`interpret_total`). -/
def interpret (self : Context U) {A : Type u} : ServiceProgram U A → Option A
  | .pure value => some value
  | .vis key next => (self.get? key).bind fun value => interpret self (next value)

/-! ### `ENV-PG-CONTEXT`: the eleven laws of `PLAN.md:208`

"pointwise extensionality, lookup at the same and distinct keys, merge associativity and
identities, shadowing, satisfaction for empty/singleton/union, weakening, handler agreement, and
total interpretation for `UsesOnly` programs under a satisfying environment." -/

/-- Law 1 (extensionality). Two environments with the same lookups answer the same requirement
row and the same value at every key. Insertion order is *not* recovered — `Equiv` is exactly what
`get?` can see, and the eighth counterexample below shows order is invisible to it. -/
theorem ext_keysRow {a b : Context U} (h : Equiv a b) : a.keysRow = b.keysRow := by
  apply Row.eq_of_mem_iff
  intro key
  show key ∈ Row.normalize (a.entries.map Service.key) ↔
    key ∈ Row.normalize (b.entries.map Service.key)
  rw [Row.mem_normalize, Row.mem_normalize, ← lookup_isSome_iff_mem key a.entries,
    ← lookup_isSome_iff_mem key b.entries]
  have e : lookup key a.entries = lookup key b.entries := h key
  rw [e]

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

/-- Law 7 (satisfaction, empty): every environment satisfies the empty row. -/
theorem satisfies_empty (self : Context U) : self.Satisfies Requirement.empty :=
  fun key h => absurd h (Row.not_mem_empty key)

/-- Law 8 (satisfaction, singleton): iff the key is bound. -/
theorem satisfies_single (self : Context U) (key : ServiceKey) :
    self.Satisfies (Requirement.single key) ↔ (self.get? key).isSome = true := by
  constructor
  · intro h
    exact h key ((Row.mem_singleton key key).mpr rfl)
  · intro h key' hmem
    have e : key' = key := (Row.mem_singleton key key').mp hmem
    rw [e]
    exact h

/-- Law 9 (satisfaction, union): iff both rows are satisfied. -/
theorem satisfies_union (self : Context U) (r s : Requirement) :
    self.Satisfies (Requirement.union r s) ↔ self.Satisfies r ∧ self.Satisfies s := by
  constructor
  · intro h
    exact ⟨fun key hk => h key ((Row.mem_union key r s).mpr (Or.inl hk)),
      fun key hk => h key ((Row.mem_union key r s).mpr (Or.inr hk))⟩
  · intro h key hk
    rcases (Row.mem_union key r s).mp hk with hr | hs
    · exact h.1 key hr
    · exact h.2 key hs

/-- Law 10 (weakening): satisfying a row satisfies every subrow. -/
theorem satisfies_weaken (self : Context U) {r s : Requirement} (h : self.Satisfies s)
    (hrs : Row.Subset r s) : self.Satisfies r :=
  fun key hk => h key (hrs key hk)

/-- Law 11a (handler agreement): environments agreeing on `r` interpret a program using only
`r` identically. -/
theorem interpret_agree {A : Type u} {r : Requirement} {p : ServiceProgram U A}
    (hp : UsesOnly r p) (a b : Context U) (h : ∀ key, key ∈ r → a.get? key = b.get? key) :
    a.interpret p = b.interpret p := by
  induction hp with
  | pure value => rfl
  | vis key next hkey _ ih =>
    show (a.get? key).bind (fun value => a.interpret (next value)) =
      (b.get? key).bind (fun value => b.interpret (next value))
    rw [h key hkey]
    cases b.get? key with
    | none => rfl
    | some value => exact ih value

/-- Law 11b (total interpretation): a program using only `r` never meets a missing lookup under
an environment satisfying `r`. -/
theorem interpret_total {A : Type u} {r : Requirement} {p : ServiceProgram U A}
    (hp : UsesOnly r p) (self : Context U) (hsat : self.Satisfies r) :
    (self.interpret p).isSome = true := by
  induction hp with
  | pure value => rfl
  | vis key next hkey _ ih =>
    have hs := hsat key hkey
    show ((self.get? key).bind fun value => self.interpret (next value)).isSome = true
    cases hv : self.get? key with
    | none =>
      rw [hv] at hs
      exact Bool.noConfusion hs
    | some value => exact ih value

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

/-- The typed error alphabet. -/
inductive Err
  | boom
  | tag (code : Nat)
deriving DecidableEq, Repr

/-- The defect alphabet. `serviceNotFound` is `Context.getUnsafe`'s throw
(`internal/effect.ts:2134`, `Layer.ts:807`) as `runLoop` re-enters it (`:670-674`, `exitDie`);
`unknownLayer` is a `LayerId` outside the declared table, the model's stand-in for a layer object
that does not exist. -/
inductive Defect
  | notImplemented
  | asyncFiber
  | badName
  | serviceNotFound (key : ServiceKey)
  | unknownLayer (index : Nat)
deriving DecidableEq, Repr

/-- The cause-annotation value alphabet; `stackAnnotations` contributes none. -/
abbrev Ann := Unit

/-- The one value alphabet. `ctxNil`/`ctxCons` spell a context as a spine, so `getContext`
answers a value that `decode` reads back exactly (`decode_encode`); a `List` field would make
`Val` a nested inductive whose `DecidableEq` handler refuses (state note §3.5), and an opaque
handle would break `provideContext(context())`'s round trip. `pair` is the two-field answer a
memo hit yields (`Layer.ts:438-440`: the entry's Deferred and the map that owns it). -/
inductive Val
  /-- `exitVoid`'s value (`internal/effect.ts:988`). -/
  | unit
  | nat (n : Nat)
  | bool (b : Bool)
  /-- The handle a fork answers. -/
  | fiber (id : FiberId)
  /-- `awaitAllChildren`'s snapshot. -/
  | fibers (ids : List FiberId)
  /-- A `Scope` handle: a key of the scope store. -/
  | scopeHandle (scope : Nat)
  /-- A `MemoMap` handle (`Layer.ts:421-458`). -/
  | memoMap (id : Nat)
  /-- A `Deferred` handle (`Deferred.ts:140-145`). -/
  | promise (cell : Nat)
  /-- A two-field answer. -/
  | pair (first second : Val)
  /-- A reified successful `Exit`. -/
  | exitOk (value : Val)
  /-- A reified failed `Exit`. -/
  | exitErr (cause : Cause Err Defect FiberId Ann)
  /-- The empty list of awaited exits (M6). -/
  | exitNil
  /-- One awaited exit, and the rest. -/
  | exitCons (head tail : Val)
  /-- The empty context spine. -/
  | ctxNil
  /-- One bound service, and the rest of the spine. -/
  | ctxCons (key : ServiceKey) (value : Val) (rest : Val)
deriving DecidableEq

/-- The cause carrier at this instantiation. -/
abbrev CauseV := Cause Err Defect FiberId Ann

/-- The exit carrier at this instantiation. -/
abbrev ExitV := Exit Val Err Defect FiberId Ann

/-- The constant universe: every code reads as `Val`. -/
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

/-- The context as a value: the entry spine. -/
def encodeEntries : List (Service ValU) → Val
  | [] => Val.ctxNil
  | s :: rest => Val.ctxCons s.key s.valueVal (encodeEntries rest)

/-- `RunInterp.contextValue`: `getContext`'s answer (`internal/effect.ts:2153`). -/
def encode (c : Ctx) : Val := encodeEntries c.entries

/-- The spine read back as entries; `none` off a non-spine value. -/
def spine : Val → Option (List (Service ValU))
  | Val.ctxNil => some []
  | Val.ctxCons key value rest => (spine rest).map fun es => (⟨key, value⟩ : Service ValU) :: es
  | _ => none

/-- A value read back as a context: a spine with unique keys. -/
def decode (v : Val) : Option Ctx :=
  (spine v).bind fun es => if h : (es.map Service.key).Nodup then some ⟨es, h⟩ else none

theorem spine_encodeEntries : ∀ es : List (Service ValU), spine (encodeEntries es) = some es
  | [] => rfl
  | s :: rest => by
    show (spine (encodeEntries rest)).map (fun es => (⟨s.key, s.valueVal⟩ : Service ValU) :: es) =
      some (s :: rest)
    rw [spine_encodeEntries rest]
    rfl

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

/-- What a `withFiber` context update names: rc.112's three callers of `updateContext`
(`internal/effect.ts:2073-2097`). A function-valued update is a closure and DB-02 forbids one;
these are the three that occur. -/
inductive ContextUpdate
  /-- `setContext(self, context) = updateContext(self, constant(context))` (`:2176`). -/
  | setTo (context : Ctx)
  /-- `provideContext(self, context) = updateContext(self, Context.merge(context))` (`:2197`). -/
  | provide (that : Ctx)
  /-- `provideService(self, key, impl) = updateContext(self, Context.add(key, impl))` (`:2232`). -/
  | provideService (key : ServiceKey) (value : Val)
deriving DecidableEq

/-- `f(prevContext)` (`:2089`). -/
def ContextUpdate.apply : ContextUpdate → Ctx → Ctx
  | setTo context, _ => context
  | provide that, prev => prev.merge that
  | provideService key value, prev => prev.add key value

/-- `provideContext`'s update is the right-biased merge: the provided context wins. -/
theorem ContextUpdate.apply_provide_get? (that prev : Ctx) (key : ServiceKey) :
    ((ContextUpdate.provide that).apply prev).get? key =
      rightBiased (that.get? key) (prev.get? key) :=
  Context.get?_merge prev that key

/-- `provideService`'s update binds the key. -/
theorem ContextUpdate.apply_provideService_getV (key : ServiceKey) (value : Val) (prev : Ctx) :
    ((ContextUpdate.provideService key value).apply prev).getV key = some value :=
  Context.getV_addV_same prev key value

/-- What an instantiation of `Deep.Fibers` at `χ := Ctx` must read off the context: the four
hooks, with these values. `Deep.Layer.interp` satisfies it by `rfl`. -/
structure HooksAgree {ν σ : Type} {St : Type}
    (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx St) : Prop where
  ambient : interp.ambientScope = ambientScope
  budget : interp.budgetOf = budgetOf
  empty : interp.emptyContext = Context.empty
  value : interp.contextValue = encode

/-! ## The seven counterexample classes of `PLAN.md:208`

"nominal collision, carrier collision, mixed universes, missing lookups, right-biased
noncommutativity, hidden defaults, and proof-free casts" — each as an executable `example` at
`ValU` or as the reused theorem, plus an eighth: insertion order is invisible to `get?`. -/

section Counterexamples

/-- The empty environment at `ValU`, so the universe of every example below is fixed. -/
def ctx0 : Ctx := Context.empty

/-- Two keys sharing a name and differing in code. -/
def nominalA : ServiceKey := ⟨⟨7⟩, ⟨0⟩⟩
def nominalB : ServiceKey := ⟨⟨7⟩, ⟨1⟩⟩

/-- CE 1 (nominal collision): the keys conflict nominally, are distinct, and an environment holds
both with distinct values — identity is the pair, never the name. -/
example : ServiceKey.Conflict nominalA nominalB ∧ nominalA ≠ nominalB := by decide

example :
    ((ctx0.addV nominalA (Val.nat 1)).add nominalB (Val.nat 2)).getV nominalA =
        some (Val.nat 1) ∧
      ((ctx0.addV nominalA (Val.nat 1)).add nominalB (Val.nat 2)).getV nominalB =
        some (Val.nat 2) := by
  decide

/-- CE 2 (carrier collision): distinct codes may read as one type (the reused theorem), and at
`ValU` they always do — yet a value bound under one code is not found under the other, because
`get?` compares codes, never types. -/
example : ∃ (U : ServiceUniverse.{0}) (a b : ServiceTypeCode), a ≠ b ∧ U.Carrier a = U.Carrier b :=
  ServiceUniverse.exists_carrier_collision

example : (ctx0.addV nominalA (Val.nat 1)).getV nominalB = none := by decide

/-- CE 3 (mixed universes): a context under one universe is not a context under another; the
only crossing is `transportAll`, which demands agreement on every code — `ENV-KEY-INTERP`. Two
universes that disagree on a code exist: `Nat` and `Bool` are different types. -/
theorem nat_ne_bool : (Nat : Type) ≠ Bool := by
  intro h
  have inj : ∀ a b : Nat, cast h a = cast h b → a = b := fun a b hab => by
    have := congrArg (cast h.symm) hab
    rw [cast_cast, cast_cast, cast_eq, cast_eq] at this
    exact this
  have tri : ∀ a b c : Bool, a = b ∨ b = c ∨ a = c := by decide
  rcases tri (cast h 0) (cast h 1) (cast h 2) with e | e | e
  · exact absurd (inj 0 1 e) (by decide)
  · exact absurd (inj 1 2 e) (by decide)
  · exact absurd (inj 0 2 e) (by decide)

example : ¬ UniverseAgreement ⟨fun _ => Nat⟩ ⟨fun _ => Bool⟩ (Requirement.single scopeKey) :=
  fun h => nat_ne_bool (h scopeKey ((Row.mem_singleton scopeKey scopeKey).mpr rfl))

/-- CE 4 (missing lookups): the empty environment answers nothing, and interpreting a request
under it stops — no default is invented. -/
example : (Context.empty : Ctx).getV scopeKey = none := rfl

example :
    (Context.empty : Ctx).interpret (Effects.Program.perform (S := serviceSig ValU) scopeKey) =
      none := rfl

/-- CE 5 (right-biased noncommutativity): `merge` is not commutative; the right operand wins. -/
example :
    ((ctx0.addV nominalA (Val.nat 1)).merge (ctx0.addV nominalA (Val.nat 2))).getV
        nominalA = some (Val.nat 2) ∧
      ((ctx0.addV nominalA (Val.nat 2)).merge (ctx0.addV nominalA (Val.nat 1))).getV
        nominalA = some (Val.nat 1) := by
  decide

example :
    (ctx0.addV nominalA (Val.nat 1)).merge (ctx0.addV nominalA (Val.nat 2)) ≠
      (ctx0.addV nominalA (Val.nat 2)).merge (ctx0.addV nominalA (Val.nat 1)) := by
  decide

/-- CE 6 (hidden defaults): a reference read of the empty environment answers the default while
the lookup answers nothing; a program reading through `getRef` cannot tell the two apart. -/
example : ((Context.empty : Ctx).getRef maxOpsRef : Val) = Val.nat 2048 ∧
    (Context.empty : Ctx).getV maxOpsKey = none := ⟨rfl, rfl⟩

/-- CE 7 (proof-free casts): the only transport between carriers is `ServiceKey.transport`,
which takes the code equality as an explicit argument; at `ValU` it is the identity and still
demands the proof. No `cast` of a service value appears in this module. -/
example (a b : ServiceKey) (h : a.service = b.service) (v : ServiceKey.Carrier ValU a) :
    ServiceKey.transport ValU h v = v := rfl

/-! CE 8 (order is not observable): two environments that differ only in insertion order are
`Equiv` and are not equal — extensionality holds for `get?`, not for the data. -/

/-- The two orders. -/
def orderAB : Ctx := (ctx0.addV nominalA (Val.nat 1)).addV nominalB (Val.nat 2)
def orderBA : Ctx := (ctx0.addV nominalB (Val.nat 2)).addV nominalA (Val.nat 1)

example : Context.Equiv orderAB orderBA ∧ orderAB ≠ orderBA := by
  refine ⟨fun key => ?_, by decide⟩
  show orderAB.getV key = orderBA.getV key
  by_cases ha : key = nominalA
  · subst ha
    show ((ctx0.addV nominalA (Val.nat 1)).addV nominalB (Val.nat 2)).getV nominalA =
      ((ctx0.addV nominalB (Val.nat 2)).addV nominalA (Val.nat 1)).getV nominalA
    rw [Context.getV_addV_other (ctx0.addV nominalA (Val.nat 1)) nominalB (Val.nat 2) nominalA
        (by decide),
      Context.getV_addV_same, Context.getV_addV_same]
  · by_cases hb : key = nominalB
    · subst hb
      show ((ctx0.addV nominalA (Val.nat 1)).addV nominalB (Val.nat 2)).getV nominalB =
        ((ctx0.addV nominalB (Val.nat 2)).addV nominalA (Val.nat 1)).getV nominalB
      rw [Context.getV_addV_same,
        Context.getV_addV_other (ctx0.addV nominalB (Val.nat 2)) nominalA (Val.nat 1) nominalB
          (by decide),
        Context.getV_addV_same]
    · show ((ctx0.addV nominalA (Val.nat 1)).addV nominalB (Val.nat 2)).getV key =
        ((ctx0.addV nominalB (Val.nat 2)).addV nominalA (Val.nat 1)).getV key
      rw [Context.getV_addV_other (ctx0.addV nominalA (Val.nat 1)) nominalB (Val.nat 2) key hb,
        Context.getV_addV_other ctx0 nominalA (Val.nat 1) key ha,
        Context.getV_addV_other (ctx0.addV nominalB (Val.nat 2)) nominalA (Val.nat 1) key ha,
        Context.getV_addV_other ctx0 nominalB (Val.nat 2) key hb]

end Counterexamples

/-! ## Separation gates at this instantiation (`docs/FRAMES-DAG.md` separation 4) -/

example : DecidableEq Val := inferInstance
example : DecidableEq Ctx := inferInstance
example : DecidableEq ContextUpdate := inferInstance

end Effect4.Machine.Env
