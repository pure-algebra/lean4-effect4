import Effect4.Machine.ContextMap
import Effect4.Machine.Fibers
import Effect4.Data.Row

/-!
# Machine.Context — requirement rows, satisfaction, and the context updates `withFiber` names

The service map — `Context U`, its operations and laws, the machine's constant universe `ValU`,
`Ctx := Context ValU`, the reserved keys, the hooks the fiber machine reads off a context
(`ambientScope`, `budgetOf`) and the spine codec — is `Machine/ContextMap.lean`. This module adds
what reads the map against a requirement row: `Requirement`, an alias of the one row carrier
`Row ServiceKey`; `Context.keysRow` and `Context.Satisfies` with their laws (the adjunction
`satisfies_iff_subset_keysRow` is `Program/Provision.lean`'s); `ContextUpdate`, the three context
updates rc.112's callers of `updateContext` name; the open edge `ENV-KEY-INTERP`, named as
`UniverseAgreement`; and the eight counterexample classes. It is a module of the core root
`Effect4`, read by `Program/Typing/Rules.lean` and `Laws/Machine/ContextValue.lean`.

**History.** It began as deep spike S5 (2026-09-03, `Deep.Context` of the non-default `Deep`
library then; `docs/research/2026-09-03-deep-plan.md` row S5); its map half moved to
`Machine/ContextMap.lean` at the join (`docs/research/2026-09-07-join-dispatch.md`, cut L9). The
spike's model of service-reading programs over `Effects.Program` (`serviceSig`, `ServiceProgram`,
`UsesOnly` and its five laws, `Context.interpret` with handler agreement and total
interpretation, and one counterexample that interpreted a request) had no reader outside itself
and was the core root's one import of the `Effects` package. It was deleted on 2026-10-01
(landing seat F; the text is at `git:dceae006:src/Effect4/Machine/Context.lean`), and the core
root's import closure reaches no `Effects` module since.

**Source.** The `Context` model was read off rc.112's *uses* in `internal/effect.ts` and
`Layer.ts` before `Context.ts` was vendored (`98dcd20a`, 2026-09-04; it is
`vendor/effect-4.0.0-rc.112/src/Context.ts` now), and the citations stay at those uses:
`Context.empty()` (`internal/effect.ts:627`), `Context.add(ctx, key, value)` (`:2136`, `:2232`,
`:3942`), `Context.merge(self, that)` right-biased (`:2197`, `provideContext` is
`updateContext(self, Context.merge(context))`; `Context.ts:1745`: the service from `that`
overrides), `Context.getUnsafe` throwing on a missing key (`:2134`, `Layer.ts:807`),
`Context.getOrUndefined` (`Layer.ts:586`), `Context.Reference` with a `defaultValue` read through
`fiber.getRef` (`:715-727`, `Scheduler.ts:269-298`), and `Context.mergeAll` (`Layer.ts:1600`).
Insertion order is the JavaScript `Map` order the host keeps; only `mergeAll`'s fold observes it.
Where the model chooses (the `Map.set` position of an existing key; identity versus data equality
in `updateContext`'s `prevContext === nextContext`, `:2090`), the docstring says so.

**Two levels.** `Requirement`, `keysRow`, `Satisfies` and their laws are generic in a supplied
`ServiceUniverse U`, as `docs/research/ENVIRONMENT-DAG.md` requires. `ContextUpdate` and the
counterexamples are at the machine's instantiation `ValU`, the constant universe whose every
carrier is the one first-order value alphabet `Val` — exactly the `exists_carrier_collision`
witness, so type identity recovers nothing here by construction. The machine's context
(`Machine/Stores.lean`, `Ctx`) carries one such map as its `services`.

The error channel is `Cause`/`Exit` everywhere; a missing service is a *defect*
(`Context.getUnsafe` throws, `runLoop` catches at `:670-674` and re-enters with `exitDie`), never
a typed error and never a hidden default.

**U1b (2026-09-07).** `Val` is the shared carrier `Effect4.Store.Val` at the table of
`Machine/Value.lean`: a service context is `Value.serviceContext` over `pair key value` entries
(`entryStore`/`ofEntry` the entry codec, `encode`/`decode` the spine codec), the handles are
`Value.scope`/`Value.memoMap`/`Value.promise`/`Value.fiber`, an exit is `Value.exitOk`/
`Value.exitErr`, a memo hit's two-field answer is the carrier's `pair`. The `Env.Val`
namespace keeps the old spellings as patterns, the way `Machine/Stores.lean` spells
`Machine.Val`'s (`docs/research/2026-09-07-u1-cutover-dispatch.md`, U1b).
-/

set_option autoImplicit false

namespace Effect4.Machine.Env

open Effect4

universe u

/-! ## M4a — `Context/Requirement` (L1, fence F-REQ)

`PLAN.md` §"environment" row 4: "Make `Requirement` an alias or named view of `Row ServiceKey`",
no second row carrier. `docs/research/ENVIRONMENT-DAG.md` open question 2 is settled the same way. -/

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
`ServiceKey.Carrier`, `ServiceKey.transport` (`docs/research/ENVIRONMENT-DAG.md` edge table); a
service, a key bound to a value of its carrier under a supplied universe, is `Service` in
`Machine/ContextMap.lean`. -/

/-- **`ENV-KEY-INTERP`, the open edge.** Every typing statement about a service value is relative
to a supplied universe, and nothing forces two callers to agree on one. `UniverseAgreement U V r`
is what agreement on a row *would* be; no declaration of the tree proves an instance of it or
consumes one. It is named so the edge stays visible, not to close it
(`docs/research/ENVIRONMENT-DAG.md:23-25`, `src/Effect4/Machine/Key.lean:35-38`). -/
def UniverseAgreement (U V : ServiceUniverse.{u}) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → ServiceKey.Carrier U key = ServiceKey.Carrier V key

/-! ## M4b — `Context/Environment`: the requirement rows over the map

The map, its operations and its laws are `Machine/ContextMap.lean` (moved in the join,
dependency cut L9; the names keep this namespace). What stays here reads the requirement
rows. -/

namespace Context

variable {U : ServiceUniverse.{u}}

/-- The requirement row an environment answers: its keys, canonical. -/
def keysRow (self : Context U) : Requirement := Row.normalize self.keys

/-- `Satisfies self r`: every key of the row is bound. -/
def Satisfies (self : Context U) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → (self.get? key).isSome = true

/-! ### `ENV-PG-CONTEXT`: the eleven laws of `PLAN.md`, environment / Context

"pointwise extensionality, lookup at the same and distinct keys, merge associativity and
identities, shadowing, satisfaction for empty/singleton/union, weakening, handler agreement, and
total interpretation for `UsesOnly` programs under a satisfying environment." Lookup, merge and
shadowing are `Machine/ContextMap.lean`'s; extensionality, satisfaction and weakening are here.
Handler agreement and total interpretation (laws 11a and 11b) were stated over the
`Effects.Program` service model and were deleted with it on 2026-10-01 (module header). -/

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

end Context

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

/-! ### Shadowing (the join review, 2026-09-08)

`provideContext(self, context)` is `updateContext(self, Context.merge(context))`
(`internal/effect.ts:2197`), and `Context.merge` is right-biased: the provided context's
binding wins where it binds, the previous binding stays where it does not. Two provisions
of one key nest as two updates, and the nearer — applied last — shadows the farther; the
farther is invisible to every lookup. The row plane never sees a duplicate: the requirement
row is a set (`Row.union_idem`, `Program/Typing.lean`'s `Row.diff_single_twice`).

The composition law of the join — the machine's four context hooks read off the service map,
with `Ctx.CacheAgrees` as the premise of the budget hook — is `Effect4.Machine.stores_hooks`
(`Machine/Stores.lean`); the structure that stated it against the retired Layer machine's
interpreter retired with it. -/

theorem ContextUpdate.apply_provide_wins (that prev : Ctx) (key : ServiceKey) (value : Val)
    (h : that.getV key = some value) :
    ((ContextUpdate.provide that).apply prev).getV key = some value := by
  show (prev.merge that).getV key = some value
  rw [Context.getV_merge, h]
  rfl

theorem ContextUpdate.apply_provide_keeps (that prev : Ctx) (key : ServiceKey)
    (h : that.getV key = none) :
    ((ContextUpdate.provide that).apply prev).getV key = prev.getV key := by
  show (prev.merge that).getV key = prev.getV key
  rw [Context.getV_merge, h]
  rfl

/-- Two `provideService`s at one key: the nearer wins, the farther is invisible. -/
theorem ContextUpdate.apply_provideService_shadows (key : ServiceKey) (near far : Val)
    (prev : Ctx) :
    ((ContextUpdate.provideService key near).apply
      ((ContextUpdate.provideService key far).apply prev)).getV key = some near :=
  ContextUpdate.apply_provideService_getV key near _

/-- `provideService` at one key leaves every other key's binding alone. -/
theorem ContextUpdate.apply_provideService_other (key : ServiceKey) (value : Val) (prev : Ctx)
    (key' : ServiceKey) (hne : key' ≠ key) :
    ((ContextUpdate.provideService key value).apply prev).getV key' = prev.getV key' :=
  Context.getV_addV_other prev key value key' hne

/-! ## The seven counterexample classes of `PLAN.md`, environment counterexamples

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

/-- CE 4 (missing lookups): the empty environment answers nothing — no default is invented. -/
example : (Context.empty : Ctx).getV scopeKey = none := rfl

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

/-! ## Separation gates at this instantiation (`docs/research/FRAMES-DAG.md` separation 4) -/

example : DecidableEq Val := inferInstance
example : DecidableEq Ctx := inferInstance
example : DecidableEq ContextUpdate := inferInstance

end Effect4.Machine.Env
