import Effect4.Machine.ContextMap
import Effect4.Machine.Fibers
import Effect4.Data.Row
import Effects.Algebra.Program

/-!
# Deep spike S5, part 1: the Context carrier (M4a, M4b) and the machine's `χ`

Status: design spike, 2026-09-03. Module `Deep.Context` of the non-default `Deep` library
(`lakefile.toml`, `srcDir = "workshop"`); built with `lake build Deep.Context`. Plan:
`docs/research/2026-09-03-deep-plan.md` row S5, rows M4a/M4b of §2 as split by
`docs/research/2026-09-03-deep-plan-review.md` findings 6 and 7. Order:
`docs/research/ENVIRONMENT-DAG.md` L1 (`Context/Requirement`, `Context/Service`) then L2
(`Context/Environment`). Report: `docs/research/2026-09-03-spike-s5-context-layer.md`.

Reused, never re-declared: `Effect4.ServiceKey`, `ServiceUniverse`, `ServiceKey.Carrier`,
`ServiceKey.transport`, `ServiceUniverse.exists_carrier_collision` (`src/Effect4/Machine/Key.lean`),
`Effect4.Row` (`src/Effect4/Data/Row.lean`), `Effects.Program` (`.lake/packages/effects`).

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
`ServiceUniverse U`, as `docs/research/ENVIRONMENT-DAG.md` requires. The machine instantiation is at
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

**U1b (2026-09-07).** `Val` is the shared carrier `Effect4.Store.Val` at the table of
`Machine/Value.lean`: a service context is `Value.serviceContext` over `pair key value` entries
(`entryStore`/`ofEntry` the entry codec, `encode`/`decode` the spine codec), the handles are
`Value.scope`/`Value.memoMap`/`Value.promise`/`Value.fiber`, an exit is `Value.exitOk`/
`Value.exitErr`, a memo hit's two-field answer is the carrier's `pair`. The `Env.Val`
namespace keeps the old spellings as patterns, the way `Machine/Stores.lean` spells
`Machine.Val`'s (`docs/research/2026-09-07-u1-cutover-dispatch.md`, U1b; the Layer machine's
own sites follow in the join, `docs/research/2026-09-07-join-dispatch.md`).
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
`ServiceKey.Carrier`, `ServiceKey.transport` (`docs/research/ENVIRONMENT-DAG.md` edge table). A service is
a key bound to a value of its carrier under a *supplied* universe: first-order at the key, with
the universe in the trusted-boundary position `Effect4.FlowAlphabet` occupies. -/

/-- The service-access signature: one operation per key, rc.112's `Effect.service(tag)` /
`Context.Tag` as an effect (`internal/effect.ts:2069-2070`: `withFiber(fiber =>
fromOption(Context.getOption(fiber.context, service)))`), whose answer is the key's carrier.
`PLAN.md`, environment / Service: "Prefer a derived `ServiceSignature U` and `request = Program.perform` over a
duplicate service program." -/
abbrev serviceSig (U : ServiceUniverse.{u}) : Effects.Signature.{0, u} where
  Op := ServiceKey
  Answer := fun key => ServiceKey.Carrier U key

/-- A program over the service-access signature: the reused `Effects.Program`. -/
abbrev ServiceProgram (U : ServiceUniverse.{u}) (A : Type u) : Type u :=
  Effects.Program (serviceSig U) A

/-- `Program.UsesOnly r p`: every operation `p` can perform, along every answer, names a key of
`r`. A predicate over the well-founded tree, not a computed row: `PLAN.md`, environment / Service, forbids claiming a
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
(`docs/research/ENVIRONMENT-DAG.md:23-25`, `src/Effect4/Machine/Key.lean:35-38`). -/
def UniverseAgreement (U V : ServiceUniverse.{u}) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → ServiceKey.Carrier U key = ServiceKey.Carrier V key

/-! ## M4b — `Context/Environment`: the rows and the programs over the map

The map, its operations and its laws are `Machine/ContextMap.lean` (moved in the join,
dependency cut L9; the names keep this namespace). What stays here reads the requirement
rows or runs a service program. -/

namespace Context

variable {U : ServiceUniverse.{u}}

/-- The requirement row an environment answers: its keys, canonical. -/
def keysRow (self : Context U) : Requirement := Row.normalize self.keys

/-- `Satisfies self r`: every key of the row is bound. -/
def Satisfies (self : Context U) (r : Requirement) : Prop :=
  ∀ key : ServiceKey, key ∈ r → (self.get? key).isSome = true

/-- The interpretation of a service program under an environment: every `vis key` is answered
by `get?`; a missing key stops the run with `none` — the frontier `Context.getUnsafe` throws at.
Total on `UsesOnly` programs under a satisfying environment (`interpret_total`). -/
def interpret (self : Context U) {A : Type u} : ServiceProgram U A → Option A
  | .pure value => some value
  | .vis key next => (self.get? key).bind fun value => interpret self (next value)

/-! ### `ENV-PG-CONTEXT`: the eleven laws of `PLAN.md`, environment / Context

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

end Context

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

/-! ### The alphabets as values

`Err`, `Defect` and `ServiceKey` are written on the shared carrier at the generated rule of
`Machine/Value.lean` (a case of a sum is `ctor i [args…]`, a structure `ctor 0 [fields…]`); the
cause carrier follows through `Value.cause`. -/

open Effect4.Store (Image)

def ofErr : Store.Val → Option Err
  | .ctor 0 [] => some .boom
  | .ctor 1 [.nat c] => some (.tag c)
  | _ => none

/-- `Env.Err` at the generated rule. -/
def Err.image : Image Err where
  toVal
    | .boom => .ctor 0 []
    | .tag c => .ctor 1 [.nat c]
  ofVal := ofErr
  ofVal_toVal e := by cases e <;> rfl
  ofVal_exact := by
    intro v e h
    unfold ofErr at h
    split at h <;> first | (injection h with h; subst h; rfl) | exact nomatch h

theorem Err.image_handleFree : Image.HandleFree Err.image := by
  intro e
  cases e <;> rfl

def ofDefect : Store.Val → Option Defect
  | .ctor 0 [] => some .notImplemented
  | .ctor 1 [] => some .asyncFiber
  | .ctor 2 [] => some .badName
  | .ctor 3 [k] => (serviceKeyImage.ofVal k).map .serviceNotFound
  | .ctor 4 [.nat i] => some (.unknownLayer i)
  | _ => none

/-- `Env.Defect` at the generated rule; `serviceNotFound key` carries the key's image. -/
def Defect.image : Image Defect where
  toVal
    | .notImplemented => .ctor 0 []
    | .asyncFiber => .ctor 1 []
    | .badName => .ctor 2 []
    | .serviceNotFound k => .ctor 3 [serviceKeyImage.toVal k]
    | .unknownLayer i => .ctor 4 [.nat i]
  ofVal := ofDefect
  ofVal_toVal d := by
    cases d
    case serviceNotFound k =>
      show (serviceKeyImage.ofVal (serviceKeyImage.toVal k)).map Defect.serviceNotFound =
        some (.serviceNotFound k)
      rw [Image.ofVal_toVal, Option.map_some]
    all_goals rfl
  ofVal_exact := by
    intro v d h
    unfold ofDefect at h
    split at h <;> first
      | (injection h with h; subst h; rfl)
      | (next k =>
          obtain ⟨key, hk, hj⟩ := Image.map_eq_some_inv h
          subst hj
          show Store.Val.ctor 3 [k] = Store.Val.ctor 3 [serviceKeyImage.toVal key]
          rw [serviceKeyImage.ofVal_exact hk])
      | exact nomatch h

theorem Defect.image_handleFree : Image.HandleFree Defect.image := by
  intro d
  cases d
  case serviceNotFound k =>
    show (Store.Val.ctor 3 [serviceKeyImage.toVal k]).handles = []
    rw [Store.Val.handles, Store.Val.handlesList_cons, serviceKeyImage_handleFree k,
      Store.Val.handlesList_nil]
    rfl
  all_goals rfl

/-- The cause carrier at this instantiation. -/
abbrev CauseV := Cause Err Defect FiberId Ann

/-- The cause carrier as a value (`Ann = Unit`): the reason list under `ctor 0`, each reason at
the generated rule, the interruptor recorded as a fiber *identity* (`Value.fiberIdentity`),
never as a handle. -/
def causeImage : Image CauseV :=
  Value.cause Err.image Defect.image Value.fiberIdentity Image.unit

theorem causeImage_handleFree : Image.HandleFree causeImage :=
  Value.cause_handleFree _ _ _ _ Err.image_handleFree Defect.image_handleFree
    Value.fiberIdentity_handleFree Image.unit_handleFree

namespace Val

/-- A reified failed `Exit`: the cause written by `causeImage` under `Value.exitErr`. -/
abbrev exitErr (cause : CauseV) : Val := Value.exitErr (causeImage.toVal cause)

end Val

/-- The exit carrier at this instantiation. -/
abbrev ExitV := Exit Val Err Defect FiberId Ann

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

/-! ## Separation gates at this instantiation (`docs/research/FRAMES-DAG.md` separation 4) -/

example : DecidableEq Val := inferInstance
example : DecidableEq Ctx := inferInstance
example : DecidableEq ContextUpdate := inferInstance

end Effect4.Machine.Env
