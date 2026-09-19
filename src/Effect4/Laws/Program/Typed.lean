import Effect4.Program.Typed
import Effect4.Program.ErrorImage
import Effect4.Laws.Program.ErrorQueries
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Template
import Effect4.Laws.Auto.Inversion

/-!
# Program.Typed — the value typing of the native cut (slice 1, lane 1)

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §2. Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 1–9. Batteries:
`Test/Program/TypedContract.lean` (the guards and the row `E4-TYPED-CE-002`; `E4-TYPED-CE-001`
is retired, below).

This module says which machine values (`src/Effect4/Machine/Stores.lean` `Val`) inhabit which
types of the program language (`src/Effect4/Program/Eff.lean` `Ty`), and proves three things
about the native route (`src/Effect4/Program/Native.lean`): a term that types
(`src/Effect4/Program/Typing/Rules.lean` `termTy`) and evaluates (`evalTerm`) evaluates to a value of
its type; a term that types evaluates; and a request value of a `sync` row's request type
decodes to a store operation (`NativeOp.syncOpOf`). Everything is
first-order and in `Type 0`; the only `String` operation is `BEq String` on a handle target,
which is at the ceiling (`src/Effect4/Program/Config.lean` header records the same fact).

Refusals of the value typing, each a `false` of `Val.hasTy` and not a silent one:

* `TYPED-FB-INT` — `.int` has no inhabitant: `Val.nat` is a `.nat`. `Ty.render` sends both to
  `number`; the printer's identification is not the typing's (`E4-TYPED-CE-002`).
* `.except`, `.never` and an unknown handle target have no inhabitant in this cut.

Since the host rows slice (2026-09-08, DB-15) `.string` is inhabited by the carrier's `str`
frame and `.option t` by `none` and a `some` of a `t`: strings are machine values on the
native route (`Native.lean` `Lit.toVal`), so every literal evaluates and totality carries no
`noStr` premise. The former refusal `TYPED-FB-STRING` and the register row `E4-TYPED-CE-001`
are retired, the ID kept.
The cause/failed-exit error column is checked through the shared `causeAdmits` fold (DI-62):
every typed failure has an image inhabiting `E`; defects and interruptions remain outside `E`.

Two facts of this toolchain shape the spelling. Core v4.33.1 has no `List.Forall₂` and this
tree carries no Mathlib, so `Fits` is its own two-constructor inductive of that shape. And
`Val.hasTy` recurses on the *type* — the exit, product, list and union arms all descend into
the type, and the value is matched inside each arm — so it is structural in `Ty`; a closed
instance is settled by `simp [Val.hasTy]`, by `rfl`, or by a `#guard`.

Added 2026-09-09 for row DI-17, beside the existing statements and changing none of them: the
allocation section (`Extends`, `extends_append`, `hasTy_mono`, `hasTy_append`) and the
environment relation at an allocation state (`FitsWith`, `FitsIn`, `Fits_iff_FitsIn_nil`,
`FitsWith.append`, `FitsIn.append`, `FitsIn.mono`). `Fits` and every theorem over it keep
their statements; `Fits_iff_FitsIn_nil` is the bridge. The `.fiberOf` membership arm remains
a handle check and reads neither result nor error column — that is a deliberate coarseness,
not a guarantee (`Test/Program/TypedContract.lean` pins it as a refusal).
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Values against types -/

/-! ### Inversions

What a value must be, given its type: the shapes `NativeOp.syncOpOf` (`Native.lean`) and the
atoms pattern-match on. Each unfolds the type's arm and splits the value's match. -/

/-- A `.unit` is `Val.unit`. -/
theorem Val.hasTy_unit_inv {v : Val} (h : Val.hasTy v .unit = true) : v = Val.unit := by
  simp only [Val.hasTy] at h
  split at h
  · rfl
  · exact nomatch h

/-- A `.nat` is a `Val.nat`. -/
theorem Val.hasTy_nat_inv {v : Val} (h : Val.hasTy v .nat = true) : ∃ n, v = Val.nat n := by
  simp only [Val.hasTy] at h
  split at h
  · next n => exact ⟨n, rfl⟩
  · exact nomatch h

/-- A `.bool` is a `Val.bool`. -/
theorem Val.hasTy_bool_inv {v : Val} (h : Val.hasTy v .bool = true) : ∃ b, v = Val.bool b := by
  simp only [Val.hasTy] at h
  split at h
  · next b => exact ⟨b, rfl⟩
  · exact nomatch h

/-- A `.string` is a `Val.str` (DB-15). -/
theorem Val.hasTy_string_inv {v : Val} (h : Val.hasTy v .string = true) : ∃ s, v = Val.str s := by
  simp only [Val.hasTy] at h
  split at h
  · next s => exact ⟨s, rfl⟩
  · exact nomatch h

/-- A `.lit s` is `Val.str s`. -/
theorem Val.hasTy_lit_inv {v : Val} {s : String} (h : Val.hasTy v (.lit s) = true) : v = Val.str s := by
  simp only [Val.hasTy] at h
  split at h
  · next s' =>
    obtain rfl : s' = s := beq_iff_eq.mp h
    rfl
  · exact nomatch h

/-- Option inversion retains the allocation table of its payload. -/
theorem Val.hasTy_option_inv_at {v : Val} {t : Ty} {allocated : List String}
    (h : Val.hasTy v (.option t) allocated = true) :
    v = Store.Val.none ∨ ∃ x, v = Store.Val.some x ∧ Val.hasTy x t allocated = true := by
  simp only [Val.hasTy] at h
  split at h
  · exact Or.inl rfl
  · next x => exact Or.inr ⟨x, rfl, h⟩
  · exact nomatch h

/-- An `.option t` is `none` or a `some` of a `t` (DB-15). -/
theorem Val.hasTy_option_inv {v : Val} {t : Ty} (h : Val.hasTy v (.option t) = true) :
    v = Store.Val.none ∨ ∃ x, v = Store.Val.some x ∧ Val.hasTy x t = true :=
  Val.hasTy_option_inv_at h

/-- A `NativeOp.refTy` is a `Val.cell`: the other handle spellings and the context's differ
from `"Ref.Ref<number>"`, decided on the literals; the kind byte is the cell's by
`HandleKind.ofByte?_exact`. -/
theorem Val.hasTy_refTy_inv {v : Val} (h : Val.hasTy v NativeOp.refTy = true) :
    ∃ k, v = Val.cell k := by
  simp only [Val.hasTy, NativeOp.refTy] at h
  split at h
  · next kind index =>
    split at h
    · next hk => exact ⟨⟨index⟩, by rw [HandleKind.ofByte?_exact hk]; rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact nomatch h
    · exact nomatch h
  · exact absurd (Bool.and_eq_true_iff.mp h).1 (by decide)

/-- A `NativeOp.deferredTy` is a `Val.promise`. -/
theorem Val.hasTy_deferredTy_inv {v : Val} (h : Val.hasTy v NativeOp.deferredTy = true) :
    ∃ k, v = Val.promise k := by
  simp only [Val.hasTy, NativeOp.deferredTy] at h
  split at h
  · next kind index =>
    split at h
    · exact absurd h (by decide)
    · next hk => exact ⟨⟨index⟩, by rw [HandleKind.ofByte?_exact hk]; rfl⟩
    · exact absurd h (by decide)
    · exact nomatch h
    · exact nomatch h
  · exact absurd (Bool.and_eq_true_iff.mp h).1 (by decide)

/-- Product membership retains the allocation table of both component values. -/
theorem Val.hasTy_prod_inv_at {v : Val} {a b : Ty} {allocated : List String}
    (h : Val.hasTy v (.prod a b) allocated = true) :
    ∃ x y, v = Val.tuple [x, y] ∧
      Val.hasTy x a allocated = true ∧ Val.hasTy y b allocated = true := by
  simp only [Val.hasTy] at h
  split at h
  · next x y => exact ⟨x, y, rfl, (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
  · exact nomatch h

/-- A `.prod a b` is the two-cell list (`Val.tuple`) of an `a` and a `b`. (U1: the two cells
were `exitCons x (exitCons y exitNil)`; they are the carrier's `list [x, y]`.) -/
theorem Val.hasTy_prod_inv {v : Val} {a b : Ty} (h : Val.hasTy v (.prod a b) = true) :
    ∃ x y, v = Val.tuple [x, y] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true :=
  Val.hasTy_prod_inv_at h

/-- A `.list ty` value produces an element list under `Val.asList?`, all of whose elements
satisfy `ty` at the same allocation table. -/
theorem Val.hasTy_list_inv_at {v : Val} {t : Ty} {allocated : List String}
    (h : Val.hasTy v (.list t) allocated = true) :
    ∃ vs, Val.asList? v = some vs ∧ ∀ x ∈ vs, Val.hasTy x t allocated = true := by
  simp only [Val.hasTy] at h
  split at h
  · next handles =>
    split at h
    · next ids hsnap =>
      simp only [Val.asList?, hsnap, Option.map_some]
      refine ⟨ids.map Val.fiber, rfl, ?_⟩
      intro x hx
      obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hx
      exact List.all_eq_true.mp h id hid
    · exact nomatch h
  · next values =>
    refine ⟨values, rfl, ?_⟩
    intro x hx
    exact List.all_eq_true.mp h x hx
  · exact nomatch h

/-- A `.list ty` value produces an element list under `Val.asList?`, all of whose elements
satisfy `ty`. -/
theorem Val.hasTy_list_inv {v : Val} {t : Ty}
    (h : Val.hasTy v (.list t) = true) :
    ∃ vs, Val.asList? v = some vs ∧ ∀ x ∈ vs, Val.hasTy x t = true :=
  Val.hasTy_list_inv_at h


/-! ## Allocation

Row DI-17. `Val.hasTy` takes an allocation table (`allocated : List String`, the target
spelling minted at each external index) since the host rows slice; only the `.handle` arm
reads it, and it reads it by index. The external store never rewrites an index it has
already written — a registration appends — so the table only ever grows to the right, and
membership at a smaller table is membership at every larger one.

`Extends` is that growth as a relation on tables, stated by index rather than as `<+:` so it
is exactly what the `.handle` arm needs and nothing more. It is *not* a semantic type order:
a target spelling says which kind of resource a handle names, never whether that resource is
still open or which run minted it (`Test/Program/TypedContract.lean` pins both facts).
Source of the proofs: the foundation probe `Allocation.lean` (2026-09-09), reproved here
against the production definition unchanged. `Extends` and `extends_append` live in
`Effect4.Laws.Program.TyView` with the algebra conditions. -/

/-! ## The error folds

Row DI-62. `reasonAdmits` and `causeAdmits` (`src/Effect4/Program/ErrorImage.lean`) take the
membership predicate as a parameter, and they only ever apply it at the one type they are
folding at. The two congruences below say exactly that, and they are what the S2 cutover
needs: the `.causeOf e` arm of `Val.hasTy` must pass a *closed* predicate
`fun v _ => Val.hasTy v e allocated` rather than `fun v t => Val.hasTy v t allocated`, because
Lean's structural recursion has to see the recursive call at the subterm `e` and cannot see
through a lambda-bound type. These lemmas make the two spellings interchangeable afterwards,
so the arm and the `errAdmits` instantiation stay one fold read two ways.

The pointwise congruence and monotonicity laws serve both membership uses without storing
functions in program syntax. -/

/-- The reason fold only reads its predicate at the type it folds at. -/
theorem reasonAdmits_congr {f g : Val → Ty → Bool} (ty : Ty) (h : ∀ v, f v ty = g v ty)
    (r : Reason Err Defect FiberId Ann) :
    reasonAdmits f ty r = reasonAdmits g ty r := by
  cases r with
  | fail e _ =>
    cases e with
    | boom => rfl
    | tag n => exact h _
    | tagged t m => exact h _
    | text s => exact h _
  | die _ _ => rfl
  | interrupt _ _ => rfl

/-- The cause fold only reads its predicate at the type it folds at. -/
theorem causeAdmits_congr {f g : Val → Ty → Bool} (ty : Ty) (h : ∀ v, f v ty = g v ty)
    (c : CauseV) : causeAdmits f ty c = causeAdmits g ty c := by
  unfold causeAdmits
  generalize c.reasons = rs
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    rw [List.all_cons, List.all_cons, ih, reasonAdmits_congr ty h r]

/-- A pointwise enlargement of membership enlarges reason admission at the selected type. -/
theorem reasonAdmits_mono {f g : Val → Ty → Bool} (ty : Ty)
    (h : ∀ v, f v ty = true → g v ty = true) (r : Reason Err Defect FiberId Ann) :
    reasonAdmits f ty r = true → reasonAdmits g ty r = true := by
  cases r with
  | fail e _ =>
    cases e with
    | boom => intro impossible; cases impossible
    | tag n => exact h _
    | tagged t m => exact h _
    | text s => exact h _
  | die _ _ => exact id
  | interrupt _ _ => exact id

/-- Cause admission is monotone in the pointwise membership predicate. -/
theorem causeAdmits_mono {f g : Val → Ty → Bool} (ty : Ty)
    (h : ∀ v, f v ty = true → g v ty = true) (c : CauseV) :
    causeAdmits f ty c = true → causeAdmits g ty c = true := by
  intro hc
  apply List.all_eq_true.mpr
  intro r hr
  exact reasonAdmits_mono ty h r (List.all_eq_true.mp hc r hr)

/-- Row DI-62. Reified-cause membership uses the same allocation-aware cause fold. -/
theorem hasTy_causeOf_exitErr (c : CauseV) (e : Ty) (allocated : List String) :
    Val.hasTy (Val.exitErr c) (.causeOf e) allocated =
      causeAdmits (fun v t => Val.hasTy v t allocated) e c := by
  change (match Val.cause? (Val.exitErr c) with
    | some cause => causeAdmits (fun v _ => Val.hasTy v e allocated) e cause
    | none => false) = _
  rw [Val.cause?_exitErr]
  exact causeAdmits_congr e (fun _ => rfl) c

/-- Row DI-62. A failed exit checks its error column at its actual allocation table. -/
theorem hasTy_exitErr (c : CauseV) (a e : Ty) (allocated : List String) :
    Val.hasTy (Val.exitErr c) (.exitOf a e) allocated =
      causeAdmits (fun v t => Val.hasTy v t allocated) e c := by
  change (match causeImage.ofVal (causeImage.toVal c) with
    | some cause => causeAdmits (fun v _ => Val.hasTy v e allocated) e cause
    | none => false) = _
  rw [causeImage.ofVal_toVal]
  exact causeAdmits_congr e (fun _ => rfl) c

/-- The retained public wrapper is the default-allocation cause membership arm. -/
theorem hasTy_causeOf_eq_hasTyCause (v : Val) (e : Ty) :
    Val.hasTy v (.causeOf e) = hasTyCause v e := by
  aesop

/-- The registration case of `hasTy_mono`: a value typed before an allocation is typed
after it. `hasTy_mono` itself lives in `Effect4.Laws.Program.Admits` as the corollary of
`cata_admits_extend`. -/
theorem hasTy_append (ty : Ty) (v : Val) (a added : List String)
    (h : Val.hasTy v ty a = true) : Val.hasTy v ty (a ++ added) = true :=
  hasTy_mono ty v a (a ++ added) (extends_append a added) h

/-! ## Environments -/

/-- A positional environment fits a typing environment: `List.Forall₂` of `hasTy` (plan §2.1,
ENSURES 2), spelled as its own inductive of the same two constructors because core v4.33.1
carries no `List.Forall₂` and this tree carries no Mathlib. -/
inductive Fits : List Val → TyEnv → Prop
  | nil : Fits [] []
  | cons {v : Val} {t : Ty} {env : List Val} {tys : TyEnv} :
      Val.hasTy v t = true → Fits env tys → Fits (v :: env) (t :: tys)

/-- The value at a position has the type at that position (plan §2.2). -/
theorem Fits.get? {env : List Val} {tys : TyEnv} (h : Fits env tys) {i : Nat} {v : Val}
    {t : Ty} (hv : env[i]? = some v) (ht : tys[i]? = some t) : Val.hasTy v t = true := by
  induction h generalizing i with
  | nil => simp at hv
  | cons hvt _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv ht
      subst hv; subst ht; exact hvt
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv ht
      exact ih hv ht

/-- The two environments have one length (plan §2.2). -/
theorem Fits.length {env : List Val} {tys : TyEnv} (h : Fits env tys) :
    env.length = tys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Appending an answer of the answer's type keeps the fit (plan §2.2): D1's convention, every
node passes its scope forward and an answer is appended (`Eff.lean:17-19`). -/
theorem Fits.append {env : List Val} {tys : TyEnv} (h : Fits env tys) {v : Val} {t : Ty}
    (hvt : Val.hasTy v t = true) : Fits (env ++ [v]) (tys ++ [t]) := by
  induction h with
  | nil => exact Fits.cons hvt Fits.nil
  | cons hx _ ih => exact Fits.cons hx ih

/-- A fit against one type is one value of that type. -/
theorem Fits.singleton_inv {vs : List Val} {t : Ty} (h : Fits vs [t]) :
    ∃ v, vs = [v] ∧ Val.hasTy v t = true := by
  cases h with
  | cons hv hrest => cases hrest; exact ⟨_, rfl, hv⟩

/-- A fit against strings only is a list whose every member fits `.string` (the `strings`
atom's premise). -/
theorem Fits.all_string {vs : List Val} {tys : TyEnv} (h : Fits vs tys)
    (hall : tys.all (· == Ty.string) = true) : ∀ v ∈ vs, Val.hasTy v .string = true := by
  induction h with
  | nil => intro v hv; cases hv
  | cons hv _ ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    obtain ⟨rfl, hrest⟩ := hall
    intro w hw
    cases hw with
    | head => exact hv
    | tail _ hw => exact ih hrest w hw

/-- Under subsumption (DI-15, the 2026-09-12 clause): values fitting types that are each a
subtype of one type are values of that type, by `hasTy_sub`. The variadic scheme's premise
(`NativeAtom.sound_of_variadic`); `strings` is its one consumer today. -/
theorem Fits.all_sub {vs : List Val} {tys : TyEnv} (h : Fits vs tys) {t : Ty}
    (hall : tys.all (·.sub t) = true) : ∀ v ∈ vs, Val.hasTy v t = true := by
  induction h with
  | nil => intro v hv; cases hv
  | cons hv _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hsub, hrest⟩ := hall
    intro w hw
    cases hw with
    | head => exact hasTy_sub _ _ _ [] hsub hv
    | tail _ hw => exact ih hrest w hw

/-- `Fits.all_sub` at `.string`: the statement the `Effect4.Atoms` bank registers. -/
theorem Fits.all_sub_string {vs : List Val} {tys : TyEnv} (h : Fits vs tys)
    (hall : tys.all (·.sub Ty.string) = true) : ∀ v ∈ vs, Val.hasTy v .string = true :=
  h.all_sub hall

/-- Pointwise subsumption: an environment fitting `tys` fits any `params` each of whose
entries the corresponding `tys` entry is below. The fixed-signature scheme's premise
(`NativeAtom.sound_of_mono`), and the one place `hasTy_sub` is applied for every atom at
once — the twenty hand blocks applied it per atom, per argument. -/
theorem Fits.sub {vs : List Val} {tys params : TyEnv} (h : Fits vs tys)
    (hlen : tys.length = params.length)
    (hall : (tys.zip params).all (fun (a, e) => a.sub e) = true) : Fits vs params := by
  induction h generalizing params with
  | nil =>
    cases params with
    | nil => exact .nil
    | cons _ _ => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
  | cons hv _ ih =>
    cases params with
    | nil => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
    | cons p ps =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact .cons (hasTy_sub _ _ _ [] hall.1 hv) (ih hlen hall.2)

/-- A fit against two types is two values of those types. -/
theorem Fits.pair_inv {vs : List Val} {a b : Ty} (h : Fits vs [a, b]) :
    ∃ x y, vs = [x, y] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' => cases hrest'; exact ⟨_, _, rfl, hx, hy⟩

/-- A fit against an empty environment is an empty list of values. -/
theorem Fits.nil_inv {vs : List Val} (h : Fits vs []) : vs = [] := by
  cases h; rfl

/-- A fit against three types is three values of those types. -/
theorem Fits.triple_inv {vs : List Val} {a b c : Ty} (h : Fits vs [a, b, c]) :
    ∃ x y z, vs = [x, y, z] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true ∧ Val.hasTy z c = true := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' =>
      cases hrest' with
      | cons hz hrest'' => cases hrest''; exact ⟨_, _, _, rfl, hx, hy, hz⟩

/-- A successful list match puts every argument at its parameter's instance under the bindings
of the LAST step: each guard holds at its own step's bindings (`matchTemplate_sound`), and every
later step only widens them (`Ty.matchTemplateArgs_widens`, `Ty.hasTy_instantiate_widens`).
The `poly` scheme's premise (`NativeAtom.sound_of_poly`), for either rule of `join`. -/
theorem Fits.instantiate {σ₀ σ : Ty.Subst} {ps : TyEnv} {join : Bool} :
    ∀ {vs : List Val} {tys : TyEnv}, Ty.matchTemplateArgs σ₀ ps tys join = some σ →
      Fits vs tys → Fits vs (ps.map (Ty.instantiate σ)) := by
  induction ps generalizing σ₀ with
  | nil =>
    intro vs tys hmatch hfit
    cases tys with
    | nil => cases hfit; exact .nil
    | cons _ _ => exact nomatch hmatch
  | cons p ps ih =>
    intro vs tys hmatch hfit
    cases tys with
    | nil => exact nomatch hmatch
    | cons r rs =>
      simp only [Ty.matchTemplateArgs, Option.bind_eq_some_iff] at hmatch
      obtain ⟨σ₁, h₁, hrest⟩ := hmatch
      cases hfit with
      | cons hv hfit' =>
        exact .cons (Ty.hasTy_instantiate_widens (Ty.matchTemplateArgs_widens hrest) p _ []
          (hasTy_sub r _ _ [] (Ty.matchTemplate_sound σ₀ p r σ₁ h₁) hv)) (ih hrest hfit')

/-! ### Environments at an allocation state

Row DI-17. `Fits` above fixes the allocation table at the default `[]`, so it refuses an
environment holding a live external handle however the handle was minted: the `.handle` arm
looks the index up in an empty table (`Test/Program/TypedContract.lean` pins the pair). The
generalisation is one relation with the membership predicate as a parameter, and `FitsIn` is
its instance at a table.

This is a proof abstraction with the same two constructors as `Fits`, not a second program
representation and not a change to `Fits`: `Fits` keeps its statement, every theorem stated
over it keeps its statement, and `Fits_iff_FitsIn_nil` is the bridge. Source: scout B's
`FitsWith`/`FitsIn` (`docs/research/2026-09-09-scout-proof-statements.md` §5), reproved here. -/

/-- A positional environment fits a typing environment at an arbitrary notion of membership.
Core v4.33.1 carries no `List.Forall₂` and this tree carries no Mathlib, so this is its own
two-constructor inductive, exactly as `Fits` is. -/
inductive FitsWith (holds : Val → Ty → Prop) : List Val → TyEnv → Prop
  | nil : FitsWith holds [] []
  | cons {v : Val} {t : Ty} {vs : List Val} {ts : TyEnv} :
      holds v t → FitsWith holds vs ts → FitsWith holds (v :: vs) (t :: ts)

/-- The environment relation at an allocation state: `Fits` with the table supplied. -/
abbrev FitsIn (allocated : List String) := FitsWith (fun v t => Val.hasTy v t allocated = true)

/-- `Fits` is exactly `FitsIn []`: the existing relation is the empty-allocation instance of
the generalisation, so nothing stated over `Fits` weakens or strengthens. -/
theorem Fits_iff_FitsIn_nil (vs : List Val) (ts : TyEnv) : Fits vs ts ↔ FitsIn [] vs ts := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons hv ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons hv ih

/-- Appending an answer of the answer's type keeps the fit, at any membership (`Fits.append`
generalised; D1's convention, every node passes its scope forward and an answer is
appended). -/
theorem FitsWith.append {holds : Val → Ty → Prop} {vs : List Val} {ts : TyEnv}
    (hf : FitsWith holds vs ts) {v : Val} {t : Ty} (hv : holds v t) :
    FitsWith holds (vs ++ [v]) (ts ++ [t]) := by
  induction hf with
  | nil => exact .cons hv .nil
  | cons h _ ih => exact .cons h ih

/-- `FitsWith.append` at an allocation state. -/
theorem FitsIn.append {allocated : List String} {vs : List Val} {ts : TyEnv}
    (hf : FitsIn allocated vs ts) {v : Val} {t : Ty}
    (hv : Val.hasTy v t allocated = true) : FitsIn allocated (vs ++ [v]) (ts ++ [t]) :=
  FitsWith.append hf hv

/-- A fit survives a registration: `hasTy_mono` pointwise. This is the environment half of
the allocation row — an external registration extends the table and no value already in
scope loses its type. -/
theorem FitsIn.mono {a b : List String} {vs : List Val} {ts : TyEnv}
    (ext : Extends a b) (h : FitsIn a vs ts) : FitsIn b vs ts := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (hasTy_mono _ _ a b ext hv) ih

/-! ## Literals -/

/-- A literal's value has the literal's type (`Native.lean` `Lit.toVal` against `Eff.lean`
`Lit.ty`; plan §2.2, ENSURES 4). -/
theorem Lit.toVal_hasTy (l : Lit) (v : Val) (h : l.toVal = some v) : Val.hasTy v l.ty = true := by
  cases l with
  | unit => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | nat n => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | bool b => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]
  | str s => simp only [Lit.toVal, Option.some.injEq] at h; subst h; simp [Lit.ty, Val.hasTy]

/-- Every literal evaluates (`Native.lean` `Lit.toVal` answers `some` on every constructor
since DB-15; ENSURES 4). -/
theorem Lit.toVal_isSome (l : Lit) : l.toVal.isSome = true := by
  cases l <;> rfl

/-- The literal rule is sound for the literal's own value: a `str s` inhabits `lit s` as it
inhabits `string`, and every other literal's argument type is its `Lit.ty` (`litArgTy`). -/
theorem Lit.toVal_hasTy_arg (const : Bool) (l : Lit) (v : Val) (h : l.toVal = some v) :
    Val.hasTy v (litArgTy const l) = true := by
  cases l with
  | str s =>
    cases Option.some.inj h
    cases const
    · simp only [litArgTy, Bool.false_eq_true, ↓reduceIte, Val.hasTy]
    · -- `s == s` on a string: `beq_iff_eq`, never `simp`'s string lemmas (`Classical.choice`)
      simp only [litArgTy, ↓reduceIte, Val.hasTy]
      exact beq_iff_eq.mpr rfl
  | unit => cases Option.some.inj h; rfl
  | nat n => cases Option.some.inj h; rfl
  | bool b => cases Option.some.inj h; rfl

/-! ## Atoms -/

/-- Projecting a typed product union uses the existing evaluator and retains membership
at the same allocation table. The bottom case is vacuous, not a fabricated value. -/
theorem NativeAtom.projectProduct_typed (second : Bool) (input output : Ty)
    (v : Val) (allocated : List String)
    (hproject : NativeAtom.projectProduct second input = some output)
    (hv : Val.hasTy v input allocated = true) :
    ∃ result, NativeAtom.eval (if second then .snd else .fst) [v] = some result ∧
      Val.hasTy result output allocated = true := by
  induction input generalizing output with
  | never => simp only [Val.hasTy, Bool.false_eq_true] at hv
  | prod a b =>
    simp only [NativeAtom.projectProduct] at hproject
    cases hproject
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv_at hv
    cases second
    · exact ⟨x, rfl, hx⟩
    · exact ⟨y, rfl, hy⟩
  | union a b iha ihb =>
    cases hleft : NativeAtom.projectProduct second a with
    | none => simp only [NativeAtom.projectProduct, hleft, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at hproject
    | some left =>
      cases hright : NativeAtom.projectProduct second b with
      | none => simp only [NativeAtom.projectProduct, hleft, hright,
          Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at hproject
      | some right =>
        simp only [NativeAtom.projectProduct, hleft, hright, Option.bind_eq_bind,
          Option.bind_some] at hproject
        cases hproject
        rcases Bool.or_eq_true_iff.mp hv with ha | hb
        · obtain ⟨result, heval, htyped⟩ := iha left hleft ha
          exact ⟨result, heval, Ty.hasTy_join_left left right result allocated htyped⟩
        · obtain ⟨result, heval, htyped⟩ := ihb right hright hb
          exact ⟨result, heval, Ty.hasTy_join_right left right result allocated htyped⟩
  | _ => simp only [NativeAtom.projectProduct, reduceCtorEq] at hproject

/-- DI-78 option equations describe selection, independently of typing. -/
theorem NativeAtom.isSome_none : NativeAtom.eval .isSome [Store.Val.none] = some (.bool false) := rfl
theorem NativeAtom.isSome_some (v : Val) :
    NativeAtom.eval .isSome [Store.Val.some v] = some (.bool true) := rfl
theorem NativeAtom.getOrElse_none (fallback : Val) :
    NativeAtom.eval .getOrElse [Store.Val.none, fallback] = some fallback := rfl
theorem NativeAtom.getOrElse_some (v fallback : Val) :
    NativeAtom.eval .getOrElse [Store.Val.some v, fallback] = some v := rfl

/-! ### Atom soundness, once per scheme

`nativeAtom_typed` was one theorem of twenty hand blocks, each re-deriving the same three
facts: that `typeOf`'s guard held, that subsumption at each parameter put the value in the
parameter's own frame, and that the atom's `eval` answered in the answer's frame. The first
two are properties of the *scheme* (`NativeAtom.Scheme`), not of the atom, so they are proved
once per scheme here; what is left per atom is the third, which is the atom's own content and
nothing else. -/

/-- The per-atom obligation: at any argument types the atom accepts, an environment fitting
those types evaluates, and the answer inhabits the answer type.

Not decidable at any strength — it quantifies over all `Ty` and all `Val`, both infinite —
which is why the table's *structural* obligations are a separate, decided fact
(`NativeAtom.atom_table_wf`). -/
def NativeAtom.Sound (a : NativeAtom) : Prop :=
  ∀ (tys : List Ty) (ty : Ty) (vs : List Val),
    a.typeOf tys = some ty → Fits vs tys →
      ∃ v, NativeAtom.eval a vs = some v ∧ Val.hasTy v ty = true

namespace NativeAtom

/-- A fixed signature. Subsumption at every parameter is discharged here, once, so the atom
answers only on values of the parameters' own types. -/
theorem sound_of_mono {a : NativeAtom} {params : TyEnv} {answer : Ty}
    (hs : (spec a).scheme = .mono params answer)
    (hev : ∀ vs, Fits vs params → ∃ v, eval a vs = some v ∧ Val.hasTy v answer = true) :
    Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply, monoApply] at hty
  split at hty
  · next hguard =>
    cases hty
    exact hev vs (hfit.sub hguard.1 hguard.2)
  · exact nomatch hty

/-- Any number of arguments at one parameter type. -/
theorem sound_of_variadic {a : NativeAtom} {param answer : Ty}
    (hs : (spec a).scheme = .variadic param answer)
    (hev : ∀ vs, (∀ v ∈ vs, Val.hasTy v param = true) →
             ∃ v, eval a vs = some v ∧ Val.hasTy v answer = true) : Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply] at hty
  split at hty
  · next hall =>
    cases hty
    exact hev vs (hfit.all_sub hall)
  · exact nomatch hty

/-- A named rule keeps its own content; the scheme only routes to it. -/
theorem sound_of_custom {a : NativeAtom} {tag : CustomScheme}
    (hs : (spec a).scheme = .custom tag)
    (hev : ∀ tys ty vs, tag.apply tys = some ty → Fits vs tys →
             ∃ v, eval a vs = some v ∧ Val.hasTy v ty = true) : Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply] at hty
  exact hev tys ty vs hty hfit

/-- A template. What is left per atom is its content at the parameters' instances, for every
substitution: the step from "the arguments fit `tys`" to "they fit the parameters instantiated
at the final bindings" is `Fits.instantiate`, once, for either rule of `join`. Quantifying
over every σ is stronger than `Scheme.apply` needs, and every template here is parametric in
what it binds, so nothing is lost. -/
theorem sound_of_poly {a : NativeAtom} {params : TyEnv} {answer : Ty} {join : Bool}
    (hs : (spec a).scheme = .poly params answer join)
    (hev : ∀ (σ : Ty.Subst) (vs : List Val), Fits vs (params.map (Ty.instantiate σ)) →
             ∃ v, eval a vs = some v ∧ Val.hasTy v (Ty.instantiate σ answer) = true) :
    Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply] at hty
  obtain ⟨σ, hmatch, rfl⟩ := Option.map_eq_some_iff.mp hty
  exact hev σ vs (hfit.instantiate hmatch)

/-- The alternative a `findSome?` over fixed signatures hit. -/
theorem findSome?_monoApply {alts : List (TyEnv × Ty)} {tys : List Ty} {ty : Ty}
    (h : alts.findSome? (fun c => monoApply c.1 c.2 tys) = some ty) :
    ∃ params answer, (params, answer) ∈ alts ∧ monoApply params answer tys = some ty := by
  induction alts with
  | nil => exact nomatch h
  | cons c cs ih =>
    obtain ⟨params, answer⟩ := c
    simp only [List.findSome?_cons] at h
    split at h
    · next hc =>
      cases h
      exact ⟨params, answer, List.mem_cons_self, hc⟩
    · next hc =>
      obtain ⟨p, ans, hmem, heq⟩ := ih h
      exact ⟨p, ans, List.mem_cons_of_mem _ hmem, heq⟩

/-- Alternative fixed signatures, first hit wins. -/
theorem sound_of_alts {a : NativeAtom} {alts : List (TyEnv × Ty)}
    (hs : (spec a).scheme = .alts alts)
    (hev : ∀ params answer, (params, answer) ∈ alts → ∀ vs, Fits vs params →
             ∃ v, eval a vs = some v ∧ Val.hasTy v answer = true) : Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply] at hty
  obtain ⟨params, answer, hmem, heq⟩ := findSome?_monoApply hty
  simp only [monoApply] at heq
  split at heq
  · next hguard =>
    cases heq
    exact hev _ _ hmem vs (hfit.sub hguard.1 hguard.2)
  · exact nomatch heq

/-! The evaluation shapes the monomorphic atoms have. A shape names the parameter frames and
the answer frame; `sound_of_shape` inverts the fit once per shape, so an atom of that shape
costs one line naming its kernel rather than a block re-deriving the inversion. -/

/-- The monomorphic evaluation shapes present in the alphabet. -/
inductive Shape
  | nat1 | natTest | bool1 | nat2 | natRel | bool2 | strTest | str2
deriving DecidableEq, Repr

def Shape.params : Shape → TyEnv
  | .nat1 | .natTest => [.nat]
  | .bool1 => [.bool]
  | .nat2 | .natRel => [.nat, .nat]
  | .bool2 => [.bool, .bool]
  | .strTest => [.string, .unknown]
  | .str2 => [.string, .string]

def Shape.answer : Shape → Ty
  | .nat1 | .nat2 => .nat
  | .natTest | .bool1 | .natRel | .bool2 | .strTest => .bool
  | .str2 => .string

/-- What an atom of this shape must do: answer in the answer's frame on the frames its
parameters admit. This is the whole per-atom content of a monomorphic atom. -/
def Shape.holds (s : Shape) (a : NativeAtom) : Prop :=
  match s with
  | .nat1 => ∀ m : Nat, ∃ n : Nat, eval a [Val.nat m] = some (Val.nat n)
  | .natTest => ∀ m : Nat, ∃ b : Bool, eval a [Val.nat m] = some (Val.bool b)
  | .bool1 => ∀ x : Bool, ∃ b : Bool, eval a [Val.bool x] = some (Val.bool b)
  | .nat2 => ∀ m k : Nat, ∃ n : Nat, eval a [Val.nat m, Val.nat k] = some (Val.nat n)
  | .natRel => ∀ m k : Nat, ∃ b : Bool, eval a [Val.nat m, Val.nat k] = some (Val.bool b)
  | .bool2 => ∀ x y : Bool, ∃ b : Bool, eval a [Val.bool x, Val.bool y] = some (Val.bool b)
  | .strTest => ∀ (t : String) (v : Val), ∃ b : Bool, eval a [Val.str t, v] = some (Val.bool b)
  | .str2 => ∀ s t : String, ∃ u : String, eval a [Val.str s, Val.str t] = some (Val.str u)

/-- The inversion of a shape's parameter fit, once per shape. `strTest`'s second parameter is
the top (decisions row 46), which every value inhabits, so its second argument is unconstrained
— which is exactly what the tag test wants. -/
theorem sound_of_shape {a : NativeAtom} (s : Shape)
    (hs : (spec a).scheme = .mono s.params s.answer) (hev : s.holds a) : Sound a := by
  refine sound_of_mono hs ?_
  intro vs hfit
  cases s with
  | nat1 | natTest =>
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hv
    obtain ⟨_, he⟩ := hev m
    exact ⟨_, he, rfl⟩
  | bool1 =>
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨x, rfl⟩ := Val.hasTy_bool_inv hv
    obtain ⟨_, he⟩ := hev x
    exact ⟨_, he, rfl⟩
  | nat2 | natRel =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨k, rfl⟩ := Val.hasTy_nat_inv hy
    obtain ⟨_, he⟩ := hev m k
    exact ⟨_, he, rfl⟩
  | bool2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨p, rfl⟩ := Val.hasTy_bool_inv hx
    obtain ⟨q, rfl⟩ := Val.hasTy_bool_inv hy
    obtain ⟨_, he⟩ := hev p q
    exact ⟨_, he, rfl⟩
  | strTest =>
    obtain ⟨x, y, rfl, hx, _⟩ := hfit.pair_inv
    obtain ⟨t, rfl⟩ := Val.hasTy_string_inv hx
    obtain ⟨_, he⟩ := hev t y
    exact ⟨_, he, rfl⟩
  | str2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨s, rfl⟩ := Val.hasTy_string_inv hx
    obtain ⟨t, rfl⟩ := Val.hasTy_string_inv hy
    obtain ⟨_, he⟩ := hev s t
    exact ⟨_, he, rfl⟩

/-- Every atom is sound: one line where a shape carries the argument, a short block where the
atom's evaluation reads its argument's own frame (a projection, a cause query, an option, a
list), and no atom re-derives its scheme's guard. -/
theorem sound (a : NativeAtom) : Sound a := by
  cases a with
  | succ => exact sound_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩)
  | pred => exact sound_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩)
  | isZero => exact sound_of_shape .natTest rfl (fun _ => ⟨_, rfl⟩)
  | boolNot => exact sound_of_shape .bool1 rfl (fun _ => ⟨_, rfl⟩)
  | add => exact sound_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | lt => exact sound_of_shape .natRel rfl (fun _ _ => ⟨_, rfl⟩)
  | boolOr => exact sound_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩)
  | boolAnd => exact sound_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩)
  | tagIs => exact sound_of_shape .strTest rfl (fun _ _ => ⟨_, rfl⟩)
  | strings =>
    refine sound_of_variadic rfl ?_
    intro vs hall
    have hstr : ∀ v ∈ vs, ∃ s, v = Val.str s := fun v hv => Val.hasTy_string_inv (hall v hv)
    refine ⟨Val.list vs, ?_, ?_⟩
    · rw [NativeAtom.eval, stringsAtom, if_pos]
      rw [List.all_eq_true]
      intro v hv
      obtain ⟨s, rfl⟩ := hstr v hv
      rfl
    · simp only [Val.hasTy, List.all_eq_true]
      intro v hv
      obtain ⟨s, rfl⟩ := hstr v hv
      rfl
  | eq =>
    refine sound_of_alts rfl ?_
    intro params answer hmem vs hfit
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmem
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
      obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
      exact ⟨_, rfl, rfl⟩
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨s, rfl⟩ := Val.hasTy_string_inv hx
      obtain ⟨t, rfl⟩ := Val.hasTy_string_inv hy
      exact ⟨_, rfl, rfl⟩
  | pair =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨u, w, rfl, hu, hw⟩ := hfit.pair_inv
    exact ⟨Val.list [u, w], rfl, Bool.and_eq_true_iff.mpr ⟨hu, hw⟩⟩
  | fst =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, projectRule] at hty
    split at hty
    · obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
      exact projectProduct_typed false _ _ v [] hty hv
    all_goals exact nomatch hty
  | snd =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, projectRule] at hty
    split at hty
    · obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
      exact projectProduct_typed true _ _ v [] hty hv
    all_goals exact nomatch hty
  | causeIsFail =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, causeTestRule] at hty
    split at hty
    · obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      exact queryTag_typed .fail value _ error [] hdomain hv
    all_goals exact nomatch hty
  | causeIsDie =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, causeTestRule] at hty
    split at hty
    · obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      exact queryTag_typed .die value _ error [] hdomain hv
    all_goals exact nomatch hty
  | causeIsInterrupt =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, causeTestRule] at hty
    split at hty
    · obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      exact queryTag_typed .interrupt value _ error [] hdomain hv
    all_goals exact nomatch hty
  | causeError =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, causeErrorRule] at hty
    split at hty
    · obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
      exact queryError_typed value _ error [] hdomain hv
    all_goals exact nomatch hty
  | isSome =>
    refine sound_of_mono rfl ?_
    intro vs hfit
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    rcases Val.hasTy_option_inv_at hv with rfl | ⟨u, rfl, _⟩
    · exact ⟨Val.bool false, rfl, rfl⟩
    · exact ⟨Val.bool true, rfl, rfl⟩
  | getOrElse =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨u, w, rfl, hu, hw⟩ := hfit.pair_inv
    rcases Val.hasTy_option_inv_at hu with rfl | ⟨x, rfl, hx⟩
    · exact ⟨w, rfl, hw⟩
    · exact ⟨x, rfl, hx⟩
  | ite =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨c, t, f, rfl, hc, ht, hf⟩ := hfit.triple_inv
    obtain ⟨b, rfl⟩ := Val.hasTy_bool_inv hc
    refine ⟨if b then t else f, rfl, ?_⟩
    cases b
    · exact hf
    · exact ht
  | optSome =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    exact ⟨Store.Val.some v, rfl, hv⟩
  | optNone => exact sound_of_mono rfl fun vs hfit => by cases hfit.nil_inv; exact ⟨_, rfl, rfl⟩
  | mul => exact sound_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | listNil => exact sound_of_mono rfl fun vs hfit => by cases hfit.nil_inv; exact ⟨_, rfl, rfl⟩
  | listCons =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨x, xs, rfl, hx, hxs⟩ := hfit.pair_inv
    obtain ⟨elems, hl, helems⟩ := Val.hasTy_list_inv hxs
    exact ⟨.list (x :: elems), by simp only [eval, hl, Option.map_some],
      Bool.and_eq_true_iff.mpr ⟨hx, List.all_eq_true.mpr helems⟩⟩
  | listGet =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := Val.hasTy_list_inv hxs
    cases hn : elems[n]? with
    | none => exact ⟨Store.Val.none, by simp only [eval, hl, hn, Option.map_some], rfl⟩
    | some e =>
      exact ⟨Store.Val.some e, by simp only [eval, hl, hn, Option.map_some],
        helems e (List.mem_of_getElem? hn)⟩
  | listLength =>
    refine sound_of_mono rfl fun vs hfit => ?_
    obtain ⟨xs, rfl, hxs⟩ := hfit.singleton_inv
    obtain ⟨elems, hl, _⟩ := Val.hasTy_list_inv hxs
    exact ⟨Val.nat elems.length, by simp only [eval, hl, Option.map_some], rfl⟩
  | listAppend =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := hfit.pair_inv
    obtain ⟨front, hf, hfront⟩ := Val.hasTy_list_inv hxs
    obtain ⟨back, hb, hback⟩ := Val.hasTy_list_inv hys
    exact ⟨.list (front ++ back), by simp only [eval, hf, hb, Option.bind_some, Option.map_some],
      List.all_eq_true.mpr fun y hy => (List.mem_append.mp hy).elim (hfront y) (hback y)⟩
  | natSub => exact sound_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | natDiv => exact sound_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | natMod => exact sound_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | strConcat => exact sound_of_shape .str2 rfl (fun _ _ => ⟨_, rfl⟩)

end NativeAtom

/-- A typed atom application answers a value of the answer type (`nativeAtomTy`,
`Native.lean`, against `nativeAtom`; plan §2.2, ENSURES 5). The name resolves to an atom, and
the atom is sound: twenty hand blocks became a dispatch over the schemes. -/
theorem nativeAtom_typed (atom : String) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : nativeAtomTy atom tys = some ty) (hfit : Fits vs tys) :
    ∃ v, nativeAtom atom vs = some v ∧ Val.hasTy v ty = true := by
  unfold nativeAtomTy at hty
  obtain ⟨named, hname, hty⟩ := Option.bind_eq_some_iff.mp hty
  simp only [nativeAtom, hname, Option.bind_some]
  exact NativeAtom.sound named tys ty vs hty hfit

/-! ## Terms -/

/-- `termTy` on an application is the atom's type at the arguments' types, typed under the
atom's const-generic flag (`Typing/Rules.lean`, `argTy`), as an `Option.bind`. `argsTy_cons`
is the cons equation, with `argTy` for the head. -/
theorem termTy_app (tys : TyEnv) (atom : String) (args : Terms) :
    termTy nativeSignature tys (.app atom args) =
      (argsTy nativeSignature tys (nativeConstAtom atom) args).bind (nativeAtomTy atom) := rfl

/-- `evalTerm` on an application is the atom at the arguments' values (`Native.lean:91-93`). -/
theorem evalTerm_app (env : List Val) (atom : String) (args : Terms) :
    evalTerm env (.app atom args) = (evalTerms env args).bind (nativeAtom atom) := rfl

/-- `evalTerms` on a cons (`Native.lean:96-99`). -/
theorem evalTerms_cons (env : List Val) (head : Term) (tail : Terms) :
    evalTerms env (.cons head tail) =
      (evalTerm env head).bind fun v =>
        (evalTerms env tail).bind fun rest => some (v :: rest) := rfl

mutual
/-- Under `Fits`, a term that types and evaluates evaluates to a value of its type
(plan §2.2, ENSURES 6): `Fits.get?` at a variable, `Lit.toVal_hasTy` at a literal,
`nativeAtom_typed` at an application, with `nativeSignature.atomOf = nativeAtomTy` by `rfl`. -/
theorem evalTerm_hasTy (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty) (v : Val)
    (hfit : Fits env tys) (hty : termTy nativeSignature tys t = some ty)
    (hev : evalTerm env t = some v) : Val.hasTy v ty = true := by
  cases t with
  | var i => exact hfit.get? hev hty
  | lit l =>
    have hty' : some l.ty = some ty := by
      simp only [termTy, argTy, litArgTy_false] at hty
      exact hty
    cases hty'
    exact Lit.toVal_hasTy l v hev
  | app atom args =>
    rw [termTy_app] at hty
    obtain ⟨tl, hts, hatom⟩ := Option.bind_eq_some_iff.mp hty
    rw [evalTerm_app] at hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨v', hv', hty'⟩ :=
      nativeAtom_typed atom tl ty vs hatom
        (evalTerms_hasTy args env tys (nativeConstAtom atom) tl vs hfit hts hvs)
    rw [hv'] at hv
    cases hv
    exact hty'
termination_by structural t
/-- The list form of `evalTerm_hasTy`: the values fit the types (ENSURES 6), under either
const flag — a literal argument fits its literal-rule type (`Lit.toVal_hasTy_arg`). -/
theorem evalTerms_hasTy (ts : Terms) (env : List Val) (tys : TyEnv) (const : Bool)
    (tl : List Ty) (vs : List Val) (hfit : Fits env tys)
    (hty : argsTy nativeSignature tys const ts = some tl)
    (hev : evalTerms env ts = some vs) : Fits vs tl := by
  cases ts with
  | nil =>
    have hty' : some ([] : List Ty) = some tl := hty
    have hev' : some ([] : List Val) = some vs := hev
    cases hty'; cases hev'
    exact Fits.nil
  | cons head tail =>
    rw [argsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    rw [evalTerms_cons] at hev
    obtain ⟨v1, hv1, hev'⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨vrest, hvrest, hvcons⟩ := Option.bind_eq_some_iff.mp hev'
    cases hvcons
    refine Fits.cons ?_ (evalTerms_hasTy tail env tys const rest vrest hfit hrest hvrest)
    rcases argTy_cases _ _ _ head t1 ht1 with ⟨value, rfl, rfl⟩ | ht1'
    · exact Lit.toVal_hasTy_arg const value v1 hv1
    · exact evalTerm_hasTy head env tys t1 v1 hfit ht1' hv1
termination_by structural ts
end

mutual
/-- Under `Fits`, a term that types evaluates (plan §2.2, ENSURES 7): the lengths agree at a
variable (`Fits.length`), `Lit.toVal_isSome` at a literal, and `nativeAtom_typed` at an
application over the fitted argument values. Until DB-15 this carried a `noStr` premise, the
one literal that did not evaluate. -/
theorem evalTerm_isSome (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty)
    (hfit : Fits env tys) (hty : termTy nativeSignature tys t = some ty) :
    (evalTerm env t).isSome = true := by
  cases t with
  | var i =>
    have hty' : tys[i]? = some ty := hty
    have hlt : i < env.length := hfit.length ▸ (List.getElem?_eq_some_iff.mp hty').1
    show (env[i]?).isSome = true
    cases hv : env[i]? with
    | none => exact absurd hlt (Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hv))
    | some _ => rfl
  | lit l =>
    show l.toVal.isSome = true
    exact Lit.toVal_isSome l
  | app atom args =>
    rw [termTy_app] at hty
    obtain ⟨tl, hts, hatom⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨vs, hvs⟩ :=
      Option.isSome_iff_exists.mp (evalTerms_isSome args env tys (nativeConstAtom atom) tl hfit hts)
    obtain ⟨v', hv', _⟩ :=
      nativeAtom_typed atom tl ty vs hatom
        (evalTerms_hasTy args env tys (nativeConstAtom atom) tl vs hfit hts hvs)
    rw [evalTerm_app, hvs]
    show (nativeAtom atom vs).isSome = true
    rw [hv']
    rfl
termination_by structural t
/-- The list form of `evalTerm_isSome` (ENSURES 7), under either const flag. -/
theorem evalTerms_isSome (ts : Terms) (env : List Val) (tys : TyEnv) (const : Bool)
    (tl : List Ty) (hfit : Fits env tys) (hty : argsTy nativeSignature tys const ts = some tl) :
    (evalTerms env ts).isSome = true := by
  cases ts with
  | nil => rfl
  | cons head tail =>
    rw [argsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, _⟩ := Option.bind_eq_some_iff.mp hty'
    have hhead : (evalTerm env head).isSome = true := by
      rcases argTy_cases _ _ _ head t1 ht1 with ⟨value, rfl, _⟩ | ht1'
      · exact Lit.toVal_isSome value
      · exact evalTerm_isSome head env tys t1 hfit ht1'
    obtain ⟨v1, hv1⟩ := Option.isSome_iff_exists.mp hhead
    obtain ⟨vrest, hvrest⟩ :=
      Option.isSome_iff_exists.mp (evalTerms_isSome tail env tys const rest hfit hrest)
    rw [evalTerms_cons, hv1]
    show ((evalTerms env tail).bind fun rest => some (v1 :: rest)).isSome = true
    rw [hvrest]
    rfl
termination_by structural ts
end

/-! ## Rows -/

/-- A request value of a `sync` row's request type decodes to a store operation
(plan §2.2, ENSURES 8): the twenty rows of `NativeOp.row` (`Native.lean:145-203`) against the
patterns of `NativeOp.syncOpOf` (`:208-232`), each request shape recovered by the inversions
above. -/
theorem syncOpOf_isSome (op : NativeOp) (v : Val)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (hk : (NativeOp.row op).kind = .sync) : (NativeOp.syncOpOf op v).isSome = true := by
  cases op with
  | refMake =>
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    rfl
  | refGet =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refGetAndSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refSetAndGet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    rfl
  | refUpdate f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refGetAndUpdate f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateAndGet f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateSome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refGetAndUpdateSome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refUpdateSomeAndGet f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refModify f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | refModifySome f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    rfl
  | deferredMake =>
    obtain rfl := Val.hasTy_unit_inv hv
    rfl
  | deferredIsDone =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hv
    rfl
  | deferredPoll =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hv
    rfl
  | deferredSucceed =>
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    rfl
  | deferredFail =>
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    rfl
  | deferredAwait => simp [NativeOp.row] at hk
  | external _ => simp [NativeOp.row, NativeOp.externalPlaceholder] at hk
  | scopeMake strategy =>
    cases strategy with
    | sequential =>
      obtain rfl := Val.hasTy_unit_inv hv
      rfl
    | parallel =>
      obtain rfl := Val.hasTy_unit_inv hv
      rfl
  | sleep => simp [NativeOp.row] at hk
  | clockNow =>
    obtain rfl := Val.hasTy_unit_inv hv
    rfl

/-- An `async` row never decodes to a store operation (plan §2.2, ENSURES 9): the one async
row is `deferredAwait` (`Native.lean:195-197`), which `syncOpOf` sends to `none` on every
value (`:232`). -/
theorem syncOpOf_async_none (op : NativeOp) (v : Val) (hk : (NativeOp.row op).kind = .async) :
    NativeOp.syncOpOf op v = none := by
  cases op with
  | deferredAwait => rfl
  | external _ => rfl
  | sleep => rfl
  | scopeMake strategy => cases strategy <;> simp [NativeOp.row] at hk
  | _ => simp [NativeOp.row] at hk

end Effect4.Program
