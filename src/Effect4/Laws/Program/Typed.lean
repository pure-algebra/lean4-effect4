import Effect4.Program.Typed
import Effect4.Program.ErrorImage
import Effect4.Laws.Program.ErrorQueries

/-!
# Program.Typed — the value typing of the native cut (slice 1, lane 1)

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §2. Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 1–9. Batteries:
`Test/Program/TypedContract.lean` (the guards and the row `E4-TYPED-CE-002`; `E4-TYPED-CE-001`
is retired, below) and `Test/Program/TypedAxiomReport.lean`.

This module says which machine values (`src/Effect4/Machine/Stores.lean` `Val`) inhabit which
types of the program language (`src/Effect4/Program/Eff.lean` `Ty`), and proves three things
about the native route (`src/Effect4/Program/Native.lean`): a term that types
(`src/Effect4/Program/Typing.lean` `termTy`) and evaluates (`evalTerm`) evaluates to a value of
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

/-- An `.option t` is `none` or a `some` of a `t` (DB-15). -/
theorem Val.hasTy_option_inv {v : Val} {t : Ty} (h : Val.hasTy v (.option t) = true) :
    v = Store.Val.none ∨ ∃ x, v = Store.Val.some x ∧ Val.hasTy x t = true := by
  simp only [Val.hasTy] at h
  split at h
  · exact Or.inl rfl
  · next x => exact Or.inr ⟨x, rfl, h⟩
  · exact nomatch h

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

/-- A `.prod a b` is the two-cell list (`Val.tuple`) of an `a` and a `b`. (U1: the two cells
were `exitCons x (exitCons y exitNil)`; they are the carrier's `list [x, y]`.) -/
theorem Val.hasTy_prod_inv {v : Val} {a b : Ty} (h : Val.hasTy v (.prod a b) = true) :
    ∃ x y, v = Val.tuple [x, y] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true := by
  simp only [Val.hasTy] at h
  split at h
  · next x y => exact ⟨x, y, rfl, (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
  · exact nomatch h

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
against the production definition unchanged. -/

/-- The allocation table `after` agrees with `before` at every index `before` has. -/
def Extends (before after : List String) : Prop :=
  ∀ (i : Nat) (target : String), before[i]? = some target → after[i]? = some target

/-- A registration appends, and an append extends. -/
theorem extends_append (before added : List String) : Extends before (before ++ added) := by
  intro i target h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

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
  change (match Val.cause? v with
    | some c => causeAdmits (fun w _ => Val.hasTy w e) e c
    | none => false) = (match Val.cause? v with
    | some c => causeAdmits (fun w t => Val.hasTy w t) e c
    | none => false)
  cases hc : Val.cause? v with
  | none => rfl
  | some c => exact causeAdmits_congr e (fun _ => rfl) c

/-- Membership is monotone in the allocation table at every type. The type induction
uses the shared pointwise cause-fold law for causes and failed exits; only external handle
membership reads the table. All previous environment statements retain their premises. -/
theorem hasTy_mono (ty : Ty) (v : Val) (a b : List String)
    (ext : Extends a b) (typed : Val.hasTy v ty a = true) : Val.hasTy v ty b = true := by
  induction ty generalizing v with
  | never | int | except => simp [Val.hasTy] at typed
  | unit | nat | bool | string | fiberOf | lit => exact typed
  | handle target =>
    cases v <;> simp only [Val.hasTy] at typed ⊢
    all_goals try exact typed
    split at typed <;> try exact typed
    next h =>
      obtain ⟨ht, hi⟩ := Bool.and_eq_true_iff.mp typed
      apply Bool.and_eq_true_iff.mpr
      exact ⟨ht, beq_iff_eq.mpr (ext _ _ (beq_iff_eq.mp hi))⟩
  | option inner ih =>
    cases v <;> simp only [Val.hasTy] at typed ⊢
    all_goals try exact typed
    exact ih _ typed
  | prod x y ihx ihy =>
    simp only [Val.hasTy] at typed ⊢
    split at typed <;> try exact typed
    next u v =>
      exact Bool.and_eq_true_iff.mpr ⟨ihx u (Bool.and_eq_true_iff.mp typed).1,
        ihy v (Bool.and_eq_true_iff.mp typed).2⟩
  | union x y ihx ihy =>
    simp only [Val.hasTy, Bool.or_eq_true] at typed ⊢
    exact typed.elim (fun h => Or.inl (ihx _ h)) (fun h => Or.inr (ihy _ h))
  | exitOf x y ihx ihy =>
    simp only [Val.hasTy] at typed ⊢
    split at typed <;> try exact typed
    · exact ihx _ typed
    · split at typed <;> try exact typed
      exact causeAdmits_mono y (fun w => ihy w) _ typed
  | causeOf e ih =>
    simp only [Val.hasTy] at typed ⊢
    split at typed <;> try exact typed
    exact causeAdmits_mono e (fun w => ih w) _ typed
  | list x ih =>
    simp only [Val.hasTy] at typed ⊢
    split at typed <;> try exact typed
    · split at typed <;> try exact typed
      apply List.all_eq_true.mpr
      intro id hid
      exact ih (Val.fiber id) (List.all_eq_true.mp typed id hid)
    · apply List.all_eq_true.mpr
      intro value hv
      exact ih value (List.all_eq_true.mp typed value hv)

/-- The registration case of `hasTy_mono`: a value typed before an allocation is typed
after it. -/
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

/-- A fit against two types is two values of those types. -/
theorem Fits.pair_inv {vs : List Val} {a b : Ty} (h : Fits vs [a, b]) :
    ∃ x y, vs = [x, y] ∧ Val.hasTy x a = true ∧ Val.hasTy y b = true := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' => cases hrest'; exact ⟨_, _, rfl, hx, hy⟩

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

/-! ## Atoms -/

/-- A typed atom application answers a value of the answer type (`nativeAtomTy`,
`Native.lean:73-84`, against `nativeAtom`, `:59-70`; plan §2.2, ENSURES 5). `pair` answers
`Val.tuple [a, b]`, the `.prod` shape of `hasTy`; `fst` and `snd` read that shape back. -/
theorem nativeAtom_typed (atom : String) (tys : List Ty) (ty : Ty) (vs : List Val)
    (hty : nativeAtomTy atom tys = some ty) (hfit : Fits vs tys) :
    ∃ v, nativeAtom atom vs = some v ∧ Val.hasTy v ty = true := by
  unfold nativeAtomTy at hty
  obtain ⟨named, hname, hty⟩ := Option.bind_eq_some_iff.mp hty
  simp only [nativeAtom, hname, Option.bind_some]
  unfold NativeAtom.typeOf at hty
  split at hty
  · -- succ
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- pred
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- isZero
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- not
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨b, rfl⟩ := Val.hasTy_bool_inv hv
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- add
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- lt
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- eq
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := Val.hasTy_nat_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- string equality
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨a, rfl⟩ := Val.hasTy_string_inv hx
    obtain ⟨b, rfl⟩ := Val.hasTy_string_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- pair
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    exact ⟨_, rfl, by simp [Val.hasTy, hx, hy]⟩
  · -- fst
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    exact ⟨x, rfl, hx⟩
  · -- snd
    cases hty
    obtain ⟨v, rfl, hv⟩ := hfit.singleton_inv
    obtain ⟨x, y, rfl, _, hy⟩ := Val.hasTy_prod_inv hv
    exact ⟨y, rfl, hy⟩
  · -- strings: every argument fits `.string`, so every value is a `str` and the list types
    split at hty
    · next hall =>
      cases hty
      have hstr : ∀ v ∈ vs, ∃ s, v = Val.str s := fun v hv =>
        Val.hasTy_string_inv (Fits.all_string hfit hall v hv)
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
    · cases hty
  · -- cause failure query
    obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
    cases hanswer
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact queryTag_typed .fail value _ error [] hdomain hv
  · -- cause defect query
    obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
    cases hanswer
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact queryTag_typed .die value _ error [] hdomain hv
  · -- cause interruption query
    obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
    cases hanswer
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact queryTag_typed .interrupt value _ error [] hdomain hv
  · -- first failure payload query
    obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
    cases hanswer
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact queryError_typed value _ error [] hdomain hv
  · -- Boolean or
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨a, rfl⟩ := Val.hasTy_bool_inv hx
    obtain ⟨b, rfl⟩ := Val.hasTy_bool_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  · -- Boolean and
    cases hty
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨a, rfl⟩ := Val.hasTy_bool_inv hx
    obtain ⟨b, rfl⟩ := Val.hasTy_bool_inv hy
    exact ⟨_, rfl, by simp [Val.hasTy]⟩
  -- Each constructor has its own exhaustive argument-shape refusal.
  all_goals cases hty

/-! ## Terms -/

/-- `termTy` on an application is the atom's type at the arguments' types
(`Typing.lean:63-65`), as an `Option.bind`. -/
theorem termTy_app (tys : TyEnv) (atom : String) (args : Terms) :
    termTy nativeSignature tys (.app atom args) =
      (termsTy nativeSignature tys args).bind (nativeAtomTy atom) := rfl

/-- `termsTy` on a cons (`Typing.lean:68-71`), as nested `Option.bind`s. -/
theorem termsTy_cons (tys : TyEnv) (head : Term) (tail : Terms) :
    termsTy nativeSignature tys (.cons head tail) =
      (termTy nativeSignature tys head).bind fun t =>
        (termsTy nativeSignature tys tail).bind fun rest => some (t :: rest) := rfl

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
    have hty' : some l.ty = some ty := hty
    cases hty'
    exact Lit.toVal_hasTy l v hev
  | app atom args =>
    rw [termTy_app] at hty
    obtain ⟨tl, hts, hatom⟩ := Option.bind_eq_some_iff.mp hty
    rw [evalTerm_app] at hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨v', hv', hty'⟩ :=
      nativeAtom_typed atom tl ty vs hatom (evalTerms_hasTy args env tys tl vs hfit hts hvs)
    rw [hv'] at hv
    cases hv
    exact hty'
termination_by structural t
/-- The list form of `evalTerm_hasTy`: the values fit the types (ENSURES 6). -/
theorem evalTerms_hasTy (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty)
    (vs : List Val) (hfit : Fits env tys) (hty : termsTy nativeSignature tys ts = some tl)
    (hev : evalTerms env ts = some vs) : Fits vs tl := by
  cases ts with
  | nil =>
    have hty' : some ([] : List Ty) = some tl := hty
    have hev' : some ([] : List Val) = some vs := hev
    cases hty'; cases hev'
    exact Fits.nil
  | cons head tail =>
    rw [termsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    rw [evalTerms_cons] at hev
    obtain ⟨v1, hv1, hev'⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨vrest, hvrest, hvcons⟩ := Option.bind_eq_some_iff.mp hev'
    cases hvcons
    exact Fits.cons (evalTerm_hasTy head env tys t1 v1 hfit ht1 hv1)
      (evalTerms_hasTy tail env tys rest vrest hfit hrest hvrest)
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
      Option.isSome_iff_exists.mp (evalTerms_isSome args env tys tl hfit hts)
    obtain ⟨v', hv', _⟩ :=
      nativeAtom_typed atom tl ty vs hatom (evalTerms_hasTy args env tys tl vs hfit hts hvs)
    rw [evalTerm_app, hvs]
    show (nativeAtom atom vs).isSome = true
    rw [hv']
    rfl
termination_by structural t
/-- The list form of `evalTerm_isSome` (ENSURES 7). -/
theorem evalTerms_isSome (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty)
    (hfit : Fits env tys) (hty : termsTy nativeSignature tys ts = some tl) :
    (evalTerms env ts).isSome = true := by
  cases ts with
  | nil => rfl
  | cons head tail =>
    rw [termsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, _⟩ := Option.bind_eq_some_iff.mp hty'
    obtain ⟨v1, hv1⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome head env tys t1 hfit ht1)
    obtain ⟨vrest, hvrest⟩ :=
      Option.isSome_iff_exists.mp (evalTerms_isSome tail env tys rest hfit hrest)
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
