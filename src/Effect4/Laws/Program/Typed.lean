import Effect4.Program.Typed
import Effect4.Laws.Program.Typed.RecordValues
import Effect4.Laws.Program.Typed.MapValues
import Effect4.Program.ErrorImage
import Effect4.Laws.Program.ErrorQueries
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Template
import Effect4.Program.Bounds
import Effect4.Laws.Program.Bounds
import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.Eliminators
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

/-- A value at `refOf A` is a `Val.cell`, at any `A`: the kind byte is the cell's
(`HandleKind.ofByte?_exact`); what the cell holds is typed by the world's tables. -/
theorem Val.hasTy_refOf_inv {v : Val} {A : Ty} {allocated : List String}
    (h : Val.hasTy v (.refOf A) allocated = true) : ∃ k, v = Val.cell k := by
  simp only [Val.hasTy] at h
  split at h
  · next kind index =>
    exact ⟨⟨index⟩, by rw [HandleKind.ofByte?_exact (beq_iff_eq.mp h)]; rfl⟩
  · exact nomatch h

/-- A value at `deferredOf A E` is a `Val.promise`, at any `A` and `E`. -/
theorem Val.hasTy_deferredOf_inv {v : Val} {A E : Ty} {allocated : List String}
    (h : Val.hasTy v (.deferredOf A E) allocated = true) : ∃ k, v = Val.promise k := by
  simp only [Val.hasTy] at h
  split at h
  · next kind index =>
    exact ⟨⟨index⟩, by rw [HandleKind.ofByte?_exact (beq_iff_eq.mp h)]; rfl⟩
  · exact nomatch h

/-- **A spelling no handle kind owns has no member** (the state plan's T3a): a retired spelling is
not the scope's, the memo map's or the context's, and an external handle may not take it
(`internalHandleTargets`). The inhabitance fold reads the same list (`inhabitedAlg`). -/
theorem Val.hasTy_handle_retired {v : Val} {target : String} {allocated : List String}
    (hr : retiredHandleTargets.contains target = true) :
    Val.hasTy v (.handle target) allocated = false := by
  have hm : target ∈ retiredHandleTargets := List.contains_iff_mem.mp hr
  simp only [retiredHandleTargets, List.mem_cons, List.not_mem_nil, or_false] at hm
  have hext : externalHandleTarget target = false := by
    rcases hm with rfl | rfl <;> decide
  have hscope : (target == Ty.scopeTarget) = false := by
    rcases hm with rfl | rfl <;> decide
  have hmemo : (target == Ty.memoMapTarget) = false := by
    rcases hm with rfl | rfl <;> decide
  have hctx : (target == Ty.contextTarget) = false := by
    rcases hm with rfl | rfl <;> decide
  have hmask : (target == Ty.maskRestoreTarget) = false := by
    rcases hm with rfl | rfl <;> decide
  simp only [Val.hasTy]
  split
  · split
    · exact hscope
    · exact hmemo
    · rw [hext, Bool.false_and]
    · rfl
  · rw [hctx, hmask, Bool.false_and, Bool.false_and]
    rfl

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
    -- the fold reads the error only through its image, whatever the error alphabet holds
    simp only [reasonAdmits]
    cases valOfErr e with
    | none => rfl
    | some v => exact h v
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
    simp only [reasonAdmits]
    cases valOfErr e with
    | none => exact id
    | some v => exact h v
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

/-- Appending the two binders of a list fold keeps the fit: the accumulator at the fold's level
and the element one above it (decisions row 228). Step of the fold cases of `evalTerm_hasTy` and
`evalTerm_isSome`. -/
theorem Fits.append_pair {env : List Val} {tys : TyEnv} (h : Fits env tys) {v w : Val}
    {t u : Ty} (hv : Val.hasTy v t = true) (hw : Val.hasTy w u = true) :
    Fits (env ++ [v, w]) (tys ++ [t, u]) := by
  induction h with
  | nil => exact Fits.cons hv (Fits.cons hw Fits.nil)
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

/-- A successful list match by bounds puts every argument at its parameter's instance under the
bindings of the match: each argument is below its parameter's instance (`matchArgsB_sound`), and
values of a subtype are values of the supertype (`hasTy_sub`). -/
theorem Fits.instantiate_admits {σ : Ty.Subst} {ps : TyEnv} :
    ∀ {rs : TyEnv}, ps.length = rs.length → Bounds.Admits σ ps rs →
      ∀ {vs : List Val}, Fits vs rs → Fits vs (ps.map (Ty.instantiate σ)) := by
  induction ps with
  | nil =>
    intro rs hlen hadm vs hfit
    cases rs with
    | nil => cases hfit; exact .nil
    | cons _ _ => exact nomatch hlen
  | cons p ps ih =>
    intro rs hlen hadm vs hfit
    cases rs with
    | nil => exact nomatch hlen
    | cons r rs =>
      cases hfit with
      | cons hv hfit' =>
        have hsub : Ty.sub r.normalize (Ty.instantiate σ p).normalize = true :=
          hadm (p, r) List.mem_cons_self
        have hinst := hasTy_sub r.normalize _ _ [] hsub ((hasTy_normalize r _ []).trans hv)
        rw [hasTy_normalize] at hinst
        have hadm' : Bounds.Admits σ ps rs := fun pr hpr =>
          hadm pr (List.mem_cons_of_mem _ hpr)
        exact .cons hinst (ih (Nat.succ.inj hlen) hadm' hfit')

/-- The poly scheme's premise for matchArgsB (`NativeAtom.sound_of_poly`). -/
theorem Fits.instantiateB {σ : Ty.Subst} {ps rs : TyEnv}
    (hmatch : Bounds.matchArgsB ps rs = some σ)
    {vs : List Val} (hfit : Fits vs rs) : Fits vs (ps.map (Ty.instantiate σ)) := by
  have ⟨hlen, hadm⟩ := Bounds.matchArgsB_sound hmatch
  exact Fits.instantiate_admits hlen hadm hfit

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

/-- Exact tuple construction from fitted atom arguments, for `NativeAtom.sound`. -/
theorem Fits.tuple {values : List Val} {types : List Ty} (h : Fits values types) :
    Val.hasTy (.list values) (.tuple types) = true := by
  rw [Val.hasTy_tuple]
  induction h with
  | nil => rfl
  | cons hx _ ih =>
    simp only [List.map_cons, itemsHasTy, Bool.and_eq_true]
    exact ⟨hx, ih⟩

/-- A typed tuple's admitted position has a value of that exact column.
This is the indexed helper consumed by `Tuple.project_typed`. -/
theorem tupleItem_typed (allocated : List String) :
    ∀ (types : List Ty) (values : List Val) (index : Nat) (answer : Ty),
      types[index]? = some answer →
      itemsHasTy (types.map (fun t x => Val.hasTy x t allocated)) values = true →
      ∃ value, values[index]? = some value ∧ Val.hasTy value answer allocated = true
  | [], _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | t :: ts, value :: values, 0, answer, h, hv => by
    cases h
    exact ⟨value, rfl, (Bool.and_eq_true_iff.mp hv).1⟩
  | t :: ts, value :: values, index + 1, answer, h, hv =>
    tupleItem_typed allocated ts values index answer h (Bool.and_eq_true_iff.mp hv).2

/-- A plain tuple frame supports every statically admitted column. -/
theorem tupleAt_typed {allocated : List String} {types : List Ty} {value : Val}
    {index : Nat} {answer : Ty} (hi : types[index]? = some answer)
    (hv : Val.hasTy value (.tuple types) allocated = true) :
    ∃ out, Val.tupleAt? value index = some out ∧ Val.hasTy out answer allocated = true := by
  simp only [Val.hasTy] at hv
  split at hv
  · next values =>
    rw [Val.itemCheckers_eq_map] at hv
    exact tupleItem_typed allocated types values index answer hi hv
  · cases hv

/-- The projection rule produces a member of the selected type, at the same allocation table.
This serves `denote-typed` through the term membership and progress consumers. -/
theorem Tuple.project_typed (index : Nat) (input output : Ty) (value : Val)
    (allocated : List String) (hp : Tuple.project index input = some output)
    (hv : Val.hasTy value input allocated = true) :
    ∃ out, Val.tupleAt? value index = some out ∧ Val.hasTy out output allocated = true := by
  induction input generalizing output with
  | never => cases hv
  | tuple items _ => exact tupleAt_typed hp hv
  | prod a b _ _ =>
    apply tupleAt_typed hp
    rw [hasTy_tuple_pair]
    exact hv
  | union a b iha ihb =>
    obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨right, hr, heq⟩ := Option.bind_eq_some_iff.mp rest
    cases heq
    rcases Bool.or_eq_true_iff.mp hv with ha | hb
    · obtain ⟨out, he, hm⟩ := iha left hl ha
      exact ⟨out, he, Ty.hasTy_join_left left right out allocated hm⟩
    · obtain ⟨out, he, hm⟩ := ihb right hr hb
      exact ⟨out, he, Ty.hasTy_join_right left right out allocated hm⟩
  | _ => simp only [Tuple.project, reduceCtorEq] at hp

/-- Normalization retains the tuple projection's membership premise. -/
theorem Tuple.typeAt_typed {index : Nat} {input output : Ty} {value : Val}
    {allocated : List String} (hp : Tuple.typeAt input index = some output)
    (hv : Val.hasTy value input allocated = true) :
    ∃ out, Val.tupleAt? value index = some out ∧ Val.hasTy out output allocated = true := by
  apply Tuple.project_typed index input.normalize output value allocated hp
  rw [hasTy_normalize]
  exact hv

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

/-! String-map operations at the Boolean value check.
These helpers serve `denote-typed` through native-atom soundness, with the existing premises. -/
namespace MapChecks
open Typed.MapValues

/-- A fitting string map has its exact pair carrier and fitting payloads. -/
theorem map_inv {value : Val} {t : Ty} (h : Val.hasTy value (.map .string t) = true) :
    ∃ entries, value = Machine.Map.write entries ∧
      ∀ e ∈ entries, Val.hasTy e.2 t = true := by
  simp only [Val.hasTy] at h
  split at h
  · next values =>
    have hall := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2
    have hw : ∀ value ∈ values, ∃ e : String × Val,
        value = .pair (.str e.1) e.2 ∧ Val.hasTy e.2 t = true := by
      intro v hv
      have hp := hall v hv
      cases v with
      | pair key payload =>
        cases key with
        | str name => exact ⟨(name, payload), rfl, (Bool.and_eq_true_iff.mp hp).2⟩
        | _ => cases hp
      | _ => cases hp
    obtain ⟨entries, rfl, hentries⟩ := encoded_of_all _ _ values hw
    exact ⟨entries, rfl, hentries⟩
  · exact nomatch h

/-- Canonical map construction retains every payload's Boolean type membership. -/
theorem write_canon {entries : List (String × Val)} {t : Ty}
    (h : ∀ e ∈ entries, Val.hasTy e.2 t = true) :
    Val.hasTy (Machine.Map.write (Field.canonBy Field.bytesKey entries)) (.map .string t) = true := by
  refine Bool.and_eq_true_iff.mpr ⟨sorted_pairs (Field.canonBy_ascending entries), ?_⟩
  apply List.all_eq_true.mpr
  intro value hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact h e (Field.mem_canonBy he)

/-- Lookup produces a typed outer option and preserves absence. -/
theorem get {value : Val} {t : Ty} (h : Val.hasTy value (.map .string t) = true) (key : String) :
    ∃ out, Machine.Map.get value key = some out ∧ Val.hasTy out (.option t) = true := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  cases hf : Field.firstOf key entries with
  | none => exact ⟨.none, by simp only [Machine.Map.get, Machine.Map.read_write, hf, Option.map_some, Option.elim_none], rfl⟩
  | some found =>
    exact ⟨.some found, by simp only [Machine.Map.get, Machine.Map.read_write, hf, Option.map_some, Option.elim_some],
      hall (key, found) (Field.firstOf_mem hf)⟩

/-- Update answers in the union of the old and replacement value types. -/
theorem set {value replacement : Val} {a b : Ty}
    (h : Val.hasTy value (.map .string a) = true) (key : String)
    (hr : Val.hasTy replacement b = true) :
    ∃ out, Machine.Map.set value key replacement = some out ∧
      Val.hasTy out (.map .string (.union a b)) = true := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  refine ⟨Machine.Map.write (Field.canonBy Field.bytesKey ((key, replacement) :: entries)),
    by simp only [Machine.Map.set, Machine.Map.read_write, Option.map_some], write_canon ?_⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact Bool.or_eq_true_iff.mpr (Or.inr hr)
  · exact Bool.or_eq_true_iff.mpr (Or.inl (hall e he))

/-- Key extraction answers a list of strings. -/
theorem keys {value : Val} {t : Ty} (h : Val.hasTy value (.map .string t) = true) :
    ∃ out, Machine.Map.keys value = some out ∧ Val.hasTy out (.list .string) = true := by
  obtain ⟨entries, rfl, _⟩ := map_inv h
  refine ⟨.list ((Field.canonBy Field.bytesKey entries).map fun e => .str e.1),
    by simp only [Machine.Map.keys, Machine.Map.read_write, Option.map_some], ?_⟩
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hv
  rfl

/-- Entry extraction uses ordinary program pairs and retains payload membership. -/
theorem entries {value : Val} {t : Ty} (h : Val.hasTy value (.map .string t) = true) :
    ∃ out, Machine.Map.entries value = some out ∧
      Val.hasTy out (.list (.prod .string t)) = true := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  refine ⟨.list ((Field.canonBy Field.bytesKey entries).map fun e => .list [.str e.1, e.2]),
    by simp only [Machine.Map.entries, Machine.Map.read_write, Option.map_some], ?_⟩
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact hall e (Field.mem_canonBy he)

/-- Every fitting list of ordinary string pairs constructs a map, including the empty snapshot. -/
theorem fromEntries {value : Val} {t : Ty}
    (h : Val.hasTy value (.list (.prod .string t)) = true) :
    ∃ out, Machine.Map.fromEntries value = some out ∧ Val.hasTy out (.map .string t) = true := by
  obtain ⟨values, hv, hall⟩ := Val.hasTy_list_inv h
  have hw : ∀ value ∈ values, ∃ e : String × Val,
      value = .list [.str e.1, e.2] ∧ Val.hasTy e.2 t = true := by
    intro value hvalue
    obtain ⟨key, payload, rfl, hk, hp⟩ := Val.hasTy_prod_inv (hall value hvalue)
    obtain ⟨name, rfl⟩ := Val.hasTy_string_inv hk
    exact ⟨(name, payload), rfl, hp⟩
  obtain ⟨entries, rfl, hentries⟩ := encoded_of_all _ _ values hw
  refine ⟨Machine.Map.write (Field.canonBy Field.bytesKey entries.reverse),
    by simp only [Machine.Map.fromEntries, hv, Option.bind_eq_bind, Option.bind_some,
      Machine.Map.readTuples_map, Option.pure_def], write_canon ?_⟩
  exact fun e he => hentries e (List.mem_reverse.mp he)

end MapChecks

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
at the final bindings" is `Fits.instantiateB`. Quantifying over every σ is stronger than
`Scheme.apply` needs, and every template here is parametric in what it binds, so nothing is lost. -/
theorem sound_of_poly {a : NativeAtom} {params : TyEnv} {answer : Ty}
    (hs : (spec a).scheme = .poly params answer)
    (hev : ∀ (σ : Ty.Subst) (vs : List Val), Fits vs (params.map (Ty.instantiate σ)) →
             ∃ v, eval a vs = some v ∧ Val.hasTy v (Ty.instantiate σ answer) = true) :
    Sound a := by
  intro tys ty vs hty hfit
  simp only [typeOf, hs, Scheme.apply] at hty
  obtain ⟨σ, hmatch, rfl⟩ := Option.map_eq_some_iff.mp hty
  exact hev σ vs (Fits.instantiateB hmatch hfit)

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
  | mapEmpty => exact sound_of_mono rfl fun vs hfit => by cases hfit.nil_inv; exact ⟨_, rfl, rfl⟩
  | mapGet =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨value, key, rfl, hv, hk⟩ := hfit.pair_inv
    obtain ⟨name, rfl⟩ := Val.hasTy_string_inv hk
    exact MapChecks.get hv name
  | mapSet =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨value, key, replacement, rfl, hv, hk, hr⟩ := hfit.triple_inv
    obtain ⟨name, rfl⟩ := Val.hasTy_string_inv hk
    exact MapChecks.set hv name hr
  | mapKeys =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact MapChecks.keys hv
  | mapEntries =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact MapChecks.entries hv
  | mapFromEntries =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨value, rfl, hv⟩ := hfit.singleton_inv
    exact MapChecks.fromEntries hv
  | tuple =>
    refine sound_of_custom rfl fun types answer values ht hv => ?_
    cases ht
    refine ⟨.list values, rfl, ?_⟩
    rw [hasTy_normalize]
    exact hv.tuple
  -- a prefix and its rest hold members of the list (decisions row 228)
  | listTake =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := Val.hasTy_list_inv hxs
    exact ⟨.list (elems.take n), by simp only [eval, hl, Option.map_some],
      List.all_eq_true.mpr fun y hy => helems y (List.mem_of_mem_take hy)⟩
  | listDrop =>
    refine sound_of_poly rfl fun σ vs hfit => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := Val.hasTy_list_inv hxs
    exact ⟨.list (elems.drop n), by simp only [eval, hl, Option.map_some],
      List.all_eq_true.mpr fun y hy => helems y (List.mem_of_mem_drop hy)⟩
  -- two handles of one admitted kind carry one kind byte, so the test answers (decisions
  -- row 229): the typing excludes the two-kinds refusal of the evaluation
  | sameHandle =>
    refine sound_of_custom rfl ?_
    intro tys ty vs hty hfit
    simp only [CustomScheme.apply, sameHandleRule] at hty
    split at hty
    · cases hty
      obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hx
      obtain ⟨k', rfl⟩ := Val.hasTy_refOf_inv hy
      refine ⟨Val.bool (k.index = k'.index), ?_, rfl⟩
      show (if (2 : UInt8) = 2 then some (Val.bool (decide (k.index = k'.index))) else none) = _
      exact if_pos rfl
    · cases hty
      obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl⟩ := Val.hasTy_deferredOf_inv hx
      obtain ⟨k', rfl⟩ := Val.hasTy_deferredOf_inv hy
      refine ⟨Val.bool (k.index = k'.index), ?_, rfl⟩
      show (if (3 : UInt8) = 3 then some (Val.bool (decide (k.index = k'.index))) else none) = _
      exact if_pos rfl
    · exact nomatch hty

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

/-! Record operations at the Boolean value check.
These laws serve the existing native term contracts, separately from world-indexed membership.
The shared named-frame facts retain the operation's actual returned value. -/
namespace RecordChecks
open Typed

private abbrev Has (value : Val) (type : Ty) : Prop := Val.hasTy value type = true
private def pred (field : Bool × Ty) : Bool × (Val → Prop) :=
  (field.1, fun value => Has value field.2)

private theorem has_normalize (type : Ty) (value : Val) : Has value type.normalize ↔ Has value type := by
  unfold Has
  rw [hasTy_normalize]

private theorem has_subN {a b : Ty} (hsub : Ty.subN a b = true) (value : Val)
    (hvalue : Has value a) : Has value b := by
  change Val.hasTy value b = true
  rw [← hasTy_normalize b value []]
  exact hasTy_sub a.normalize b.normalize value [] hsub ((has_normalize a value).mpr hvalue)

private theorem has_members (value : Val) (type : Ty) :
    (∃ branch ∈ type.members, Has value branch) ↔ Has value type := by
  change (∃ branch ∈ type.members, Val.hasTy value branch = true) ↔ Val.hasTy value type = true
  rw [← hasTy_members value type [], List.any_eq_true]

private theorem join_left (a b : Ty) (value : Val) (h : Has value a) : Has value (Ty.join a b) :=
  Ty.hasTy_join_left a b value [] h

private theorem join_right (a b : Ty) (value : Val) (h : Has value b) : Has value (Ty.join a b) :=
  Ty.hasTy_join_right a b value [] h

/-- The Boolean value check reads a union: its normal form, its union members and its join
(`UnionRule.ReadsUnion`, `src/Effect4/Laws/Program/UnionRule.lean`). A step of `fieldType` and
`setType` below: each record rule's law at one record lifts through it. -/
theorem has_reads : UnionRule.ReadsUnion Has where
  normalize h := (has_normalize _ _).mpr h
  members h := (has_members _ _).mpr h
  joinLeft a b h := join_left a b _ h
  joinRight a b h := join_right a b _ h

private theorem has_record {v : Val} {ns xs : List Val} (hv : recordParts? v = some (ns, xs))
    (fields : List (String × Bool × Ty)) :
    Has v (.record fields) ↔ NamedFit ((Ty.canon fields).map (fun q => (q.1, pred q.2))) ns xs := by
  unfold Has
  rw [Val.hasTy_record hv fields [], ← namedFit_check_iff]
  simp only [List.map_map, Function.comp_def, Val.checkerOf, pred]

private theorem has_record_inv (v : Val) (fields : List (String × Bool × Ty))
    (hfit : Has v (.record fields)) : ∃ ns xs, recordParts? v = some (ns, xs) ∧
      NamedFit ((Ty.canon fields).map (fun q => (q.1, pred q.2))) ns xs := by
  cases hv : recordParts? v with
  | none =>
    change Val.hasTy v (.record fields) = true at hfit
    rw [Val.hasTy_record_none hv] at hfit
    exact Bool.noConfusion hfit
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    exact ⟨ns, xs, rfl, (has_record hv fields).mp hfit⟩

/-- Fitting argument lists stay paired with their supplied names and named lookups. -/
theorem zipNames_checked {values : List Val} {types : List Ty}
    (hfit : Effect4.Program.Fits values types) :
    ∀ (names : List String) (arguments : List (String × Ty)),
      Record.zipNames names types = some arguments →
      ∃ es, Record.zipNames names values = some es ∧
        ∀ name, match Field.firstOf name es, Field.firstOf name arguments with
        | none, none => True
        | some value, some type => Has value type
        | _, _ => False := by
  induction hfit with
  | nil =>
    intro names arguments h
    cases names with
    | nil => cases h; exact ⟨[], rfl, fun _ => True.intro⟩
    | cons n ns => cases h
  | @cons value type values types hv _ ih =>
    intro names arguments h
    cases names with
    | nil => cases h
    | cons n names =>
      obtain ⟨args, hargs, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨es, hes, hrel⟩ := ih names args hargs
      refine ⟨(n, value) :: es, ?_, ?_⟩
      · simp only [Record.zipNames, hes, Option.map_some]
      · intro name
        by_cases hn : n = name
        · simp only [Field.firstOf, if_pos hn]
          exact hv
        · simp only [Field.firstOf, if_neg hn]
          exact hrel name

/-- An admitted construction returns a value accepted by its Boolean type check.
The native term proofs supply evaluated arguments through `Program.Fits`. -/
theorem build {fields : List (String × Bool × Ty)}
    {names : List String} {types : List Ty} {values : List Val} {answer : Ty}
    (hcheck : Program.Record.check fields names types = some answer)
    (hfit : Effect4.Program.Fits values types) :
    ∃ value, Record.build names values = some value ∧ Has value answer := by
  cases hargs : Record.zipNames names types with
  | none =>
    simp only [Program.Record.check, hargs, Option.bind_eq_bind, Option.bind_none] at hcheck
    cases hcheck
  | some arguments =>
    simp only [Program.Record.check, hargs, Option.bind_eq_bind, Option.bind_some] at hcheck
    split at hcheck
    next hchecks =>
      cases hcheck
      obtain ⟨es, hes, hrel⟩ := zipNames_checked hfit names arguments hargs
      have hargsNames := (zipNames_columns names types arguments hargs).1
      have hesNames := (zipNames_columns names values es hes).1
      have hall := Bool.and_eq_true_iff.mp hchecks.2.2
      have hsubsetRaw : es.map Prod.fst ⊆ fields.map Prod.fst := by
        intro name hname
        rw [hesNames, ← hargsNames] at hname
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hname
        have hadmitted := List.all_eq_true.mp hall.1 a ha
        cases hf : Field.firstOf a.1 fields with
        | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hadmitted
        | some field => exact List.mem_map.mpr ⟨(a.1, field), Field.firstOf_mem hf, rfl⟩
      let canonical := Field.canonBy Field.bytesKey es
      let predicates := (Ty.canon fields).map (fun q => (q.1, pred q.2))
      have hsorted : Field.Ascending Field.bytesKey predicates :=
        Field.ascending_map (pred) (Field.canonBy_ascending fields)
      have hcanonical : Field.Ascending Field.bytesKey canonical := Field.canonBy_ascending es
      have hsubset : canonical.map Prod.fst ⊆ predicates.map Prod.fst := by
        intro name hname
        have hraw : name ∈ es.map Prod.fst :=
          (Field.mem_names_canonBy Field.bytesKey_injective es name).mp hname
        have hf : name ∈ (Ty.canon fields).map Prod.fst :=
          (Field.mem_names_canonBy Field.bytesKey_injective fields name).mpr (hsubsetRaw hraw)
        simpa only [predicates, List.map_map, Function.comp_def] using hf
      have hlookup : ∀ q ∈ predicates, match Field.firstOf q.1 canonical with
          | none => q.2.1 = true
          | some value => q.2.2 value := by
        intro q hq
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
        have hfield := List.all_eq_true.mp hall.2 f (Field.mem_canonBy hf)
        have hvalues := hrel f.1
        rw [Field.firstOf_canonBy Field.bytesKey_injective]
        cases ht : Field.firstOf f.1 arguments with
        | none =>
          simp only [ht] at hfield hvalues
          cases hv : Field.firstOf f.1 es with
          | none => exact hfield
          | some value => simp only [hv] at hvalues
        | some type =>
          simp only [ht] at hfield hvalues
          cases hv : Field.firstOf f.1 es with
          | none => simp only [hv] at hvalues
          | some value =>
            simp only [hv] at hvalues
            exact has_subN hfield value hvalues
      refine ⟨Record.frame canonical, ?_, ?_⟩
      · simp only [Record.build, hes, Option.bind_eq_bind, Option.bind_some, if_pos hchecks.2.1, canonical]
      · apply (has_normalize (.record fields) _).mpr
        apply (has_record (v := Record.frame canonical) rfl fields).mpr
        exact namedFit_of_sublist_lookup predicates canonical
          (Field.names_nodup_of_ascending hsorted)
          (ascending_names_sublist predicates canonical hsorted hcanonical hsubset) hlookup
    next hchecks => cases hcheck


/-- The Boolean record check supplies a frame with string names and distinct fields.
Lookup consumes the existing value. -/
theorem entries {v : Val} {fields : List (String × Bool × Ty)}
    (hfit : Has v (.record fields)) :
    ∃ es, Record.entries v = some es ∧
      NamedFit ((Ty.canon fields).map (fun q => (q.1, pred q.2)))
        (es.map (fun e => .str e.1)) (es.map Prod.snd) := by
  obtain ⟨ns, xs, hparts, hnamed⟩ := has_record_inv v fields hfit
  obtain ⟨es, rfl, rfl⟩ := namedFit_columns _ ns xs hnamed
  have hnd : (((Ty.canon fields).map (fun q => (q.1, pred q.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      Field.canonBy_names_nodup (key := Field.bytesKey) fields
  have hend := (namedFit_names_sublist _ es hnamed).nodup hnd
  refine ⟨es, ?_, hnamed⟩
  simp only [Record.entries, hparts, Option.bind_eq_bind, Option.bind_some, readColumns_frame, if_pos hend]


/-- A declared field's actual lookup either returns its member or proves optional absence.
The term evaluator consumes this bridge for both field-read modes. -/
theorem lookup {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {optional : Bool} {type : Ty}
    (hfit : Has v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (optional, type)) :
    ∃ result, Record.lookup v name = some result ∧
      match result with
      | none => optional = true
      | some value => Has value type := by
  obtain ⟨es, hentries, hnamed⟩ := entries hfit
  have hnd : (((Ty.canon fields).map (fun q => (q.1, pred q.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      Field.canonBy_names_nodup (key := Field.bytesKey) fields
  have hmem := Field.firstOf_mem hfield
  have hq : (name, optional, fun x => Has x type) ∈
      (Ty.canon fields).map (fun q => (q.1, pred q.2)) :=
    List.mem_map.mpr ⟨(name, optional, type), hmem, rfl⟩
  refine ⟨Field.firstOf name es, ?_, namedFit_lookup _ es hnd hnamed _ hq⟩
  simp only [Record.lookup, hentries, Option.map_some]


/-- Required lookup finds the existing field accepted by its declared type check.
The native term theorem `evalTerm_isSome` consumes this operation result. -/
theorem required {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {type : Ty}
    (hfit : Has v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (false, type)) :
    ∃ value, Record.lookup v name = some (some value) ∧ Has value type := by
  obtain ⟨result, hlookup, hresult⟩ := lookup hfit hfield
  cases result with
  | none => exact Bool.noConfusion hresult
  | some value => exact ⟨value, hlookup, hresult⟩


/-- Optional lookup wraps presence, including present `undefined` or an inner empty option. -/
theorem optional {v : Val} {fields : List (String × Bool × Ty)}
    {name : String} {optional : Bool} {type : Ty}
    (hfit : Has v (.record fields))
    (hfield : Field.firstOf name (Ty.canon fields) = some (optional, type)) :
    ∃ result, Record.lookup v name = some result ∧ Has (result.elim .none .some) (.option type) := by
  obtain ⟨result, hlookup, hresult⟩ := lookup hfit hfield
  refine ⟨result, hlookup, ?_⟩
  cases result with
  | none => trivial
  | some value => exact hresult


/-- The single-record field rule returns the actual fitting read result in either mode. -/
theorem fieldOf {value : Val} {target answer : Ty}
    {optional : Bool} {name : String}
    (htype : Program.Record.fieldOf optional name target = some answer)
    (hfit : Has value target) :
    ∃ out, Record.read optional value name = some out ∧ Has out answer := by
  cases target with
  | record fields =>
    cases hf : Field.firstOf name fields with
    | none =>
      simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_none] at htype
      cases htype
    | some field =>
      obtain ⟨mayBeAbsent, type⟩ := field
      have hcanonical : Field.firstOf name (Ty.canon fields) = some (mayBeAbsent, type) := by
        rw [Field.firstOf_canonBy Field.bytesKey_injective]
        exact hf
      cases optional with
      | true =>
        simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
          ↓reduceIte, Option.some.injEq] at htype
        subst answer
        obtain ⟨result, hlookup, hresult⟩ := optional hfit hcanonical
        refine ⟨result.elim .none .some, ?_, hresult⟩
        simp only [Record.read, hlookup, Option.bind_eq_bind, Option.bind_some,
          ↓reduceIte]
      | false =>
        cases mayBeAbsent with
        | true =>
          simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte] at htype
          cases htype
        | false =>
          simp only [Program.Record.fieldOf, hf, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at htype
          subst answer
          obtain ⟨out, hlookup, hresult⟩ := required hfit hcanonical
          refine ⟨out, ?_, hresult⟩
          simp only [Record.read, hlookup, Option.bind_eq_bind, Option.bind_some,
            Bool.false_eq_true, ↓reduceIte]
  | _ => cases htype


/-- Field typing covers every union branch and returns an actual fitting read result. The
record-only law `fieldOf`, lifted (`UnionRule.ReadsUnion.lift_sound`). -/
theorem fieldType {value : Val} {target answer : Ty}
    {optional : Bool} {name : String}
    (htype : Program.Record.fieldType optional target name = some answer)
    (hfit : Has value target) :
    ∃ out, Record.read optional value name = some out ∧ Has out answer :=
  has_reads.lift_sound (fun _ _ typed fit => fieldOf typed fit) htype hfit


/-- A sorted frame fits a record when its names and all declared lookups fit. -/
theorem frame {fields : List (String × Bool × Ty)}
    {es : List (String × Val)}
    (hsorted : Field.Ascending Field.bytesKey es)
    (hsubset : es.map Prod.fst ⊆ (Ty.canon fields).map Prod.fst)
    (hlookup : ∀ q ∈ Ty.canon fields, match Field.firstOf q.1 es with
      | none => q.2.1 = true
      | some value => Has value q.2.2) : Has (Record.frame es) (.record fields) := by
  apply (has_record (v := Record.frame es) rfl fields).mpr
  let predicates := (Ty.canon fields).map (fun q => (q.1, pred q.2))
  have hps : Field.Ascending Field.bytesKey predicates :=
    Field.ascending_map (pred) (Field.canonBy_ascending fields)
  apply namedFit_of_sublist_lookup predicates es (Field.names_nodup_of_ascending hps)
  · apply ascending_names_sublist predicates es hps hsorted
    simpa only [predicates, List.map_map, Function.comp_def] using hsubset
  · intro q hq
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
    exact hlookup f hf


/-- Overwrite returns a fitting record with the replacement field required at its new type.
No subtype relation to the input record is asserted. -/
theorem set {value replacement : Val}
    {fields : List (String × Bool × Ty)} {name : String} {replacementType : Ty}
    (hfit : Has value (.record fields)) (hreplacement : Has replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧
      Has out (Ty.record ((name, false, replacementType) ::
        fields.filter (fun q => decide (q.1 ≠ name)))).normalize := by
  obtain ⟨es, hentries, hnamed⟩ := entries hfit
  let outputFields := (name, false, replacementType) :: fields.filter (fun q => decide (q.1 ≠ name))
  let outputEntries := Field.canonBy Field.bytesKey ((name, replacement) :: es)
  have hsubsetOld : es.map Prod.fst ⊆ (Ty.canon fields).map Prod.fst := by
    have hsub := (namedFit_names_sublist _ es hnamed).subset
    simpa only [List.map_map, Function.comp_def] using hsub
  refine ⟨Record.frame outputEntries, ?_, ?_⟩
  · simp only [Record.set, hentries, Option.bind_eq_bind, Option.bind_some, outputEntries]
  · apply (has_normalize (.record outputFields) _).mpr
    apply frame (Field.canonBy_ascending _)
    · intro n hn
      apply (Field.mem_names_canonBy Field.bytesKey_injective outputFields n).mpr
      have hraw := (Field.mem_names_canonBy Field.bytesKey_injective ((name, replacement) :: es) n).mp hn
      rcases List.mem_cons.mp hraw with rfl | hraw
      · exact List.mem_cons_self
      · by_cases hne : n = name
        · subst n
          exact List.mem_cons_self
        · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp (hsubsetOld hraw)
          apply List.mem_cons_of_mem
          refine List.mem_map.mpr ⟨q, ?_, hqn⟩
          exact List.mem_filter.mpr ⟨Field.mem_canonBy hq,
            decide_eq_true (fun h => hne (hqn.symm.trans h))⟩
    · intro q hq
      have hqlookup := Field.firstOf_of_nodup (Field.canonBy_names_nodup outputFields) hq
      rw [Field.firstOf_canonBy Field.bytesKey_injective] at hqlookup
      change Field.firstOf q.1 ((name, false, replacementType) ::
        fields.filter (fun q => decide (q.1 ≠ name))) = some q.2 at hqlookup
      change match Field.firstOf q.1 (Field.canonBy Field.bytesKey ((name, replacement) :: es)) with
        | none => q.2.1 = true
        | some value => Has value q.2.2
      rw [Field.firstOf_canonBy Field.bytesKey_injective]
      by_cases hn : name = q.1
      · simp only [Field.firstOf, if_pos hn, Option.some.injEq] at hqlookup
        simp only [Field.firstOf, if_pos hn, ← hqlookup]
        exact hreplacement
      · simp only [Field.firstOf, if_neg hn, firstOf_filter_other name q.1 hn] at hqlookup
        have hfield : Field.firstOf q.1 (Ty.canon fields) = some q.2 := by
          rw [Field.firstOf_canonBy Field.bytesKey_injective]
          exact hqlookup
        obtain ⟨result, hlookup, hresult⟩ := lookup hfit hfield
        simp only [Record.lookup, hentries, Option.map_some, Option.some.injEq] at hlookup
        simp only [Field.firstOf, if_neg hn, hlookup]
        exact hresult


/-- The record-only overwrite rule returns the actual fitting value. -/
theorem setOf {value replacement : Val} {target answer replacementType : Ty}
    {name : String}
    (htype : Program.Record.setOf name replacementType target = some answer)
    (hfit : Has value target) (hreplacement : Has replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧ Has out answer := by
  cases target with
  | record fields =>
    cases htype
    exact set hfit hreplacement
  | _ => cases htype


/-- Overwrite typing covers every union branch and returns an actual fitting value. The
record-only law `setOf`, lifted (`UnionRule.ReadsUnion.lift_sound`). -/
theorem setType {value replacement : Val} {target answer replacementType : Ty}
    {name : String}
    (htype : Program.Record.setType target name replacementType = some answer)
    (hfit : Has value target) (hreplacement : Has replacement replacementType) :
    ∃ out, Record.set value name replacement = some out ∧ Has out answer :=
  has_reads.lift_sound (fun _ _ typed fit => setOf typed fit hreplacement) htype hfit


end RecordChecks

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

/-- Record typing supplies checked argument types after the formation guard. -/
theorem termTy_record_inv {Op : Type} {sig : Signature Op} {env : TyEnv}
    {fields : List (String × Bool × Ty)} {names : List String} {values : Terms} {ty : Ty}
    (h : termTy sig env (.record fields names values) = some ty) :
    ∃ types, argsTy sig env true values = some types ∧ Record.check fields names types = some ty := by
  unfold termTy argTy at h
  split at h
  · cases h
  · exact Option.bind_eq_some_iff.mp h

/-- Fold typing supplies its parts (decisions row 228): the list's type has the list head; the
fold's type is the stated accumulator type, or the initial value's where none is stated; the
initial value's type and the body's are below it in the checker's order; and the body is typed
under the accumulator at the fold's level and the element one above it. Step of
`fold-typed-atomic-update` (R4); its consumers are the fold cases of both value judgments. -/
theorem termTy_fold_inv {Op : Type} {sig : Signature Op} {env : TyEnv} {accTy : Option Ty}
    {list init body : Term} {ty : Ty}
    (h : termTy sig env (.fold accTy list init body) = some ty) :
    ∃ listType item initType bodyType,
      termTy sig env list = some listType ∧
      Checker.listOf? listType = some item ∧
      termTy sig env init = some initType ∧
      ty = accTy.getD initType ∧
      Ty.subN initType ty = true ∧
      termTy sig (env ++ [ty, item]) body = some bodyType ∧
      Ty.subN bodyType ty = true := by
  unfold termTy argTy at h
  obtain ⟨listType, hlist, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨item, hitem, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨initType, hinit, h3⟩ := Option.bind_eq_some_iff.mp h2
  dsimp only at h3
  split at h3
  · next hsubInit =>
    obtain ⟨bodyType, hbody, h4⟩ := Option.bind_eq_some_iff.mp h3
    split at h4
    · next hsubBody =>
      cases h4
      exact ⟨listType, item, initType, bodyType, hlist, hitem, hinit, rfl, hsubInit, hbody, hsubBody⟩
    · exact nomatch h4
  · exact nomatch h3

/-- Boolean membership is closed under the checker's order, the comparison of normal forms. A
fold's accumulator is typed through it. -/
theorem Val.hasTy_subN {a b : Ty} (hsub : Ty.subN a b = true) {v : Val}
    (hv : Val.hasTy v a = true) : Val.hasTy v b = true := by
  rw [← hasTy_normalize b v []]
  refine hasTy_sub a.normalize b.normalize v [] hsub ?_
  rw [hasTy_normalize]
  exact hv

mutual
/-- Under `Fits`, an admitted native term returns a value accepted by its checked type.
Actual successful evaluation remains a premise. Record cases use `RecordChecks`.
This serves the existing straight-fragment meaning typing contract (ENSURES 6). -/
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
  | record fields names values =>
    obtain ⟨types, ht, hc⟩ := termTy_record_inv hty
    have he : (evalTerms env values).bind (Machine.Record.build names) = some v := hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hfitout⟩ := RecordChecks.build hc (evalTerms_hasTy values env tys true types vs hfit ht hvs)
    rw [hout] at hv
    cases hv
    exact hfitout
  | field mode target name =>
    have ht : (termTy nativeSignature tys target).bind (fun ty => Record.fieldType (mode = .optional) ty name) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    have he : (evalTerm env target).bind (fun value => Machine.Record.read (mode = .optional) value name) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hfitout⟩ := RecordChecks.fieldType hc (evalTerm_hasTy target env tys targetType value hfit ht he)
    rw [hout] at hv
    cases hv
    exact hfitout
  | recordSet target name replacement =>
    have ht : ((termTy nativeSignature tys target).bind fun targetType =>
      (argTy nativeSignature tys true replacement).bind fun replacementType =>
      Record.setType targetType name replacementType) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨replacementType, hr, hc⟩ := Option.bind_eq_some_iff.mp hc
    have he : ((evalTerm env target).bind fun value => (evalTerm env replacement).bind
      fun next => Machine.Record.set value name next) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨next, hn, hv⟩ := Option.bind_eq_some_iff.mp hv
    have hnext : Val.hasTy next replacementType = true := by
      rcases argTy_cases _ _ _ replacement replacementType hr with ⟨l, rfl, rfl⟩ | hr
      · exact Lit.toVal_hasTy_arg true l next hn
      · exact evalTerm_hasTy replacement env tys replacementType next hfit hr hn
    obtain ⟨out, hout, hfitout⟩ := RecordChecks.setType hc (evalTerm_hasTy target env tys targetType value hfit ht he) hnext
    rw [hout] at hv
    cases hv
    exact hfitout
  | tupleAt target index =>
    have ht : (termTy nativeSignature tys target).bind (fun targetType => Tuple.typeAt targetType index) = some ty := hty
    obtain ⟨targetType, ht, hp⟩ := Option.bind_eq_some_iff.mp ht
    have he : (evalTerm env target).bind (fun value => Val.tupleAt? value index) = some v := hev
    obtain ⟨value, he, hv⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨out, hout, hm⟩ := Tuple.typeAt_typed hp (evalTerm_hasTy target env tys targetType value hfit ht he)
    rw [hout] at hv
    cases hv
    exact hm
  -- the accumulator keeps the fold's type: the initial value is below it, every element is of
  -- the element type, and a step answers a value of the body's type, which is below it
  | fold accTy list init body =>
    obtain ⟨listType, item, initType, bodyType, hlist, hitem, hinit, _, hsubInit, hbody, hsubBody⟩ :=
      termTy_fold_inv hty
    rw [evalTerm_fold] at hev
    obtain ⟨value, hlv, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨items, hitems, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨start, hstart, hev⟩ := Option.bind_eq_some_iff.mp hev
    have hhas := Val.hasTy_subN (listOf_upper hitem)
      (evalTerm_hasTy list env tys listType value hfit hlist hlv)
    obtain ⟨items', hitems', hall⟩ := Val.hasTy_list_inv hhas
    rw [hitems] at hitems'
    cases hitems'
    refine foldlM_keeps (P := fun acc => Val.hasTy acc ty = true)
      (Q := fun x => Val.hasTy x item = true) ?_ items start v hall
      (Val.hasTy_subN hsubInit (evalTerm_hasTy init env tys initType start hfit hinit hstart))
      hev
    intro acc x next hacc hx hnext
    exact Val.hasTy_subN hsubBody (evalTerm_hasTy body (env ++ [acc, x]) (tys ++ [ty, item])
      bodyType next (hfit.append_pair hacc hx) hbody hnext)
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
/-- Under `Fits`, an admitted native term evaluates (ENSURES 7).
The atom table and record operations supply actual results for their checked arguments.
This pure-term theorem establishes no whole-program termination or host liveness. -/
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
  | record fields names values =>
    obtain ⟨types, ht, hc⟩ := termTy_record_inv hty
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (evalTerms_isSome values env tys true types hfit ht)
    obtain ⟨out, hout, _⟩ := RecordChecks.build hc (evalTerms_hasTy values env tys true types vs hfit ht hvs)
    show ((evalTerms env values).bind (Machine.Record.build names)).isSome = true
    rw [hvs, Option.bind_some, hout]
    rfl
  | field mode target name =>
    have ht : (termTy nativeSignature tys target).bind (fun ty => Record.fieldType (mode = .optional) ty name) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨value, he⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome target env tys targetType hfit ht)
    obtain ⟨out, hout, _⟩ := RecordChecks.fieldType hc (evalTerm_hasTy target env tys targetType value hfit ht he)
    show ((evalTerm env target).bind (fun value => Machine.Record.read (mode = .optional) value name)).isSome = true
    rw [he, Option.bind_some, hout]
    rfl
  | recordSet target name replacement =>
    have ht : ((termTy nativeSignature tys target).bind fun targetType =>
      (argTy nativeSignature tys true replacement).bind fun replacementType =>
      Record.setType targetType name replacementType) = some ty := hty
    obtain ⟨targetType, ht, hc⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨replacementType, hr, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨value, he⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome target env tys targetType hfit ht)
    have hnext : ∃ next, evalTerm env replacement = some next ∧ Val.hasTy next replacementType = true := by
      rcases argTy_cases _ _ _ replacement replacementType hr with ⟨l, rfl, rfl⟩ | hr
      · obtain ⟨next, hn⟩ := Option.isSome_iff_exists.mp (Lit.toVal_isSome l)
        exact ⟨next, hn, Lit.toVal_hasTy_arg true l next hn⟩
      · obtain ⟨next, hn⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome replacement env tys replacementType hfit hr)
        exact ⟨next, hn, evalTerm_hasTy replacement env tys replacementType next hfit hr hn⟩
    obtain ⟨next, hn, hnext⟩ := hnext
    obtain ⟨out, hout, _⟩ := RecordChecks.setType hc (evalTerm_hasTy target env tys targetType value hfit ht he) hnext
    show ((evalTerm env target).bind fun value => (evalTerm env replacement).bind
      fun next => Machine.Record.set value name next).isSome = true
    rw [he, Option.bind_some, hn, Option.bind_some, hout]
    rfl
  | tupleAt target index =>
    have ht : (termTy nativeSignature tys target).bind (fun targetType => Tuple.typeAt targetType index) = some ty := hty
    obtain ⟨targetType, ht, hp⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨value, he⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome target env tys targetType hfit ht)
    obtain ⟨out, hout, _⟩ := Tuple.typeAt_typed hp (evalTerm_hasTy target env tys targetType value hfit ht he)
    show ((evalTerm env target).bind (fun value => Val.tupleAt? value index)).isSome = true
    rw [he, Option.bind_some, hout]
    rfl
  -- the list and the initial value evaluate; the list's value reads as a list of the element
  -- type; each step evaluates at a fitting environment and keeps the fold's type, so the fold
  -- answers (the empty list answers the initial value)
  | fold accTy list init body =>
    obtain ⟨listType, item, initType, bodyType, hlist, hitem, hinit, _, hsubInit, hbody, hsubBody⟩ :=
      termTy_fold_inv hty
    obtain ⟨value, hlv⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome list env tys listType hfit hlist)
    have hhas := Val.hasTy_subN (listOf_upper hitem)
      (evalTerm_hasTy list env tys listType value hfit hlist hlv)
    obtain ⟨items, hitems, hall⟩ := Val.hasTy_list_inv hhas
    obtain ⟨start, hstart⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome init env tys initType hfit hinit)
    have hstep : ∀ acc x, Val.hasTy acc ty = true → Val.hasTy x item = true →
        ∃ next, evalTerm (env ++ [acc, x]) body = some next ∧ Val.hasTy next ty = true := by
      intro acc x hacc hx
      have hfit' := hfit.append_pair hacc hx
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (evalTerm_isSome body (env ++ [acc, x]) (tys ++ [ty, item]) bodyType hfit' hbody)
      exact ⟨next, hnext, Val.hasTy_subN hsubBody
        (evalTerm_hasTy body (env ++ [acc, x]) (tys ++ [ty, item]) bodyType next hfit' hbody
          hnext)⟩
    obtain ⟨v, hv, _⟩ := foldlM_answers (P := fun acc => Val.hasTy acc ty = true)
      (Q := fun x => Val.hasTy x item = true) hstep items start hall
      (Val.hasTy_subN hsubInit (evalTerm_hasTy init env tys initType start hfit hinit hstart))
    rw [evalTerm_fold, hlv, Option.bind_some, hitems, Option.bind_some, hstart,
      Option.bind_some, hv]
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

/-- A request value of a `sync` row's request type, at any instance of the row's template,
decodes to a store operation (plan §2.2, ENSURES 8): every row of `NativeOp.row` against the
patterns of `NativeOp.syncOpOf`, each request shape recovered by the inversions above. A cell or
a promise fits its handle at any argument (`Val.hasTy_refOf_inv`, `Val.hasTy_deferredOf_inv`), and
the value a `Ref` row writes or a `Deferred` row completes with is decoded at any type, so the
instance never decides the decoding (the state plan's T3a). -/
theorem syncOpOf_isSome (op : NativeOp) (σ : Ty.Subst) (env : List Val) (v : Val)
    (hv : Val.hasTy v ((NativeOp.row op).request.instantiate σ) = true)
    (hk : (NativeOp.row op).kind = .sync) : (NativeOp.syncOpOf op env v).isSome = true := by
  cases op with
  | refMake => rfl
  | refGet =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hx
    rfl
  | refGetAndSet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hx
    rfl
  | refSetAndGet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hx
    rfl
  | refUpdateWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refGetAndUpdateWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refUpdateAndGetWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refUpdateSomeWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refGetAndUpdateSomeWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refUpdateSomeAndGetWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refModifyWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | refModifySomeWith f =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refOf_inv hv
    rfl
  | deferredMakeOf value error =>
    obtain rfl := Val.hasTy_unit_inv hv
    rfl
  | deferredIsDone =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredOf_inv hv
    rfl
  | deferredPoll =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredOf_inv hv
    rfl
  | deferredSucceed =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredOf_inv hx
    rfl
  | deferredFail =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredOf_inv hx
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
theorem syncOpOf_async_none (op : NativeOp) (env : List Val) (v : Val)
    (hk : (NativeOp.row op).kind = .async) : NativeOp.syncOpOf op env v = none := by
  cases op with
  | deferredAwait => rfl
  | external _ => rfl
  | sleep => rfl
  | scopeMake strategy => cases strategy <;> simp [NativeOp.row] at hk
  | _ => simp [NativeOp.row] at hk

end Effect4.Program
