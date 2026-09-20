import Effect4.Laws.Program.TyView

/-!
# The fold condition for the subtype order (tooling plan 1.5)

`Val.hasTy` is a fold (`fold_of` at `src/Effect4/Laws/Program/Folds/Ty.lean`), so "membership respects
`sub`" is not a fact about `Val.hasTy` at all: it is a fact about *any* admission algebra whose
arms satisfy the generated condition `AdmitsSub` (`Laws/Program/TyView.lean`, one field per
constructor). Three declarations, in the order they depend on each other:

* `cata_admits_sub` — the law, proved once, by `fun_induction Ty.sub`, naming no constructor;
* `Val.hasTy_admitsSub` — the fourteen fields discharged for the admission fold of this tree;
* `hasTy_sub` — the law every caller uses, now the two applied to one another.

`hasTy_sub` lives here rather than in the core beside `Val.hasTy` because the fold lives above
the core (`Program/Folds/Ty.lean` imports `Program/Typed.lean`), and because the core keeps
definitions while the Laws keep laws: `Program/Typed.lean` carries no theorem about `sub` any
more. Every call site is under `Laws`, and all but two of them reach this module through
`Effect4.Laws.Program.TypeAlgebra`.

The carrier is the paramorphic one `fold_of` builds — `Ty × (Val → List String → Bool)`, the node
rebuilt beside its result — so every field reads the arm's `.2`. `Val.hasTy.eq_cata` is
`Val.hasTy v ty allocated = (cata_ty Val.hasTy.alg ty).snd v allocated`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine Effect4.Program.Ty

/-! ## The one real proof

By `fun_induction Ty.sub`, so the case list is `sub`'s own arm list: five exceptional rules, nine
congruence arms and a catch-all whose hypothesis is `false = true`. No constructor of `Ty` is
named by the script; each case cites the field of `AdmitsSub` that carries it. -/

theorem cata_admits_sub {alg : TyAlgebra AdmCarrier} (h : AdmitsSub alg) {a b : Ty}
    (hsub : Ty.sub a b = true) : Adm.le (cata_ty alg a).2 (cata_ty alg b).2 := by
  fun_induction Ty.sub a b
  -- the reflexive guard
  case case1 => exact Adm.le_refl _
  -- `never` admits nothing, so the inclusion is vacuous
  case case2 =>
    intro v al hp
    simp only [cata_ty, h.never] at hp
    exact Bool.noConfusion hp
  -- a union on the left is the disjunction of its members
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al hp
    simp only [cata_ty, h.union] at hp
    exact (Bool.or_eq_true_iff.mp hp).elim (fun hx => iha h1 v al hx) (fun hx => ihb h2 v al hx)
  -- a union on the right is a choice
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro v al hp
    simp only [cata_ty, h.union]
    exact (Bool.or_eq_true_iff.mp hsub).elim
      (fun hx => Bool.or_eq_true_iff.mpr (Or.inl (iha hx v al hp)))
      (fun hx => Bool.or_eq_true_iff.mpr (Or.inr (ihb hx v al hp)))
  -- the top admits everything (decisions row 46)
  case case5 =>
    intro v al _
    simp only [cata_ty]
    exact h.top v al
  -- the literal rule
  case case6 =>
    simp only [cata_ty]
    exact h.lit_string _
  -- the nine congruence arms, each its own field
  case case7 x y _ ih => simp only [cata_ty]; exact h.option _ _ (ih hsub)
  case case8 x y _ ih => simp only [cata_ty]; exact h.list _ _ (ih hsub)
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.prod _ _ _ _ (iha h1) (ihb h2)
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.except _ _ _ _ (ihe h1) (iha h2)
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.exitOf _ _ _ _ (iha h1) (ihe h2)
  case case12 e1 e2 _ ih => simp only [cata_ty]; exact h.causeOf _ _ (ih hsub)
  case case13 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.fiberOf _ _ _ _ (iha h1) (ihe h2)
  -- the invariant handles (decisions row 55, DI-17): the arm ignores its argument, so the
  -- inclusion is an equality and needs no induction hypothesis at all
  case case14 =>
    simp only [cata_ty]
    exact (h.refOf _ _) ▸ Adm.le_refl _
  case case15 =>
    simp only [cata_ty]
    exact (h.deferredOf _ _ _ _) ▸ Adm.le_refl _
  -- every other pair: `sub` answers `false`
  case case16 => exact Bool.noConfusion hsub

/-! ## The condition discharged for the admission fold of this tree

Fourteen fields, one per constructor. Six are `rfl` because the arm is a constant or reads only
its own results (`never`, `union`, `top`, `var`) or ignores its argument outright — the two
invariant handles, which is decisions row 44 (a handle is coarse by kind; the world's tables
type what it holds) stated as a law rather than left as a comment. `fiberOf` is the identity
for the same reason. The seven that inspect the value are the hand definition's own arms: the
same `dsimp only [...]` then `split at hv` that proves `Val.hasTy`'s laws, because the emitted
arm carries the matcher `Val.hasTy` wrote (`FoldOf.lean`'s `matchOnCtorDiscr`).

The whole instance depends on `[propext]` alone. -/

theorem Val.hasTy_admitsSub : AdmitsSub Val.hasTy.alg where
  never := fun _ _ => rfl
  union := fun _ _ _ _ => rfl
  top := fun _ _ => rfl
  var := fun _ _ _ => rfl
  lit_string := by
    intro s v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · exact Bool.noConfusion hv
  option := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · rename_i w
      exact h w al hv
    · exact Bool.noConfusion hv
  list := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact list_all_mono _ (fun id => h (Val.fiber id) al) hv
      · exact Bool.noConfusion hv
    · rename_i vs
      exact list_all_mono vs (fun w => h w al) hv
    · exact Bool.noConfusion hv
  prod := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i x y
      simp only [Bool.and_eq_true_iff] at hv ⊢
      exact ⟨h0 x al hv.1, h1 y al hv.2⟩
    · exact Bool.noConfusion hv
  except := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ al hv
    · exact h1 _ al hv
    · exact Bool.noConfusion hv
  exitOf := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ al hv
    · split at hv
      · exact causeAdmits_mono_sub (fun w hw => h1 w al hw) _ hv
      · exact Bool.noConfusion hv
    · exact Bool.noConfusion hv
  causeOf := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact causeAdmits_mono_sub (fun w hw => h w al hw) _ hv
    · exact Bool.noConfusion hv
  fiberOf := fun _ _ _ _ _ _ => Adm.le_refl _
  refOf := fun _ _ => rfl
  deferredOf := fun _ _ _ _ => rfl

/-- The subtype relation on `Ty` respects value typing (`hasTy`). If `Ty.sub a b = true`
and value `v` has type `a`, then `v` also has type `b`.

There is no case analysis here at all: the two lines above it are the whole proof. The law is
`cata_admits_sub` — monotonicity along `sub` is a condition on the ALGEBRA — applied to
`Val.hasTy_admitsSub` through `Val.hasTy.eq_cata`, which is what makes a new constructor of
`Ty` cost one field in the instance rather than an arm in every proof that carries membership.
Statement and argument order are unchanged from the direct proof this replaces, so no call
site moved. -/
theorem hasTy_sub (a b : Ty) (v : Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true := by
  rw [Val.hasTy.eq_cata v a allocated] at hv
  rw [Val.hasTy.eq_cata v b allocated]
  exact cata_admits_sub Val.hasTy_admitsSub hsub v allocated hv

/-! ## Monotonicity in the allocation table -/

/-- An admission algebra whose twenty arms satisfy `AdmitsExtend` has a fold that preserves
extension of the allocation table. -/
theorem cata_admits_extend {alg : TyAlgebra AdmCarrier} (h : AdmitsExtend alg) (ty : Ty) :
    Adm.Extends (cata_ty alg ty).2 := by
  fun_induction cata_ty alg ty
  case case1 => exact h.never
  case case2 => exact h.unit
  case case3 => exact h.nat
  case case4 => exact h.int
  case case5 => exact h.string
  case case6 => exact h.bool
  case case7 target => exact h.handle target
  case case8 _ ih => exact h.option _ ih
  case case9 _ ih => exact h.list _ ih
  case case10 _ _ ih1 ih2 => exact h.prod _ _ ih1 ih2
  case case11 _ _ ih1 ih2 => exact h.except _ _ ih1 ih2
  case case12 _ _ ih1 ih2 => exact h.exitOf _ _ ih1 ih2
  case case13 _ ih => exact h.causeOf _ ih
  case case14 _ _ ih1 ih2 => exact h.fiberOf _ _ ih1 ih2
  case case15 _ _ ih1 ih2 => exact h.union _ _ ih1 ih2
  case case16 value => exact h.lit value
  case case17 _ ih => exact h.refOf _ ih
  case case18 _ _ ih1 ih2 => exact h.deferredOf _ _ ih1 ih2
  case case19 index => exact h.var index
  case case20 => exact h.unknown

/-- The extension condition discharged for `Val.hasTy.alg`. -/
theorem Val.hasTy_admitsExtend : AdmitsExtend Val.hasTy.alg where
  never := fun _ _ _ _ hv => by
    dsimp only [Val.hasTy.alg] at hv
    exact Bool.noConfusion hv
  unit := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  nat := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  int := fun _ _ _ _ hv => by
    dsimp only [Val.hasTy.alg] at hv
    exact Bool.noConfusion hv
  string := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  bool := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  handle := by
    intro target v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact hv
      · exact hv
      · exact hv
      · obtain ⟨ht, hi⟩ := Bool.and_eq_true_iff.mp hv
        simp only [ht]
        exact beq_iff_eq.mpr (ext _ target (beq_iff_eq.mp hi))
      · exact Bool.noConfusion hv
    · exact hv
  option := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · rename_i w
      exact h0 w a b ext hv
    · exact Bool.noConfusion hv
  list := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact list_all_mono _ (fun id => h0 (Val.fiber id) a b ext) hv
      · exact Bool.noConfusion hv
    · rename_i vs
      exact list_all_mono vs (fun w => h0 w a b ext) hv
    · exact Bool.noConfusion hv
  prod := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i x y
      simp only [Bool.and_eq_true_iff] at hv ⊢
      exact ⟨h0 x a b ext hv.1, h1 y a b ext hv.2⟩
    · exact Bool.noConfusion hv
  except := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ a b ext hv
    · exact h1 _ a b ext hv
    · exact Bool.noConfusion hv
  exitOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ a b ext hv
    · split at hv
      · exact causeAdmits_mono_sub (fun w hw => h1 w a b ext hw) _ hv
      · exact Bool.noConfusion hv
    · exact Bool.noConfusion hv
  causeOf := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact causeAdmits_mono_sub (fun w hw => h0 w a b ext hw) _ hv
    · exact Bool.noConfusion hv
  fiberOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  union := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    obtain h | h := Bool.or_eq_true_iff.mp hv
    · exact Bool.or_eq_true_iff.mpr (Or.inl (h0 v a b ext h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (h1 v a b ext h))
  lit := by
    intro s v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  refOf := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  deferredOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  var := fun _ _ _ _ _ hv => by
    dsimp only [Val.hasTy.alg] at hv
    exact Bool.noConfusion hv
  unknown := fun _ _ _ _ _ => rfl

/-- Membership is monotone in the allocation table at every type. -/
theorem hasTy_mono (ty : Ty) (v : Val) (a b : List String)
    (ext : Extends a b) (typed : Val.hasTy v ty a = true) : Val.hasTy v ty b = true := by
  rw [Val.hasTy.eq_cata v ty a] at typed
  rw [Val.hasTy.eq_cata v ty b]
  exact cata_admits_extend Val.hasTy_admitsExtend ty v a b ext typed

/-- In cause admission, discarding the type argument makes the choice of type irrelevant. -/
theorem causeAdmits_discard_ty (m : Val → Bool) (t1 t2 : Ty) (c : CauseV) :
    causeAdmits (fun w _ => m w) t1 c = causeAdmits (fun w _ => m w) t2 c := by
  apply List.all_congr rfl
  intro r
  cases r with
  | fail e _ => dsimp only [reasonAdmits]
  | die _ _ => rfl
  | interrupt _ _ => rfl

/-- What an admission algebra satisfies when its arms respect equality of admitted values.
The congruence arms preserve pointwise agreement of their subterm admissions; the coarse
handles ignore normalisation of their arguments. -/
structure AdmitsNormalize (alg : TyAlgebra AdmCarrier) : Prop where
  option : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_option p0).2 = (alg.ty_option q0).2
  list : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_list p0).2 = (alg.ty_list q0).2
  except : ∀ p0 p1 q0 q1, (p0).2 = (q0).2 → (p1).2 = (q1).2 → (alg.ty_except p0 p1).2 = (alg.ty_except q0 q1).2
  exitOf : ∀ p0 p1 q0 q1, (p0).2 = (q0).2 → (p1).2 = (q1).2 → (alg.ty_exitOf p0 p1).2 = (alg.ty_exitOf q0 q1).2
  causeOf : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_causeOf p0).2 = (alg.ty_causeOf q0).2
  fiberOf : ∀ p0 p1 q0 q1, (alg.ty_fiberOf p0 p1).2 = (alg.ty_fiberOf q0 q1).2
  refOf : ∀ p0 q0, (alg.ty_refOf p0).2 = (alg.ty_refOf q0).2
  deferredOf : ∀ p0 p1 q0 q1, (alg.ty_deferredOf p0 p1).2 = (alg.ty_deferredOf q0 q1).2

/-- The congruence condition for normalisation discharged for `Val.hasTy.alg`. -/
theorem Val.hasTy_admitsNormalize : AdmitsNormalize Val.hasTy.alg where
  option := fun _ _ h => by dsimp only [Val.hasTy.alg]; rw [h]
  list := fun _ _ h => by dsimp only [Val.hasTy.alg]; rw [h]
  except := fun _ _ _ _ h0 h1 => by dsimp only [Val.hasTy.alg]; rw [h0, h1]
  exitOf := by
    intro p0 p1 q0 q1 h0 h1
    dsimp only [Val.hasTy.alg]
    rw [h0, h1]
    funext v allocated
    split
    · rfl
    · split
      · exact causeAdmits_discard_ty (fun w => q1.snd w allocated) p1.fst q1.fst _
      · rfl
    · rfl
  causeOf := by
    intro p0 q0 h
    dsimp only [Val.hasTy.alg]
    rw [h]
    funext v allocated
    split
    · exact causeAdmits_discard_ty (fun w => q0.snd w allocated) p0.fst q0.fst _
    · rfl
  fiberOf := fun _ _ _ _ => rfl
  refOf := fun _ _ => rfl
  deferredOf := fun _ _ _ _ => rfl

end Effect4.Program

