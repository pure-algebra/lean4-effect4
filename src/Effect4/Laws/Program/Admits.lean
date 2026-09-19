import Effect4.Laws.Program.TyView

/-!
# The fold condition for the subtype order (tooling plan 1.5)

`Val.hasTy` is a fold (`fold_of` at `src/Effect4/Program/Folds/Ty.lean`), so "membership respects
`sub`" is not a fact about `Val.hasTy` at all: it is a fact about *any* admission algebra whose
arms satisfy the generated condition `AdmitsSub` (`Laws/Program/TyView.lean`, one field per
constructor). This module proves that once: `cata_admits_sub`. Discharging the condition for
`Val.hasTy` itself is the mechanical half and is not here; the closing section says exactly what
is left and why.

What that buys, and what it costs. `hasTy_sub` itself stays where it is
(`src/Effect4/Program/Typed.lean`): it is below the fold in the import order, twenty-five call
sites in five files read it, and its own proof is now `fun_induction Ty.sub` at seventy-nine
lines. What is new here is the **generic** statement, which is what L2 needs: `Val.hasTyWith`
under an oracle, `Val.hasTyIn` at a world, and any later admission fold get their monotonicity by
discharging fifteen fields rather than by re-proving a two-hundred-line case analysis.
The claim that the existing law is an instance is therefore still a claim; what is proved here
is the generic law it would be an instance of.

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

/-! ## What is owed: the condition discharged for `Val.hasTy`

`Val.hasTy_admitsSub : AdmitsSub Val.hasTy.alg` is **not** here, and the reason is worth writing
down because it is a property of `fold_of`'s output, not of the design.

Five of the fifteen fields are immediate — `never`, `union`, `top`, `var` and the two invariant
handles are `rfl`, because the generated arms are literally `fun v al => false`,
`fun v al => p.2 v al || q.2 v al`, `fun v al => true` and (for `refOf`/`deferredOf`) functions
that ignore their argument, which is decisions row 44 stated as a law. `lit_string` and `option`
close by `cases v` in three lines each.

The remaining seven (`list`, `prod`, `except`, `exitOf`, `causeOf`, `fiberOf` and the `handle`
side of the leaves) inspect the VALUE, and `fold_of` emits those arms through the compiler's
sparse case analyses (`Val.hasTy._sparseCasesOn_37` and kin, one per reachable frame group)
rather than through `Val`'s own matcher. `split` refuses them — "Could not split an `if` or
`match` expression" — so each needs a `cases v` walk over `Val`'s frames with the two-cell and
snapshot sub-cases spelled out, rather than the four-line `split at hv` the hand `Val.hasTy`
admits. That is mechanical and perhaps eighty lines; it is not a design question and it is not
attempted here.

Until it lands, `hasTy_sub` (`src/Effect4/Program/Typed.lean`) is the law every caller uses, and
it is proved directly by `fun_induction Ty.sub` at seventy-nine lines. What `cata_admits_sub`
adds today is the statement L2 needs — that monotonicity along `sub` is a condition on the
ALGEBRA and not a property of one fold — proved once, so `Val.hasTyWith` under an oracle and any
later admission fold discharge fifteen fields instead of re-proving a case analysis.
-/

end Effect4.Program
