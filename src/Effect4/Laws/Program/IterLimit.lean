import Effect4.Laws.Program.DenoteB

/-!
# Program.IterLimit: the limit of the budgeted meaning

Formal pass, algebra note A8 (`docs/research/2026-10-01-formal-pass/algebra/note.md` §2.3; probe
`algebra/probes/P4ComodelIteration.lean`, confirmed by its verifier as ALG-08). `iter f k x`
(`Iter.lean`) is the `k`-th approximant of a loop's unfolding equation. `Program` is well
founded, so it has no iteration operator of its own: the budgeted meaning is the Kleene chain of
the least fixed point, and the meaning of a loop is the limit of that chain, the answer some
budget finishes with. `Conv f x s y s'` names that limit for a step over the store signature run
from the stores `s` (`runP`, `DenoteB.lean`); it lives here and not in `Iter.lean`, which is
generic over the signature and runs nothing.

Elgot's laws hold for the limit, never for one budget:

* `conv_fixpoint`, the fixpoint law: the loop converges exactly when its step stops with that
  answer, or continues to a cursor from which the loop converges;
* `conv_least`, leastness: convergence is contained in every relation closed under the loop's two
  rules, so it is the least fixed point (Kleene);
* `conv_unique`: convergence is single-valued, stores included, the generic form of
  `meaningB_unique` (`DenoteB.lean`), from `iter_finished_succ`;
* the red control `budget_not_fixpoint` (`Test/Program/IterLimit.lean`): at budget 1 a two-round
  loop is unfinished while one unfolding in front of the same budget finishes, so no single
  approximant solves the fixpoint equation.

Uniformity already holds at every budget (`iter_uniform`). Naturality, dinaturality and the
codiagonal (nested loops as one loop) are not stated: they are owed only when a form or a printer
step declares a loop rewrite (R10), and no milestone needs them.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

variable {X Y : Type}

/-- Convergence of a budgeted loop: some budget finishes with the answer `y` and the stores
`s'`. -/
def Conv (f : X → Effects.Program StoreSig (Y ⊕ X)) (x : X) (s : Stores) (y : Y) (s' : Stores) :
    Prop :=
  ∃ k, runP (iter f k x) s = (some y, s')

/-- **Elgot's fixpoint law, for the limit.** The loop converges exactly when its step stops with
that answer, or continues to a cursor from which the loop converges. -/
theorem conv_fixpoint (f : X → Effects.Program StoreSig (Y ⊕ X)) (x : X) (s : Stores) (y : Y)
    (s' : Stores) :
    Conv f x s y s' ↔
      runP (f x) s = (.inl y, s') ∨ ∃ x' s₁, runP (f x) s = (.inr x', s₁) ∧ Conv f x' s₁ y s' := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      rw [iter_zero, runP_pure] at hk
      cases hk
    | succ k =>
      rw [iter_succ, runP_bind] at hk
      rcases hr : runP (f x) s with ⟨r, s₁⟩
      rw [hr] at hk
      cases r with
      | inl y₀ =>
        rw [show iterNext (iter f k) (Sum.inl y₀) = pure (some y₀) from rfl, runP_pure] at hk
        cases hk
        exact .inl rfl
      | inr x' =>
        exact .inr ⟨x', s₁, rfl, k, hk⟩
  · rintro (h | ⟨x', s₁, h, k, hk⟩)
    · refine ⟨1, ?_⟩
      rw [iter_succ, runP_bind, h]
      rfl
    · refine ⟨k + 1, ?_⟩
      rw [iter_succ, runP_bind, h]
      exact hk

/-- **The limit is the least solution.** Any relation closed under the loop's two rules contains
convergence (Kleene: the budget chain's limit is the least fixed point). -/
theorem conv_least (f : X → Effects.Program StoreSig (Y ⊕ X))
    (R : X → Stores → Y → Stores → Prop)
    (stop : ∀ x s y s', runP (f x) s = (.inl y, s') → R x s y s')
    (step : ∀ x s x' s₁ y s', runP (f x) s = (.inr x', s₁) → R x' s₁ y s' → R x s y s') :
    ∀ x s y s', Conv f x s y s' → R x s y s' := by
  intro x s y s' ⟨k, hk⟩
  induction k generalizing x s with
  | zero =>
    rw [iter_zero, runP_pure] at hk
    cases hk
  | succ k ih =>
    rw [iter_succ, runP_bind] at hk
    rcases hr : runP (f x) s with ⟨r, s₁⟩
    rw [hr] at hk
    cases r with
    | inl y₀ =>
      rw [show iterNext (iter f k) (Sum.inl y₀) = pure (some y₀) from rfl, runP_pure] at hk
      simp only [Prod.mk.injEq, Option.some.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact stop x s _ _ hr
    | inr x' =>
      exact step x s x' s₁ y s' hr (ih x' s₁ hk)

/-- A finished budget stays finished one budget later, with the same answer and stores. -/
theorem iter_finished_succ (f : X → Effects.Program StoreSig (Y ⊕ X)) :
    ∀ (k : Nat) (x : X) (s : Stores) (y : Y) (s' : Stores),
      runP (iter f k x) s = (some y, s') → runP (iter f (k + 1) x) s = (some y, s') := by
  intro k
  induction k with
  | zero =>
    intro x s y s' hk
    rw [iter_zero, runP_pure] at hk
    cases hk
  | succ k ih =>
    intro x s y s' hk
    rw [iter_succ, runP_bind] at hk ⊢
    rcases hr : runP (f x) s with ⟨r, s₁⟩
    rw [hr] at hk
    cases r with
    | inl y₀ => exact hk
    | inr x' => exact ih x' s₁ y s' hk

/-- **The limit is single-valued**: two finishing budgets agree, stores included. -/
theorem conv_unique (f : X → Effects.Program StoreSig (Y ⊕ X)) (x : X) (s : Stores)
    {y y' : Y} {s₁ s₂ : Stores} (h : Conv f x s y s₁) (h' : Conv f x s y' s₂) :
    y = y' ∧ s₁ = s₂ := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  have up : ∀ (j n : Nat) (y₀ : Y) (s₀ : Stores), runP (iter f n x) s = (some y₀, s₀) →
      runP (iter f (n + j) x) s = (some y₀, s₀) := by
    intro j
    induction j with
    | zero => intro n y₀ s₀ hn; exact hn
    | succ j ih =>
      intro n y₀ s₀ hn
      rw [← Nat.add_assoc]
      exact iter_finished_succ f (n + j) x s y₀ s₀ (ih n y₀ s₀ hn)
  have a := up k' k y s₁ hk
  have b := up k k' y' s₂ hk'
  rw [Nat.add_comm] at b
  rw [a] at b
  cases b
  exact ⟨rfl, rfl⟩

end Effect4.Program.Denote
