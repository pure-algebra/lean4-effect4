import Effect4.Laws.Program.DenoteB

/-!
# P4 — the store handler as a comodel of state, and budgeted iteration's limit

Formal pass, seat ALGEBRA, 2026-10-01.

**Comodel.** `storeHandler : Handler StoreSig (StateT Stores Id)` (`Laws/Program/Denote.lean:124`)
is a comodel of the store signature: a co-operation `Stores → Val × Stores` per operation
(Plotkin and Power 2008). Read against the theory of state (Plotkin and Power 2002: lookup and
update with their four equations), the question is whether the comodel satisfies the
co-equations. Heap-level put-get exists (`refPeek_poke_self`, `Machine/Stores.lean:962`); the
handler-level equations are not stated. They hold on live cells (below); on a cell the store
never allocated the handler's fallback answers `Val.unit` (`E4-DEN-CE-002`), and put-get fails
(red control). So the store is a lawful comodel of state on its live part only, which is the part
`Fits` admits.

**Iteration.** `iter` (`Laws/Program/Iter.lean:30`) is Elgot iteration cut at a budget. The tree
proves the unfolding (`iter_succ`), uniformity (`iter_uniform`) and, for the loop fragment,
monotonicity and uniqueness of finished answers (`denoteB_mono`, `meaningB_unique`). What the
limit is, is not stated. Below, for any step function over the store signature: convergence
(some budget finishes) satisfies Elgot's fixpoint law, is the least relation closed under the
loop's two rules (a least fixed point, Kleene), and is single-valued. Red control: a fixed budget
is not a solution of the fixpoint equation.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P4

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-! ## The comodel -/

/-- One store operation as a program. -/
abbrev op (o : SyncOp) : Effects.Program StoreSig Val := Effects.Program.perform (S := StoreSig) o

/-- The co-operation: one store step, with the handler's fallback. -/
theorem runP_op (o : SyncOp) (s : Stores) :
    runP (op o) s = (match syncOpStep o s with
      | some (s', v) => (v, s')
      | none => (Val.unit, s)) := by
  unfold runP
  rw [Effects.interpret_perform]
  rfl

/-- A cell the heap holds. -/
abbrev Live (s : Stores) (c : RefKey) : Prop := c.index < s.refs.length

theorem syncOp_refSet_live {s : Stores} {c : RefKey} (h : Live s c) (v : Val) :
    syncOpStep (.refSet c v) s = some ({ s with refs := s.refs.set c.index v }, Val.cell c) := by
  have hp : refPeek s.refs c = some (s.refs[c.index]'h) := List.getElem?_eq_getElem h
  show (refStep (.refSet c v) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
  simp only [refStep, hp, Option.map_some, refPoke]

theorem syncOp_refGet_live {s : Stores} {c : RefKey} (h : Live s c) :
    syncOpStep (.refGet c) s = some (s, s.refs[c.index]'h) := by
  have hp : refPeek s.refs c = some (s.refs[c.index]'h) := List.getElem?_eq_getElem h
  show (refStep (.refGet c) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
  simp only [refStep, hp, Option.map_some]

theorem syncOp_ref_dead {s : Stores} {c : RefKey} (h : ¬ Live s c) (v : Val) :
    syncOpStep (.refSet c v) s = none ∧ syncOpStep (.refGet c) s = none := by
  have hp : refPeek s.refs c = none := List.getElem?_eq_none (Nat.le_of_not_lt h)
  constructor
  · show (refStep (.refSet c v) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
    simp only [refStep, hp, Option.map_none]
  · show (refStep (.refGet c) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
    simp only [refStep, hp, Option.map_none]

/-- **put-get** on a live cell: reading after writing answers the value written. -/
theorem put_get {s : Stores} {c : RefKey} (h : Live s c) (v : Val) :
    runP (op (.refSet c v) >>= fun _ => op (.refGet c)) s =
      (v, { s with refs := s.refs.set c.index v }) := by
  have h' : Live { s with refs := s.refs.set c.index v } c := by
    unfold Live at h ⊢
    simp only [List.length_set]
    exact h
  have h1 : runP (op (.refSet c v)) s = (Val.cell c, { s with refs := s.refs.set c.index v }) := by
    rw [runP_op, syncOp_refSet_live h v]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_op, syncOp_refGet_live h']
  simp only [List.getElem_set_self]

/-- **get-get**: two reads answer the same value and leave the store, live or not. -/
theorem get_get (s : Stores) (c : RefKey) :
    runP (op (.refGet c) >>= fun a => op (.refGet c) >>= fun b => pure (a, b)) s =
      ((match syncOpStep (.refGet c) s with | some (_, v) => v | none => Val.unit,
        match syncOpStep (.refGet c) s with | some (_, v) => v | none => Val.unit), s) := by
  by_cases h : Live s c
  · have h1 : runP (op (.refGet c)) s = (s.refs[c.index]'h, s) := by
      rw [runP_op, syncOp_refGet_live h]
    rw [runP_bind, h1]
    dsimp only
    rw [runP_bind, h1]
    rw [syncOp_refGet_live h]
    rfl
  · have h1 : runP (op (.refGet c)) s = (Val.unit, s) := by
      rw [runP_op, (syncOp_ref_dead h Val.unit).2]
    rw [runP_bind, h1]
    dsimp only
    rw [runP_bind, h1]
    rw [(syncOp_ref_dead h Val.unit).2]
    rfl

/-- **put-put** on a live cell: the second write wins, as one write would. -/
theorem put_put {s : Stores} {c : RefKey} (h : Live s c) (v v' : Val) :
    runP (op (.refSet c v) >>= fun _ => op (.refSet c v')) s = runP (op (.refSet c v')) s := by
  have h' : Live { s with refs := s.refs.set c.index v } c := by
    unfold Live at h ⊢
    simp only [List.length_set]
    exact h
  have h1 : runP (op (.refSet c v)) s = (Val.cell c, { s with refs := s.refs.set c.index v }) := by
    rw [runP_op, syncOp_refSet_live h v]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_op, syncOp_refSet_live h', runP_op, syncOp_refSet_live h v']
  simp only [List.set_set]

/-- **Red control: put-get fails on a cell the store never allocated.** The fallback answers
`Val.unit` whatever was written, so the comodel is lawful for state on live cells only. -/
theorem put_get_dead_fails :
    runP (op (.refSet ⟨0⟩ (Val.nat 7)) >>= fun _ => op (.refGet ⟨0⟩)) Stores.empty ≠
      (Val.nat 7, Stores.empty) := by
  have hd : ¬ Live Stores.empty ⟨0⟩ := Nat.lt_irrefl 0
  have h1 : runP (op (.refSet ⟨0⟩ (Val.nat 7))) Stores.empty = (Val.unit, Stores.empty) := by
    rw [runP_op, (syncOp_ref_dead hd (Val.nat 7)).1]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_op, (syncOp_ref_dead hd (Val.nat 7)).2]
  intro heq
  injection heq with hv
  cases hv

/-! ## Budgeted iteration and its limit -/

section Iteration

variable {X Y : Type}

/-- Convergence: some budget finishes with this answer and these stores. -/
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

/-- A finished budget stays finished one budget later. -/
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

end Iteration

/-- The step of a two-round loop: from `0` continue at `1`, from anything else stop. -/
def twoRounds : Nat → Effects.Program StoreSig (Nat ⊕ Nat) :=
  fun n => pure (if n = 0 then .inr 1 else .inl n)

/-- **Red control: a fixed budget is not a fixpoint.** At budget 1 the loop is unfinished, while
one unfolding in front of the same budget finishes: the Elgot equation holds for the limit, not
for any single approximant. -/
theorem budget_not_fixpoint :
    iter twoRounds 1 0 ≠ (twoRounds 0 >>= iterNext (iter twoRounds 1)) := by
  intro h
  change (Effects.Program.pure none : Effects.Program StoreSig (Option Nat)) =
    Effects.Program.pure (some 1) at h
  injection h with h'
  cases h'

end FormalPass.Algebra.P4

#print axioms FormalPass.Algebra.P4.put_get
#print axioms FormalPass.Algebra.P4.get_get
#print axioms FormalPass.Algebra.P4.put_put
#print axioms FormalPass.Algebra.P4.put_get_dead_fails
#print axioms FormalPass.Algebra.P4.conv_fixpoint
#print axioms FormalPass.Algebra.P4.conv_least
#print axioms FormalPass.Algebra.P4.conv_unique
#print axioms FormalPass.Algebra.P4.budget_not_fixpoint
#print axioms FormalPass.Algebra.P4.runP_op
#print axioms FormalPass.Algebra.P4.syncOp_refSet_live
#print axioms FormalPass.Algebra.P4.syncOp_refGet_live
#print axioms FormalPass.Algebra.P4.syncOp_ref_dead
#print axioms FormalPass.Algebra.P4.iter_finished_succ
