import Effect4.Laws.Program.Agreement.Machine

/-!
# Composition with a named straight-fragment observation

Concept 10, proposed registry claim `straight-composition-agreement`, R8; placement and
limits are recorded before proof work in `docs/research/2026-10-03-api-completion/plan.md`.
`StraightEq` relates the existing meanings: exit and complete stores at every environment
and store. Its runtime consumer is `StraightEq.run_agrees`; suspension removal and the
constructor congruences let authoring proofs use that consumer compositionally.

This is the straight-fragment contribution to T5. It does not compare arbitrary scheduled
programs, traces, finite-fuel frontiers, host tables or target execution. No program syntax
or runtime transformation is introduced.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Agreement

/-- Equality of exit and complete stores on the existing straight fragment. The fragment
witnesses prevent the denotation's outside-fragment fallback from admitting comparisons. -/
structure StraightEq (left right : NativeEff) : Prop where
  left_straight : Straight left = true
  right_straight : Straight right = true
  same : ∀ env stores, meaning left env stores = meaning right env stores

namespace StraightEqWanted

/-- `straight-composition-agreement`: compare executions at their own sufficient budgets,
with the exit/store observation of the existing denotation contract, E4-DEN-CE-003/004/005. -/
theorem run_agrees (a b : NativeEff) (_h : StraightEq a b) (fa fb : Nat)
    (_da : depth a ≤ fa) (_sa : 2 * steps a + 6 ≤ fa)
    (_db : depth b ≤ fb) (_sb : 2 * steps b + 6 ≤ fb) :
    ProofGraph.Obligation
      ((Api.run a fa).outcome = .finished ∧ (Api.run b fb).outcome = .finished ∧
        (Api.run a fa).exit = (Api.run b fb).exit ∧
        (Api.run a fa).stores = (Api.run b fb).stores) := ⟨⟩

end StraightEqWanted

namespace StraightEq

/-- Reflexivity on the admitted fragment; helper for the composition/run connector. -/
theorem refl (e : NativeEff) (he : Straight e = true) : StraightEq e e :=
  ⟨he, he, fun _ _ => rfl⟩

theorem symm {a b : NativeEff} (h : StraightEq a b) : StraightEq b a :=
  ⟨h.right_straight, h.left_straight, fun env stores => (h.same env stores).symm⟩

theorem trans {a b c : NativeEff} (hab : StraightEq a b) (hbc : StraightEq b c) :
    StraightEq a c :=
  ⟨hab.left_straight, hbc.right_straight,
    fun env stores => (hab.same env stores).trans (hbc.same env stores)⟩

/-- Removing a suspension changes source shape and step counts, but not this observation. -/
theorem suspend_remove (e : NativeEff) (he : Straight e = true) : StraightEq (.suspend e) e :=
  ⟨he, he, fun _ _ => rfl⟩

theorem suspend_congr {a b : NativeEff} (h : StraightEq a b) :
    StraightEq (.suspend a) (.suspend b) :=
  ⟨h.left_straight, h.right_straight, h.same⟩

theorem bind {a a' b b' : NativeEff} (ha : StraightEq a a') (hb : StraightEq b b') :
    StraightEq (.bind a b) (.bind a' b') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Straight, ha.left_straight, hb.left_straight, Bool.and_self]
  · simp only [Straight, ha.right_straight, hb.right_straight, Bool.and_self]
  · intro env stores
    simp only [meaning_bind, ha.same, hb.same]

theorem select (t : Term) (d : Decision) {a a' b b' : NativeEff}
    (ha : StraightEq a a') (hb : StraightEq b b') :
    StraightEq (.select t d a b) (.select t d a' b') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Straight, ha.left_straight, hb.left_straight, Bool.and_self]
  · simp only [Straight, ha.right_straight, hb.right_straight, Bool.and_self]
  · intro env stores
    cases hd : (evalTerm env t).bind d.decide with
    | none => rw [meaning_select_bad _ _ _ _ _ _ hd, meaning_select_bad _ _ _ _ _ _ hd]
    | some result =>
      obtain ⟨flag, bound⟩ := result
      cases flag with
      | false =>
        rw [meaning_select_false _ _ _ _ _ _ hd, meaning_select_false _ _ _ _ _ _ hd]
        exact hb.same _ _
      | true =>
        rw [meaning_select_true _ _ _ _ _ _ hd, meaning_select_true _ _ _ _ _ _ hd]
        exact ha.same _ _

theorem exit {a b : NativeEff} (h : StraightEq a b) : StraightEq (.exit a) (.exit b) := by
  refine ⟨h.left_straight, h.right_straight, ?_⟩
  intro env stores
  simp only [meaning_exit, h.same]

theorem catchCause {a a' h h' : NativeEff} (ha : StraightEq a a') (hh : StraightEq h h') :
    StraightEq (.catchCause a h) (.catchCause a' h') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Straight, ha.left_straight, hh.left_straight, Bool.and_self]
  · simp only [Straight, ha.right_straight, hh.right_straight, Bool.and_self]
  · intro env stores
    simp only [meaning_catchCause, ha.same, hh.same]

theorem matchCause {a a' v v' c c' : NativeEff}
    (ha : StraightEq a a') (hv : StraightEq v v') (hc : StraightEq c c') :
    StraightEq (.matchCause a v c) (.matchCause a' v' c') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Straight, ha.left_straight, hv.left_straight, hc.left_straight, Bool.and_self]
  · simp only [Straight, ha.right_straight, hv.right_straight, hc.right_straight, Bool.and_self]
  · intro env stores
    simp only [meaning_matchCause, ha.same, hv.same, hc.same]

theorem onExit {a a' f f' : NativeEff} (ha : StraightEq a a') (hf : StraightEq f f') :
    StraightEq (.onExit a f) (.onExit a' f') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Straight, ha.left_straight, hf.left_straight, Bool.and_self]
  · simp only [Straight, ha.right_straight, hf.right_straight, Bool.and_self]
  · intro env stores
    simp only [meaning_onExit, ha.same, hf.same]

/-- Runtime consumer of straight-fragment composition. Budgets may differ: a rewrite can
change its step bound. The observation includes state retained after failure/finalization;
trace equality and insufficient-budget executions are outside this statement. -/
theorem run_agrees {a b : NativeEff} (h : StraightEq a b) (fa fb : Nat)
    (da : depth a ≤ fa) (sa : 2 * steps a + 6 ≤ fa)
    (db : depth b ≤ fb) (sb : 2 * steps b + 6 ≤ fb) :
    (Api.run a fa).outcome = .finished ∧ (Api.run b fb).outcome = .finished ∧
      (Api.run a fa).exit = (Api.run b fb).exit ∧
      (Api.run a fa).stores = (Api.run b fb).stores := by
  obtain ⟨ha, ea, sta⟩ := run_eq_meaning a fa h.left_straight da sa
  obtain ⟨hb, eb, stb⟩ := run_eq_meaning b fb h.right_straight db sb
  have same := h.same [] Stores.empty
  refine ⟨ha, hb, ?_, ?_⟩
  · rw [ea, eb, same]
  · rw [sta, stb, same]

/-- A sufficient bound computed from the existing compilation-depth and step measures. -/
def fuelFor (e : NativeEff) : Nat := max (depth e) (2 * steps e + 6)

/-- Convenience consumer: the existing structural bounds discharge all fuel premises. -/
theorem run_agrees_at_bound {a b : NativeEff} (h : StraightEq a b) :
    (Api.run a (fuelFor a)).outcome = .finished ∧
      (Api.run b (fuelFor b)).outcome = .finished ∧
      (Api.run a (fuelFor a)).exit = (Api.run b (fuelFor b)).exit ∧
      (Api.run a (fuelFor a)).stores = (Api.run b (fuelFor b)).stores :=
  h.run_agrees _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end StraightEq

#obligation_proved StraightEqWanted.run_agrees := @StraightEq.run_agrees
#typed_state_obligations Effect4.Program.Denote.StraightEqWanted ceiling 0 using aesop

end Effect4.Program.Denote
