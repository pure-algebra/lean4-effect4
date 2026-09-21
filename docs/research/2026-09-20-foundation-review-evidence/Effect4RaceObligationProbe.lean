import Effect4.Laws.Program.Intro.Weight

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

#check @Effect4.Program.Sched.M1Origin.actionAt_raceAll
#check @Effect4.Program.Sched.actionAt_raceAll
#check @Effect4.Program.Sched.M1Origin.actionAt_fork
#check @Effect4.Program.Sched.actionAt_fork

namespace ResidueProbe

def root : NativeEff := .withFiber (.raceAll .nil)
def point : Point := rootPoint 0

theorem decoded : actionAt root point = some (.raceAll [] (some [0, 0])) := rfl

/-- Refutes the proposition stored by the actual declared obligation at concrete inputs.
The arbitrary action is getId, while the actual source action is raceAll. -/
theorem frozen_raceAll_counterexample :
    ¬ (Effect4.Program.Sched.M1Origin.actionAt_raceAll
      (root := root) (p := point) (a := .getId)
      (site := some [0, 0]) (entrants := []) decoded).statement := by
  intro h
  obtain ⟨es, impossible, _⟩ := h
  cases impossible

/-- The missing-premise statement is also false as a universally quantified proposition. -/
theorem universal_missing_premise_false :
    ¬ (∀ (r : NativeEff) (p : Point) (a : ActionTerm NativeOp)
      (site : Option (List Nat)) (entrants : List NCode),
      actionAt r p = some (.raceAll entrants site) →
      ∃ es, a = .raceAll es ∧ entrants = actionAt.entrants es ((p.child 0).child 0)) := by
  intro h
  obtain ⟨es, impossible, _⟩ := h root point .getId (some [0, 0]) [] decoded
  cases impossible

#print axioms decoded
#print axioms frozen_raceAll_counterexample
#print axioms universal_missing_premise_false

end ResidueProbe
