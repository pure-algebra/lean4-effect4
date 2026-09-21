import Effect4.Laws.Program.Intro.Weight
import Effect4.Laws.Program.Simulation.Actions

/-! E4-SCHED-CE-004: the source-location premise is required by the race action
statement. The arbitrary action below is getId, while the source contains raceAll. -/
namespace Test.Counterexamples.ActionAtRaceAllPremise
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

def root : NativeEff := .withFiber (.raceAll .nil)
def point : Point := rootPoint 0

theorem decoded : actionAt root point = some (.raceAll [] (some [0, 0])) := rfl

theorem universal_missing_premise_false :
    ¬ (∀ (r : NativeEff) (p : Point) (a : ActionTerm NativeOp)
      (site : Option (List Nat)) (entrants : List NCode),
      actionAt r p = some (.raceAll entrants site) →
      ∃ es, a = .raceAll es ∧ entrants = actionAt.entrants es ((p.child 0).child 0)) := by
  intro h
  obtain ⟨es, impossible, _⟩ := h root point .getId (some [0, 0]) [] decoded
  cases impossible

#print axioms universal_missing_premise_false
end Test.Counterexamples.ActionAtRaceAllPremise

/-! E4-SCHED-CE-005: all three premise-free action relations fail when the two
machines have unrelated fresh-id supplies. The code and answer relations still hold. -/
namespace Test.Counterexamples.ActionsPremises
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

def root : NativeEff := .withFiber .getId
def m₁ : FMachine := RunMachine.empty Stores.empty
def m₂ : RState := { RunMachine.empty Stores.empty with nextId := 1 }
def f₁ : FRun := RunFiber.make ⟨0⟩ (.success .unit) true (0, false) emptyCtx
def f₂ : RFiber := RunFiber.make ⟨0⟩ (.pure (.success .unit)) true (0, false) emptyCtx

def a₁ : FAnswer := FiberAction.coreAnswer
def a₂ : RAnswer := answerWith (fun v => .pure (.success v))
theorem programs : CodeMeans root (.success .unit) (.pure (.success .unit)) := CodeMeans.success _

theorem answers : AnswerRel root a₁ a₂ := answerRel_core root (fun v => CodeMeans.success v)

theorem fork_counterexample :
    ¬ IterRel root
      (FiberAction.fork (interpAt root []) m₁ f₁ false (.success .unit) { startImmediately := true, daemon := true, maskMode := .inherit } a₁)
      (FiberAction.fork (interpRAt root []) m₂ f₂ false (.pure (.success .unit)) { startImmediately := true, daemon := true, maskMode := .inherit } a₂) := by
  intro h
  have bad := h.machine.nextId
  change 1 = 2 at bad
  cases bad

theorem forkIn_counterexample :
    ¬ IterRel root
      (FiberAction.forkIn (interpAt root []) m₁ f₁ false (.success .unit) { startImmediately := true, daemon := true, maskMode := .inherit } 0 a₁)
      (FiberAction.forkIn (interpRAt root []) m₂ f₂ false (.pure (.success .unit)) { startImmediately := true, daemon := true, maskMode := .inherit } 0 a₂) := by
  intro h
  have bad := h.machine.nextId
  change 1 = 2 at bad
  cases bad

theorem raceAll_counterexample :
    ¬ IterRel root
      (FiberAction.raceAll (interpAt root []) m₁ f₁ false [] none)
      (FiberAction.raceAll (interpRAt root []) m₂ f₂ false [] none) := by
  intro h
  have bad := h.machine.nextId
  change 0 = 1 at bad
  cases bad
#print axioms fork_counterexample
#print axioms forkIn_counterexample
#print axioms raceAll_counterexample
end Test.Counterexamples.ActionsPremises
