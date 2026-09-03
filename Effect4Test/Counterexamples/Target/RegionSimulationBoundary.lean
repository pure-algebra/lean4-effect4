import Effect4Test.Semantics.RegionSimulationContract
import Effect4Test.Flow.RegionRunnerContract

/-!
Kernel witnesses for `E4-TARGET-CE-019` through `E4-TARGET-CE-021`.
The independent boundary amendment in `test/contracts/frame-simulation.contract.md`
owns the challenged claim and required replacement. These theorems expose the
current compilation mismatch; they do not revise the runner or generic frames.
The existing fallible-release fixture remains in RegionRunnerContract.
-/

namespace Effect4Test.Counterexamples.Target.RegionSimulationBoundary

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4
open Effect4.RegionSimulation
open Effects.Trace (Val)
open Effect4Test.Semantics.RegionSimulationContract
  (alphabet service nameOf admit? answerOf rblock rregion regionFlow vars
   opAcquire opRelease regionBothSucceed)

def runnerAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option Effect4.Trace.Log :=
  (admit? raw).map fun flow => Effects.Trace.project finalizerAndOutcomeMask
    (((Flow.runRegions fuel flow service nameOf tape (.nat 5)).run []).2)

def runnerResultAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option (Flow.RunResult × Flow.Tape) :=
  (admit? raw).map fun flow =>
    (((Flow.runRegions fuel flow service nameOf tape (.nat 5)).run []).1)

def machineAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option Effect4.Trace.Log :=
  (admit? raw).map fun flow => traceOfRun (FrameFiber.run
    (regionInterp alphabet flow.flow (statelessOracle alphabet flow.flow answerOf))
    (regionBound fuel) (FrameFiber.start (compileAt alphabet flow.flow
      ⟨fuel, flow.flow.entry, [.nat 5], tape⟩))).2

-- E4-TARGET-CE-019 reuses the existing E4-FLOW-CE-019/020 witness.
abbrev failingRelease := Effect4Test.Flow.RegionRunnerContract.releaseFails

theorem failingRelease_admitted : (admit? failingRelease).isSome = true := by rfl

theorem same_scope_closing_exit : runnerAt failingRelease 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
      .done (.failure (.str "boom"))] := by rfl

theorem nested_frames_thread_failure : machineAt failingRelease 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.failure (.str "boom")),
      .done (.failure (.str "boom"))] := by rfl

theorem failing_release_diverges :
    machineAt failingRelease 20 [] ≠ runnerAt failingRelease 20 [] := by decide

-- Positive control: the same two registrations, both releases succeeding.
def successfulReleases : RegionFlow String :=
  { failingRelease with blocks := failingRelease.blocks.map fun block =>
      { block with term := match block.term with
          | .acquire operation request _ target args =>
              .acquire operation request opRelease target args
          | term => term } }

theorem successfulReleases_admitted : (admit? successfulReleases).isSome = true := by rfl

theorem successful_scope_control : runnerAt successfulReleases 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
      .done (.success (.nat 5))] := by rfl

theorem successful_frames_control :
    machineAt successfulReleases 20 [] = runnerAt successfulReleases 20 [] := by rfl

-- E4-TARGET-CE-020: source fuel must stop with live work, not an empty cause.
theorem source_fuel_zero_result : runnerResultAt regionBothSucceed 0 [] =
    some (.frontier (.fuel ⟨0⟩), []) := by rfl

theorem source_fuel_zero_runner : runnerAt regionBothSucceed 0 [] = some [] := by rfl

theorem source_fuel_zero_machine : machineAt regionBothSucceed 0 [] =
    some [.done .interrupted] := by rfl

theorem source_fuel_zero_diverges :
    machineAt regionBothSucceed 0 [] ≠ runnerAt regionBothSucceed 0 [] := by decide

theorem source_fuel_after_acquire_result : runnerResultAt regionBothSucceed 2 [] =
    some (.frontier (.fuel ⟨2⟩), []) := by rfl

theorem source_fuel_after_acquire_runner : runnerAt regionBothSucceed 2 [] =
    some [] := by rfl

theorem source_fuel_after_acquire_machine : machineAt regionBothSucceed 2 [] =
    some [.finalizer 1 .interrupted, .done .interrupted] := by rfl

theorem source_fuel_after_acquire_diverges :
    machineAt regionBothSucceed 2 [] ≠ runnerAt regionBothSucceed 2 [] := by decide

-- E4-TARGET-CE-021: site 7 holds the acquired resource until a false decision.
def decisionCycle : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.choose ⟨7⟩ ⟨2⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

theorem decisionCycle_admitted : (admit? decisionCycle).isSome = true := by rfl

theorem unanswered_result : runnerResultAt decisionCycle 20 [] =
    some (.frontier (.unansweredDecision ⟨7⟩), []) := by rfl

theorem unanswered_runner : runnerAt decisionCycle 20 [] = some [] := by rfl

theorem unanswered_machine : machineAt decisionCycle 20 [] =
    some [.finalizer 1 .interrupted, .done .interrupted] := by rfl

theorem unanswered_decision_diverges :
    machineAt decisionCycle 20 [] ≠ runnerAt decisionCycle 20 [] := by decide

theorem unanswered_after_choice_result :
    runnerResultAt decisionCycle 20 [⟨⟨7⟩, true⟩] =
      some (.frontier (.unansweredDecision ⟨7⟩), []) := by rfl

theorem unanswered_after_choice_diverges :
    machineAt decisionCycle 20 [⟨⟨7⟩, true⟩] ≠
      runnerAt decisionCycle 20 [⟨⟨7⟩, true⟩] := by decide

theorem mismatched_decision_is_refusal :
    runnerResultAt decisionCycle 20 [⟨⟨8⟩, false⟩] =
      some (.refused ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, false⟩]) := by rfl

theorem completed_decision_control :
    machineAt decisionCycle 20 [⟨⟨7⟩, false⟩] =
      runnerAt decisionCycle 20 [⟨⟨7⟩, false⟩] := by rfl

theorem completed_decision_result : runnerResultAt decisionCycle 20 [⟨⟨7⟩, false⟩] =
    some (.done (.nat 5), []) := by rfl

-- The fixed stateless service is already enough to refute the unrestricted
-- finite-input trace equation, even when machine fuel meets regionBound.
def AllFiniteInputsAgree : Prop :=
  ∀ (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape),
    (admit? raw).isSome = true → machineAt raw fuel tape = runnerAt raw fuel tape

theorem unrestricted_finite_agreement_false : ¬ AllFiniteInputsAgree := by
  intro h
  exact failing_release_diverges (h failingRelease 20 [] failingRelease_admitted)

#print axioms failingRelease_admitted
#print axioms same_scope_closing_exit
#print axioms nested_frames_thread_failure
#print axioms failing_release_diverges
#print axioms successfulReleases_admitted
#print axioms successful_scope_control
#print axioms successful_frames_control
#print axioms source_fuel_zero_result
#print axioms source_fuel_zero_runner
#print axioms source_fuel_zero_machine
#print axioms source_fuel_zero_diverges
#print axioms source_fuel_after_acquire_result
#print axioms source_fuel_after_acquire_runner
#print axioms source_fuel_after_acquire_machine
#print axioms source_fuel_after_acquire_diverges
#print axioms decisionCycle_admitted
#print axioms unanswered_result
#print axioms unanswered_runner
#print axioms unanswered_machine
#print axioms unanswered_decision_diverges
#print axioms unanswered_after_choice_result
#print axioms unanswered_after_choice_diverges
#print axioms mismatched_decision_is_refusal
#print axioms completed_decision_control
#print axioms completed_decision_result
#print axioms unrestricted_finite_agreement_false

end Effect4Test.Counterexamples.Target.RegionSimulationBoundary
