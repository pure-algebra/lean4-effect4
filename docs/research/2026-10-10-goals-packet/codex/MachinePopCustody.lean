import Effect4.Laws.Program.ReleaseCustody.Pop
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

/-! Readers apply the actual native value pop and its saved constant to a worker acquisition identity.
They establish no whole-command closure or source-use uniqueness. -/
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

example (b : Api.Built) (f : Effect4.Program.ReleaseCustody.Pop.Frame) (next : NCode) :
    Effect4.Program.ReleaseCustody.Pop.stepCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1)
      (({f with stack := [.onSuccessConst (.yieldNowWith 0) next]}).resumeValue
        (interpAt b.program [] b.table).toPrimInterp Val.unit none).1 ≤
      currentCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) next := by
  have held := Effect4.Program.ReleaseCustody.Pop.resumeValue
    (Test.Dogfood.Scenario.Programs.crewAcquire 1) b.program [] b.table
    {f with stack := [.onSuccessConst (.yieldNowWith 0) next]} Val.unit none
  simpa only [stackCredits, Nat.add_zero] using held

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Evaluation
  Effect4.Laws.Program.ReleaseCustody.Producers Effect4.Laws.Program.ReleaseCustody.Pop
