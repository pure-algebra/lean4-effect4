import Effect4.Laws.Program.ReleaseCustody.CausePop
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

-- Actual cause resumption skips a saved yield continuation before consuming the lower frames.
example (b : Api.Built) (f : Effect4.Program.ReleaseCustody.Pop.Frame) (next : NCode)
    (cause : CauseV) :
    Effect4.Program.ReleaseCustody.Pop.stepCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1)
      (({f with stack := [.onSuccessConst (.yieldNowWith 0) next]}).resumeCause
        (interpAt b.program [] b.table).toPrimInterp cause none).1 ≤
      currentCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) next := by
  have held := Effect4.Program.ReleaseCustody.CausePop.resumeCause
    (Test.Dogfood.Scenario.Programs.crewAcquire 1) b.program [] b.table
    {f with stack := [.onSuccessConst (.yieldNowWith 0) next]} cause none
  simpa only [stackCredits, Nat.add_zero] using held

#axiom_audit Effect4.Laws.Program.ReleaseCustody.CausePop
