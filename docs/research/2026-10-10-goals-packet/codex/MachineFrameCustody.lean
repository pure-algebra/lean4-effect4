import Effect4.Laws.Program.ReleaseCustody.FrameDebit
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

-- The actual native frame evaluator and actual source-indexed trace are read together.
example (b : Api.Built) (f : Effect4.Program.ReleaseCustody.Pop.Frame) :
    Effect4.Program.ReleaseCustody.FrameDebit.starts (Test.Dogfood.Scenario.Programs.crewAcquire 1)
        (f.step (interpAt b.program [] b.table).toPrimInterp).2 +
      Effect4.Program.ReleaseCustody.Pop.stepCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1)
        (f.step (interpAt b.program [] b.table).toPrimInterp).1 ≤
      currentCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) f.current +
        stackCredits (Test.Dogfood.Scenario.Programs.crewAcquire 1) f.current f.stack +
        Effect4.Program.ReleaseCustody.FrameDebit.registrations (Test.Dogfood.Scenario.Programs.crewAcquire 1)
          (f.step (interpAt b.program [] b.table).toPrimInterp).2 :=
  Effect4.Program.ReleaseCustody.FrameDebit.step _ b.program [] b.table f

#axiom_audit Effect4.Laws.Program.ReleaseCustody.FrameDebit
