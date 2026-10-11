import Test.Dogfood.Scenario.Workers.Assertions
import ProofGraph.AxiomAudit
import ProofGraph.Plan
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody

example (b : Api.Built) (cf : Nat) (q : List Nat) (m : NativeMachine)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program) (history : Run.HistoryOf b cf m) :
    m.trace.countP (ReleaseTrace.releaseAt q) ≤ m.trace.countP (ReleaseTrace.registeredAt q) :=
  Control.Funded.read (Execution.history b cf q m fragment sequential raceFree history).funded

example (total cf : Nat) (b : Api.Built) (m : NativeMachine) (row : Nat × NativeDecision)
    (built : Api.Author.build (Test.Dogfood.Scenario.Workers.crew total) = .ok b)
    (held : Test.Dogfood.Scenario.Workers.Assertions.Holds b cf m)
    (accepted : Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m row.2) :
    Test.Dogfood.Scenario.Workers.Assertions.ReleaseDebits (Run.stepBy b m row) :=
  Test.Dogfood.Scenario.Workers.Assertions.releases_step total cf b m row built held accepted

#axiom_audit Effect4.Laws.Program.ReleaseCustody.HistoryLift Effect4.Laws.Program.ReleaseCustody.Execution
#plan_status Effect4.Program.ReleaseCustody.Execution.history
#plan_status Test.Dogfood.Scenario.Workers.Assertions.releases_step
