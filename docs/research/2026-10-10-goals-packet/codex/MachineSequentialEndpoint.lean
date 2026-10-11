import Test.Dogfood.Scenario.Workers.Assertions
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario
example (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision)
    (built : Api.Author.build (Workers.crew total) = .ok b) (held : Workers.Assertions.Holds b cf m)
    (accepted : Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2) :
    Workers.Assertions.ReleaseDebits (Run.stepBy b m x) :=
  Workers.Assertions.releases_step total cf b m x built held accepted
#axiom_audit Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers.Assertions
