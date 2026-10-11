import Effect4.Laws
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Proofs.HostTimeoutSettle
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing
example (q : List Nat) (built : Api.Built) (m : NativeMachine) (fiber : Control.Fiber) (yielding : Bool)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment built.program) (owned : SourceScope.FrameAt built.program fiber.frame)
    (sequential : SourceScope.SequentialSource built.program)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (races : m.races = []) :
    IterDebit q m fiber (evaluateNative built.program m fiber yielding built.table) :=
  NativeScopeDebit.native q built.program built.table m fiber yielding held fragment owned sequential fibers scopes fresh races
#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeScopeDebit Effect4.Laws.Program.ReleaseCustody.NativeParkDebit Effect4.Laws.Program.ReleaseCustody.NativePrimitiveDebit Effect4.Laws.Program.SourceOpportunityNative Test.Dogfood.Proofs.HostTimeoutLocalSteps Test.Dogfood.Proofs.HostTimeoutIteration Test.Dogfood.Proofs.HostTimeoutSettle
#plan_status Effect4.Program.ReleaseCustody.Execution.history
