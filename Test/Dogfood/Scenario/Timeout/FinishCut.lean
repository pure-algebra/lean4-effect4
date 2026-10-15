import Test.Dogfood.Scenario.Timeout.CommandCut
import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: a queued finish requires the actual drained saved stack.
Consumer: the numeric writer queue assertion of both Timeout goals.
Evidence: kernel evaluation at the retained actual pre-count command cut.
Limit: this internal cut refutes neither original fixed-budget endpoint.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Timeout.FinishCut
open Effect4 Effect4.Machine Effect4.Program

/-- The actual pre-count cut retains its launched attempt. -/
def pending : SourceScope.SourceFiber :=
  (CommandCut.cut.1.fiber? ⟨1⟩).get (by decide)

/-- The control reads the actual existing attempt, without a fallback record. -/
theorem actual : CommandCut.cut.1.fiber? ⟨1⟩ = some pending := by kernel_rfl

/-- The actual count prefix still retains its installed source finalizer. -/
theorem saved : pending.frame.stack ≠ [] := by decide

/-- The numeric finish permission rejects that actual unfinished prefix. -/
theorem rejected : ¬ Test.Dogfood.Proofs.HostTimeoutNumberConfiguration.TerminalStack CommandCut.cut.1 ⟨1⟩ := by
  intro terminal
  exact saved (terminal pending actual)

end Test.Dogfood.Scenario.Timeout.FinishCut
