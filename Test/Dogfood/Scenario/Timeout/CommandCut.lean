import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concept: scope-lifetime-finalization R11, with reactive-scheduling R9.
Question: the numeric command assertion must reject a resumed pre-count queue after an outside interruption.
Consumer: the coupled numeric producer of Timeout.cleanup_keeps and Timeout.retries_declared.
Reach: one internal command cut, followed by an interruption and either public evaluation or queue reuse.
Evidence: finite kernel checks of the actual source, interpreter, and command driver.
Limit: queue reuse is not a scenario move and refutes neither fixed-budget goal.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Timeout.CommandCut
open Effect4 Effect4.Machine Effect4.Program

/-- The cut lies after the fresh attempt installs its finalizer and before it writes its count. -/
def cut :=
  letI := evaluatorFor Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table
  driveState (interpOf Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table) 27
    (Api.load Test.Dogfood.Proofs.HostTimeoutSource.program budget.compileFuel) [.evaluate ⟨0⟩, .drainDue]

/-- The outside interruption records the deferred cause in that running attempt. -/
def interrupted : Effect4.Program.NativeMachine :=
  letI := evaluatorFor Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table
  (stepDecisionState (interpOf Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table) 2000 cut.1
    (.interruptFrom none .empty ⟨1⟩)).1

/-- Reusing the old internal queue is a separate command execution, absent from the scenario alphabet. -/
def reusedQueue : Effect4.Program.NativeMachine :=
  letI := evaluatorFor Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table
  (driveState (interpOf Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table) 2000 interrupted cut.2).1

/-- Public evaluation refuses to re-enter the running attempt after the cut queue has been dropped. -/
def publicEvaluation : Effect4.Program.NativeMachine :=
  letI := evaluatorFor Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table
  (stepDecisionState (interpOf Test.Dogfood.Proofs.HostTimeoutSource.program fetch.table) 2000 interrupted
    (.evaluate ⟨1⟩)).1

#guard cut.1.state.refs == [.nat 0, .list [], .list []]
#guard reusedQueue.state.refs[0]? == some (.nat 0)
#guard reusedQueue.state.refs[1]? == some (.list [.list [.nat 0, .bool true]])
#guard publicEvaluation.state.refs == [.nat 0, .list [], .list []]

end Test.Dogfood.Scenario.Timeout.CommandCut
