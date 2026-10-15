import Test.Dogfood.Proofs.WorkersLogContract
import Test.Dogfood.Proofs.QueueWorkersLogContract
import Test.Dogfood.Proofs.QueueWorkersWriter
import Test.Dogfood.Scenario.QueueWorkers.CleanupSource
import Effect4.Laws.Program.CrewLogs.InitializedHistory
import Effect4.Laws.Program.CrewLogs.Observation

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: the two actual crews instantiate one initialized log history theorem.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
Reach: every total, compile budget and session-admitted history of the original sources.
The result gives actual log identities and release debits, without progress or release order.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Test.Dogfood.Proofs.CrewLogHistory
open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario

/-- Every actual Workers history has the shared initialized log observation. -/
theorem workers (total : Nat) (b : Api.Built)
    (built : Api.Author.build (Workers.crew total) = .ok b) : CrewLogs.History WorkersLogContract.crew b := by
  apply CrewLogs.initialized_history WorkersLogContract.crew (WorkersFlow.initializedSpec total b.table) b
    (Programs.workers_built_program total b built).symm rfl (WorkersLogContract.contract total b.table)
  · intro identity member
    rw [Programs.workers_built_program total b built]
    exact WorkersWriterSource.source total identity member
  · exact SourceFragment.workers_built_fragment total b built
  · exact SourceFragment.workers_built_sequential total b built
  · exact SourceFragment.workers_built_race_free total b built

/-- Every actual QueueWorkers history has the same observation at its three source identities. -/
theorem queue (total : Nat) (b : Api.Built)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b) : CrewLogs.History QueueWorkersLogContract.crew b := by
  apply CrewLogs.initialized_history QueueWorkersLogContract.crew (QueueWorkersFlow.initializedSpec total b.table) b
    (Programs.queue_built_program total b built).symm rfl (QueueWorkersLogContract.contract total b.table)
  · intro identity member
    rw [Programs.queue_built_program total b built]
    exact QueueWorkersWriter.source total identity member
  · exact SourceFragment.queue_built_fragment total b built
  · rw [Programs.queue_built_program total b built]
    exact (QueueWorkers.CleanupSource.control total).1
  · rw [Programs.queue_built_program total b built]
    exact (QueueWorkers.CleanupSource.control total).2

end Test.Dogfood.Proofs.CrewLogHistory
