import Test.Dogfood.Scenario.QueueWorkers.ReleaseWrites
import Test.Dogfood.Scenario.SourceFragment
import Effect4.Laws.Program.ReleaseWriter.Source

/-!
Concept: scope-lifetime-finalization R11.
Question: the actual QueueWorkers source supplies the shared direct-release writer contract.
Reach: every job total and all three acquired identities.
Consumer: QueueWorkers.Assertions.logs_history through the shared writer evaluator.
The source certificate does not establish the captured value or initialized reference binding.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

/-- The observed cell and actual source term of each release. -/
def target (identity : Nat) : ReleaseWriter.Target where
  path := Programs.queueAcquire identity
  term := QueueWorkers.ReleaseWrites.releaseTerm identity
  cell := 2
  value := .nat identity

/-- The source census covers all three selected releases uniformly in the job count. -/
theorem bounded_census (total : Nat) :
    [1, 2, 3].all (fun identity => (HeapSites.performSites (Programs.queueProgram total)).all
      (ReleaseWriter.boundedSite (target identity))) = true := by kernel_rfl

/-- The existing source-site certificate identifies each selected acquisition. -/
theorem acquisition (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    SourceScope.AcquisitionAt (Programs.queueProgram total) (target identity).path := by
  have actual := Programs.queue_acquisition_sites total identity member
  change Programs.acquisitionAt (Programs.queueProgram total) (Programs.queueAcquire identity) = true at actual
  unfold Programs.acquisitionAt at actual
  split at actual
  · next first last found => exact ⟨first, last, found⟩
  · cases actual

/-- The exact release equations instantiate one shared writer source contract. -/
theorem source (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    ReleaseWriter.Source (target identity) (Programs.queueProgram total) := by
  refine ReleaseWriter.Source.of_census _ _ (SourceFragment.queue_fragment total)
    (acquisition total identity member) ?_
    (List.all_eq_true.mp (bounded_census total) identity member)
  exact ⟨.var 2, QueueWorkers.ReleaseWrites.source total identity member⟩

end Test.Dogfood.Proofs.QueueWorkersWriter
