import Test.Dogfood.Proofs.WorkersFlow
import Effect4.Laws.Program.CrewLogs.Writes
import Test.Dogfood.Scenario.SourceFragment
import Effect4.Laws.Program.ReleaseWriter.Source

/-!
Concept: scope-lifetime-finalization R11.
Question: the actual Workers source supplies the shared direct-release writer contract.
Reach: every job total and both acquired identities.
Consumer: Workers.Assertions.logs_step through the shared writer evaluator.
The source certificate does not establish the captured value or initialized reference binding.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.WorkersWriterSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

/-- The shared append expression reads the captured member and current reference value. -/
def releaseTerm (identity : Nat) : Term :=
  CrewLogs.appendTerm (identity + 6) (identity + 4)

/-- The observed cell and actual source term of each release. -/
def target (identity : Nat) : ReleaseWriter.Target where
  path := Programs.crewAcquire identity
  term := releaseTerm identity
  cell := 1
  value := .nat identity

/-- The source census covers both selected releases uniformly in the job count. -/
theorem bounded_census (total : Nat) :
    [1, 2].all (fun identity => (HeapSites.performSites (Programs.workersProgram total)).all
      (ReleaseWriter.boundedSite (target identity))) = true := by kernel_rfl

/-- The existing source-site certificate identifies each selected acquisition. -/
theorem acquisition (total identity : Nat) (member : identity ∈ [1, 2]) :
    SourceScope.AcquisitionAt (Programs.workersProgram total) (target identity).path := by
  have actual := Programs.workers_acquisition_sites total identity member
  change Programs.acquisitionAt (Programs.workersProgram total) (Programs.crewAcquire identity) = true at actual
  unfold Programs.acquisitionAt at actual
  split at actual
  · next first last found => exact ⟨first, last, found⟩
  · cases actual

/-- Each actual release uses the shared append expression at its own captured slots. -/
theorem release_source (total identity : Nat) (member : identity ∈ [1, 2]) :
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire identity ++ [1]) =
      some (.eff (.perform (.refUpdateWith (releaseTerm identity)) (.var 1))) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  · rw [List.mem_singleton.mp tail]
    kernel_rfl

/-- Both exact release equations instantiate one shared writer source contract. -/
theorem source (total identity : Nat) (member : identity ∈ [1, 2]) :
    ReleaseWriter.Source (target identity) (Programs.workersProgram total) := by
  refine ReleaseWriter.Source.of_census _ _ (SourceFragment.workers_fragment total)
    (acquisition total identity member) ?_
    (List.all_eq_true.mp (bounded_census total) identity member)
  exact ⟨.var 1, release_source total identity member⟩

end Test.Dogfood.Proofs.WorkersWriterSource
