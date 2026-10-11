import Test.Dogfood.Scenario.Workers.Program
import Test.Dogfood.Scenario.QueueWorkers.Program
import Effect4.Laws.Api.AuthorBuild
import Effect4.Laws.Program.Placement
import Effect4.Laws.Auto.KernelRfl

/-!
# Universal crew program equations and static acquisition paths

Placement: translation-simulation, R10, and scope-lifetime-finalization, R11.
These helpers serve `Workers.releases_once` and `QueueWorkers.releases_once`.
The job count ranges over every natural number.
The built-program readings assume successful `Author.build` admission.
The equations identify syntax. The predicates classify paths without proving execution counts.
They establish no progress, finalization, store invariant or host observation.
Decisions rows 254 and 275 bound the two scenario fragments.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.Programs

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Laws.Auto

/-- The crews declare the same two host rows, independently of the job count. -/
def crewScope : Env := { rows := RowDef.names [P3WorkerQueue.take, P3WorkerQueue.runJob] }

/-- The first crew's main elaborates at the closed declaration scope. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem workers_main_some (total : Nat) :
    ((Workers.crew total).main crewScope []).toOption.isSome = true := by
  kernel_rfl

/-- The queue crew's main elaborates at the closed declaration scope. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queue_main_some (total : Nat) :
    ((QueueWorkers.crew total).main crewScope []).toOption.isSome = true := by
  kernel_rfl

/-- The first crew's elaborated tree. The fallback is excluded by `workers_main_some`. -/
def workersProgram (total : Nat) : NativeEff :=
  ((Workers.crew total).main crewScope []).toOption.getD (.succeed (.lit .unit))

/-- The queue crew's elaborated tree. The fallback is excluded by `queue_main_some`. -/
def queueProgram (total : Nat) : NativeEff :=
  ((QueueWorkers.crew total).main crewScope []).toOption.getD (.succeed (.lit .unit))

/-- The first crew's main equation. Consumer: `workers_elaborates`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem workers_main_eq (total : Nat) :
    (Workers.crew total).main crewScope [] = .ok (workersProgram total) :=
  Api.Author.elaboration_eq_getD _ _ (workers_main_some total)

/-- The queue crew's main equation. Consumer: `queue_elaborates`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queue_main_eq (total : Nat) :
    (QueueWorkers.crew total).main crewScope [] = .ok (queueProgram total) :=
  Api.Author.elaboration_eq_getD _ _ (queue_main_some total)

/-- The first crew contains no layer reference. Consumer: `workers_elaborates`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem workers_refs_nil (total : Nat) : (workersProgram total).refSites [] = [] := by
  kernel_rfl

/-- The queue crew contains no layer reference. Consumer: `queue_elaborates`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queue_refs_nil (total : Nat) : (queueProgram total).refSites [] = [] := by
  kernel_rfl

/-- The first crew's module equation. Consumer: `workers_built_program`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem workers_elaborates (total : Nat) :
    elaborateModule (Workers.crew total) = .ok (workersProgram total) := by
  change elaborateModule { rows := [P3WorkerQueue.take, P3WorkerQueue.runJob], main := (Workers.crew total).main } = .ok (workersProgram total)
  exact Api.Author.elaborateModule_no_declarations _ _ crewScope.rows _
    (by rfl) (workers_main_eq total) (workers_refs_nil total)

/-- The queue crew's module equation. Consumer: `queue_built_program`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queue_elaborates (total : Nat) :
    elaborateModule (QueueWorkers.crew total) = .ok (queueProgram total) := by
  change elaborateModule { rows := [P3WorkerQueue.take, P3WorkerQueue.runJob], main := (QueueWorkers.crew total).main } = .ok (queueProgram total)
  exact Api.Author.elaborateModule_no_declarations _ _ crewScope.rows _
    (by rfl) (queue_main_eq total) (queue_refs_nil total)

/-- A successful first-crew build stores its elaborated tree. Consumer: its acquisition fact. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem workers_built_program (total : Nat) (b : Api.Built)
    (h : Api.Author.build (Workers.crew total) = .ok b) :
    b.program = workersProgram total :=
  Except.ok.inj ((Api.Author.build_retains h).1.symm.trans (workers_elaborates total))

/-- A successful queue-crew build stores its elaborated tree. Consumer: its acquisition fact. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queue_built_program (total : Nat) (b : Api.Built)
    (h : Api.Author.build (QueueWorkers.crew total) = .ok b) :
    b.program = queueProgram total :=
  Except.ok.inj ((Api.Author.build_retains h).1.symm.trans (queue_elaborates total))

/-- The first crew's acquisition paths, by worker identity. -/
def crewAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

/-- The queue crew's acquisition paths, by member identity. -/
def queueAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

/-- Read the node kind through the existing program path traversal. -/
def acquisitionAt (tree : NativeEff) (path : List Nat) : Bool :=
  match (Node.eff tree).at_ path with
  | some (.eff (.acquireRelease _ _)) => true
  | _ => false

/-- The first crew's paths address acquisition nodes.
Step of its release bridge. Consumer: `crew_released_by_releases`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem workers_acquisition_sites (total : Nat) :
    ∀ i ∈ [1, 2], acquisitionAt (workersProgram total) (crewAcquire i) = true := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · kernel_rfl
  · have h := List.mem_singleton.mp hi
    subst i
    kernel_rfl

/-- The queue crew's paths address acquisition nodes.
Step of its release bridge. Consumer: `queueCrew_released_by_releases`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem queue_acquisition_sites (total : Nat) :
    ∀ i ∈ [1, 2, 3], acquisitionAt (queueProgram total) (queueAcquire i) = true := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · kernel_rfl
  · rcases List.mem_cons.mp hi with rfl | hi
    · kernel_rfl
    · have h := List.mem_singleton.mp hi
      subst i
      kernel_rfl

/-- Both first-crew acquisition paths satisfy the static placement predicate.
Step of `Workers.releases_once`. Consumer: `crew_acquire_once_placed`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem workers_placement (total : Nat) :
    ∀ i ∈ [1, 2], OncePlaced (Node.eff (workersProgram total)) (crewAcquire i) = true := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · kernel_rfl
  · have h := List.mem_singleton.mp hi
    subst i
    kernel_rfl

/-- All three queue-crew acquisition paths satisfy the static placement predicate.
Step of `QueueWorkers.releases_once`. Consumer: `queueCrew_acquire_once_placed`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem queue_placement (total : Nat) :
    ∀ i ∈ [1, 2, 3], OncePlaced (Node.eff (queueProgram total)) (queueAcquire i) = true := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · kernel_rfl
  · rcases List.mem_cons.mp hi with rfl | hi
    · kernel_rfl
    · have h := List.mem_singleton.mp hi
      subst i
      kernel_rfl

/-- The first crew's static acquisition fact at every job count and successful build.
Step of `Workers.releases_once`. Consumer: its control-linearity assembly. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem crew_acquire_once_placed (total : Nat) (b : Api.Built)
    (h : Api.Author.build (Workers.crew total) = .ok b) :
    ∀ i ∈ [1, 2], OncePlaced (Node.eff b.program) (crewAcquire i) = true := by
  rw [workers_built_program total b h]
  exact workers_placement total

/-- The queue crew's static acquisition fact at every job count and successful build.
Step of `QueueWorkers.releases_once`. Consumer: its control-linearity assembly. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem queueCrew_acquire_once_placed (total : Nat) (b : Api.Built)
    (h : Api.Author.build (QueueWorkers.crew total) = .ok b) :
    ∀ i ∈ [1, 2, 3], OncePlaced (Node.eff b.program) (queueAcquire i) = true := by
  rw [queue_built_program total b h]
  exact queue_placement total

end Test.Dogfood.Scenario.Programs
