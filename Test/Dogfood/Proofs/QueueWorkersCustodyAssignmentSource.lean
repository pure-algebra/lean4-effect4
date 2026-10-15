import Test.Dogfood.Proofs.QueueWorkersCustodyAssignment
import Test.Dogfood.Scenario.Programs

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.Assertions.jobs_step, through assignment_commit.
The existing generated address fold checks the two actual assignment terms and lexical levels.
The custody callback producer still supplies the actual protected job slot.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersCustodyAssignmentSource
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustody

/-- Only the two literal worker writers update the actual assignment reference. -/
def head (root : NativeEff) (path : List Nat) : Node NativeOp → Bool
  | .eff (.perform (.refUpdateWith term) (.var 3)) =>
      decide (term = assignmentTerm 9 8 1 ∧ SourceScope.levelAt (.eff root) 0 path = some 9) ||
      decide (term = assignmentTerm 10 9 2 ∧ SourceScope.levelAt (.eff root) 0 path = some 10)
  | _ => true

/-- The actual crew has exactly the declared assignment expressions, for every job total. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (head (Programs.queueProgram total) path)) = true := by
  kernel_rfl

/-- Actual source ownership fixes both the assignment's worker and the slot of its captured job. -/
theorem assignment_at (total : Nat) (point : Point) (term : Term)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) (.var 3)))) :
    ∃ worker ∈ [1, 2], term = assignmentTerm point.env.length (worker + 7) worker ∧
      point.env.length = worker + 8 := by
  have member : point.path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) point.path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) point.path member
  rw [found] at checked
  change (decide (term = assignmentTerm 9 8 1 ∧
      SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some 9) ||
    decide (term = assignmentTerm 10 9 2 ∧
      SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some 10)) = true at checked
  rcases Bool.or_eq_true_iff.mp checked with first | second
  · obtain ⟨shape, level⟩ := of_decide_eq_true first
    have length : point.env.length = 9 := Option.some.inj (source.symm.trans level)
    exact ⟨1, by decide, by rw [length]; exact shape, length⟩
  · obtain ⟨shape, level⟩ := of_decide_eq_true second
    have length : point.env.length = 10 := Option.some.inj (source.symm.trans level)
    exact ⟨2, by decide, by rw [length]; exact shape, length⟩

/-- The selected actual source writer spends exactly the job retained by its worker continuation. -/
theorem assignment_native (total : Nat) (point : Point) (term : Term)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) (.var 3))))
    (world : QueueWorkersCustody.World) (token job : Nat)
    (phase : world.requests token = .holding job) (holding : job ∈ world.ledger.custody)
    (conserved : world.ledger.Conserved)
    (capture : ∀ worker ∈ [1, 2], point.env.length = worker + 8 →
      point.env[worker + 7]? = some (.nat job)) (stores : Stores)
    (read : refPeek stores.refs ⟨3⟩ = some (.list (world.ledger.assigned.map (fun p => gave p.1 p.2)))) :
    ∃ worker ∈ [1, 2],
      syncOpStep (.refUpdate ⟨3⟩ term point.env) stores =
        some ({stores with refs := (refPoke stores.refs ⟨3⟩
          (.list ((assignWorld world token job worker).ledger.assigned.map (fun p => gave p.1 p.2))))}, .unit) ∧
      Future world (assignWorld world token job worker) ∧
      (assignWorld world token job worker).ledger.Conserved ∧
      ValueAt (assignWorld world token job worker) (.spent token) .unit := by
  obtain ⟨worker, member, shape, length⟩ := assignment_at total point term source found
  subst term
  exact ⟨worker, member, assignment_commit world token job worker phase holding conserved
    point.env (worker + 7) (capture worker member length) stores read⟩

end Test.Dogfood.Proofs.QueueWorkersCustodyAssignmentSource
