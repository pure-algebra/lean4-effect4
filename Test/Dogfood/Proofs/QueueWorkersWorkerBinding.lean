import Test.Dogfood.Proofs.QueueWorkersTakeWrapper
import Test.Dogfood.Proofs.QueueWorkersReadonlySource

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through both actual worker job bindings.
The assignment captures the exact classified take answer before entering the existing readonly tail.
The shared native and history producers remain separate consumers.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersWorkerBinding
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

def path (worker : Nat) := (QueueWorkersTakeWrapper.path worker).dropLast

def afterTake (total worker : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [1]) with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

/-- Both workers bind their actual Queue.take expression immediately before assignment. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.bind
        (.bind (.withFiber .getInterruptible) (.uninterruptible (QueueWorkersTakeWrapper.allocation worker)))
        (afterTake total worker))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The real first child is the take wrapper already connected to its request producer. -/
theorem take_path (worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [0] = QueueWorkersTakeWrapper.path worker := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The immediate result continuation has the actual assignment head, for every job total. -/
theorem assignment_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    ∃ term rest, Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [1]) =
      some (.eff (.bind (.perform (.refUpdateWith term) (.var 3)) rest)) := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, _, rfl⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, _, rfl⟩
  exact (List.not_mem_nil member).elim

/-- Both source continuations begin with the same actual assignment form. -/
theorem after_take_shape (total worker : Nat) (member : worker ∈ [1, 2]) :
    ∃ term rest, afterTake total worker = .bind (.perform (.refUpdateWith term) (.var 3)) rest := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, _, rfl⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, _, rfl⟩
  exact (List.not_mem_nil member).elim

/-- An actual-body compiler override reuses the checked take and assignment chains.
Its unchecked child induction cannot supply the worker's job permission. -/
theorem constructor (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point) (firstCode : NCode)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (actual : firstCode = compileEff
      (.bind (.withFiber .getInterruptible) (.uninterruptible (QueueWorkersTakeWrapper.allocation worker)))
      (point.child 0)) :
    QueueWorkersJobGraph.CodeAt total table owner world .ordinary (.onSuccess firstCode (.cont point)) := by
  have found := source total worker member
  rw [← atPath] at found
  apply QueueWorkersJobGraph.CodeAt.bound (input := .job owner) rfl
  · rw [actual, ← Agreement.resolve_of_at (Agreement.at_child (p := point) found 0)]
    apply QueueWorkersTakeWrapper.body total worker member table world owner (point.child 0)
    · exact SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found owned rfl)
    · change point.path ++ [0] = QueueWorkersTakeWrapper.path worker
      rw [atPath, take_path worker member]
    · exact leading
  · intro nextWorld future view answer good
    cases answer
    case nat job =>
      obtain ⟨term, rest, shape⟩ := after_take_shape total worker member
      rw [shape] at found
      exact QueueWorkersJobGraph.worker_callback total table nextWorld owner point _ rest term job view
        owned found leading good
    all_goals exact good.elim

/-- The actual worker binder accepts only the job classified by its own take continuation. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    QueueWorkersJobGraph.CodeAt total table owner world .ordinary
      (resolve (Programs.queueProgram total) point) := by
  have found := source total worker member
  rw [← atPath] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    exact constructor total worker member table world owner point _ owned atPath leading rfl
end Test.Dogfood.Proofs.QueueWorkersWorkerBinding
