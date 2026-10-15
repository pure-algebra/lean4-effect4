import Test.Dogfood.Proofs.QueueWorkersTakeSites
import Test.Dogfood.Proofs.QueueWorkersNotificationFlow

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through both actual notification prefixes after each take.
The generated source addresses identify two authored postAll regions and their shared option branch.
These certificates grant no request phase or delivery fact.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersTakeTailSites
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The actual take callback enters the two notification binds before its option branch. -/
def tailPath (worker : Nat) : List Nat := (QueueWorkersTakeSites.path worker).dropLast ++ [1]

/-- Each notification body retains its existing source address. -/
def firstPath (worker : Nat) : List Nat := tailPath worker ++ [0]
def secondPath (worker : Nat) : List Nat := tailPath worker ++ [1, 0]
def optionPath (worker : Nat) : List Nat := tailPath worker ++ [1, 1]

/-- A source certificate selects existing program data, with no independent program representation. -/
def body (path : List Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram 0)) path with
  | some (.eff value) => value
  | _ => .succeed (.lit .unit)

/-- Each actual take continuation contains the same two notification binds. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (tailPath worker) =
      some (.eff (.bind (body (firstPath worker))
        (.bind (body (secondPath worker)) (body (optionPath worker))))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The first postAll body belongs to the already certified notification census. -/
theorem first_member (total worker : Nat) (member : worker ∈ [1, 2]) :
    firstPath worker ∈ QueueWorkersCustodyNotificationSource.origins total := by
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  exact (List.not_mem_nil member).elim

/-- The second postAll body belongs to the same existing source census. -/
theorem second_member (total worker : Nat) (member : worker ∈ [1, 2]) :
    secondPath worker ∈ QueueWorkersCustodyNotificationSource.origins total := by
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  exact (List.not_mem_nil member).elim

/-- The first concrete notification body consumes the existing source certificate. -/
def firstSpec (total worker : Nat) (member : worker ∈ [1, 2]) :
    QueueWorkersNotificationFlow.Spec (Programs.queueProgram total) :=
  QueueWorkersNotificationFlow.specification total (firstPath worker) (first_member total worker member)

/-- The second concrete notification body consumes the same existing source certificate. -/
def secondSpec (total worker : Nat) (member : worker ∈ [1, 2]) :
    QueueWorkersNotificationFlow.Spec (Programs.queueProgram total) :=
  QueueWorkersNotificationFlow.specification total (secondPath worker) (second_member total worker member)
end Test.Dogfood.Proofs.QueueWorkersTakeTailSites
