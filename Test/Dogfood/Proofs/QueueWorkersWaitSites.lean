import Test.Dogfood.Proofs.QueueWorkersTakeTailSites
import Test.Dogfood.Proofs.QueueWorkersWithdrawalSites

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual waiting option branch.
The certificates expose the authored await, protected cleanup and captured withdrawal key.
They establish no interruption-only failure claim or completed-history invariant.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersWaitSites
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario
open QueueWorkersTakeTailSites

/-- The empty option enters the authored wait before returning an empty retry cursor. -/
def path (worker : Nat) := optionPath worker ++ [0]

/-- The protected wait records its actual cleanup branch under its body exit. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.bind (.onExit (.restore (.var (worker + 7)) (.perform .deferredAwait (.var (worker + 10))))
        (body (path worker ++ [0, 1]))) (.succeed (.app "none" .nil)))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The wait's actual protected finalizer captures the body exit at its authored point. -/
theorem protected_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [0]) = some (.eff
      (.onExit (.restore (.var (worker + 7)) (.perform .deferredAwait (.var (worker + 10))))
        (body (path worker ++ [0, 1])))) :=
  by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The protected wait captures the original request key before its body exit is appended. -/
theorem protected_level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker ++ [0]) = some (worker + 14) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The protected cleanup selects its withdrawal from the actual captured body exit. -/
theorem cleanup (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [0, 1]) = some (.eff
      (.select (.app "causeIsInterrupt" (.cons (.var (worker + 14)) .nil)) .bool
        (body (path worker ++ [0, 1, 0])) (.succeed (.lit .unit)))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim
/-- The interrupted branch binds the actual withdrawal result before its existing notification region. -/
theorem withdraw_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [0, 1, 0]) = some (.eff
      (.bind (.perform (.refModifyWith (QueueWorkersWithdrawalSites.term worker)) (.var 0))
        (body (path worker ++ [0, 1, 0, 1])))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The withdrawal operation is the first child of this actual cleanup bind. -/
theorem withdraw_path (worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [0, 1, 0, 0] = QueueWorkersWithdrawalSites.path worker := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The cleanup's actual postAll tail uses the existing checked notification census. -/
theorem notification_member (total worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [0, 1, 0, 1] ∈ QueueWorkersCustodyNotificationSource.origins total := by
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  rcases List.mem_cons.mp member with rfl | member
  · exact of_decide_eq_true (by kernel_rfl)
  exact (List.not_mem_nil member).elim

end Test.Dogfood.Proofs.QueueWorkersWaitSites
