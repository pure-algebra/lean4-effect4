import Test.Dogfood.Proofs.QueueWorkersTakeTailSites
import Test.Dogfood.Proofs.QueueWorkersCustodyRetry

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the classified actual retry hook.
These certificates identify the existing loop and its hint-allocation binder.
They establish no active request or history invariant.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersRetrySites
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The retry loop contains the actual hint binder and take attempt. -/
def path (worker : Nat) := ((QueueWorkersTakeSites.path worker).dropLast).dropLast.dropLast

/-- Both authored request loops test and return their exact option cursor. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.iterate (some (.option .nat)) (.app "none" .nil)
        (QueueWorkersCustody.retryTest (worker + 9)) (.var (worker + 10)) (.var (worker + 9))
        (QueueWorkersTakeTailSites.body (path worker ++ [0])))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The retry loop retains the request key immediately before its cursor slot. -/
theorem level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker) = some (worker + 9) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Every retry round allocates its actual unit hint before the concrete take attempt. -/
theorem body_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker ++ [0]) = some (.eff
      (.bind (.perform (.deferredMakeOf .unit .never) (.lit .unit))
        (QueueWorkersTakeTailSites.body (path worker ++ [0, 1])))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The hint binder includes the loop cursor after the captured request key. -/
theorem body_level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker ++ [0]) = some (worker + 10) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The actual attempt after hint allocation has the original generated take position. -/
theorem attempt_path (worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [0, 1] = (QueueWorkersTakeSites.path worker).dropLast := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim
end Test.Dogfood.Proofs.QueueWorkersRetrySites
