import Test.Dogfood.Proofs.QueueWorkersRetryFlow

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the worker's actual job binder.
The retry result selection returns its own held payload at the worker input class.
It creates no permission for an unrelated Nat answer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersRetryReturn
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- The source result selection follows the actual request loop. -/
def path (worker : Nat) := (QueueWorkersRetrySites.path worker).dropLast ++ [1]

/-- Both worker results unwrap only the option returned by their own request loop. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.select (.var (worker + 9)) .option
        (.failCause (.die (.lit (.str "queue: the loop ended without a message"))))
        (.succeed (.var (worker + 10))))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The option result occupies the last existing slot before its payload is appended. -/
theorem level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker) = some (worker + 10) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The actual successful result returns the same occurrence held by its selected request. -/
theorem some_body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token job : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path worker)
    (captured : point.env[worker + 9]? = some (.some (.nat job)))
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job) :
    QueueWorkersJobGraph.CodeAt total table owner world (.job owner)
      (resolve (Programs.queueProgram total) point) := by
  have found := source total worker member
  rw [← atPath] at found
  have depth : point.env.length = worker + 10 := by
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at owned
    rw [atPath, level total worker member] at owned
    exact (Option.some.inj owned).symm
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_select _ _ _ _ fuel]
    apply QueueWorkersTakeSelection.return_body total table world owner (.job owner) job point
      (.var (worker + 9)) (.var (worker + 10)) _ (.nat job) found captured
    · rw [← depth]
      exact List.getElem?_concat_length
    · exact ⟨token, selected, holding⟩
end Test.Dogfood.Proofs.QueueWorkersRetryReturn
