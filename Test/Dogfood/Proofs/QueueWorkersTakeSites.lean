import Test.Dogfood.Proofs.QueueWorkersCustodySource

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at both actual worker take heads.
These source certificates select the library take expression and its captured request and hint slots.
They establish no active request or command-history invariant.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersTakeSites
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodySource

/-- The two actual worker take positions use the existing generated source addresses. -/
def path (worker : Nat) : List Nat :=
  if worker = 1 then Source.takePath else
    [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

/-- The actual term at the selected worker; the source certificate excludes its fallback. -/
def term (worker : Nat) : Term :=
  match Node.at_ (.eff (Programs.queueProgram 0)) (path worker) with
  | some (.eff (.perform (.refModifyWith term) _)) => term
  | _ => .lit .unit

/-- Each source member retains its own lexical request and hint positions. -/
def environment (worker : Nat) : Env := {names := List.replicate (worker + 11) ""}

/-- Both actual workers execute the declared library take term. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) =
      some (.eff (.perform (.refModifyWith (term worker)) (.var 0))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The generated lexical levels determine the actual captured environment length. -/
theorem level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker) = some (worker + 11) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Both concrete writers are the library take expression at their actual captured slots. -/
theorem tree (worker : Nat) (member : worker ∈ [1, 2]) :
    Queue.takeStep .nat (input (worker + 8)) (input (worker + 10))
      (minted ((environment worker).mint "current"))
      ((environment worker).push [(environment worker).mint "current"]) (path worker) = .ok (term worker) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim
end Test.Dogfood.Proofs.QueueWorkersTakeSites
