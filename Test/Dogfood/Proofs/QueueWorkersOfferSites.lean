import Test.Dogfood.Proofs.QueueWorkersCustodySource

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual feeder offer commit.
The source certificates retain the already observed job and its real request and hint slots.
They establish no independent job membership or history assumption.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersOfferSites
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodySource

def path : List Nat := offerEntryPath ++ [1, 0, 1, 1, 0]

def term : Term :=
  match Node.at_ (.eff (Programs.queueProgram 0)) path with
  | some (.eff (.perform (.refModifyWith term) _)) => term
  | _ => .lit .unit

def environment : Env := { names := List.replicate 14 "" }

/-- The feeder's actual commit uses the queue reference at its fixed leading slot. -/
theorem source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) path =
      some (.eff (.perform (.refModifyWith term) (.var 0))) := by
  kernel_rfl

/-- The real offer captures its job, entry flag, request and hint before the commit. -/
theorem level (total : Nat) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 path = some 14 := by
  kernel_rfl

/-- The literal offer expression reads only its actual captured request, hint and job slots. -/
theorem tree :
    Queue.offerStep .nat (input 12) (input 13) (input 10)
      (minted (environment.mint "current")) (environment.push [environment.mint "current"]) path = .ok term := by
  kernel_rfl
end Test.Dogfood.Proofs.QueueWorkersOfferSites
