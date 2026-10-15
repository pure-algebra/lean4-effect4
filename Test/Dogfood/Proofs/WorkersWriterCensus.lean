import Test.Dogfood.Proofs.WorkersWriters
import Test.Dogfood.Proofs.WorkersSlots
import Effect4.Laws.Program.AnswerSlots.Points
import Effect4.Laws.Program.HeapSites

/-!
Concept: scope-lifetime-finalization R11, each logged identity spends a release start.
Question: the store clause of Workers.Assertions.logs_step.
Consumers: the release writer's native debit and the log-membership history invariant.
Reach: every job count and actual source update, with the initialized bindings retained.
The source census identifies writes; it does not establish the dynamic binding premise.
No execution count, progress, or host agreement follows from the census alone.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.WorkersWriterCensus
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario
open WorkersSlots

/-- Only the two release leaves use the released-reference slot for a list update. -/
def allowedUpdate (site : List Nat × NativeOp × Term × Option Nat) : Bool :=
  match site.2.1 with
  | .refUpdateWith _ => decide
      (site.2.2.1 = .var 0 ∨ site.2.2.1 = .var 2 ∨
        (site.2.2.1 = .var 1 ∧
          (site.1 = Programs.crewAcquire 1 ++ [1] ∨ site.1 = Programs.crewAcquire 2 ++ [1])))
  | _ => true

/-- The actual source update census holds uniformly in the job count. -/
theorem updates (total : Nat) :
    (HeapSites.performSites (Programs.workersProgram total)).all allowedUpdate = true := by
  kernel_rfl

/-- An ordinary source update uses the opened or assigned reference slot. -/
theorem ordinary_update (total : Nat) (point : Point) (term request : Term)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (ordinary : OrdinaryPoint point) : request = .var 0 ∨ request = .var 2 := by
  have member := HeapSites.performSites_complete found
  have checked := List.all_eq_true.mp (updates total) _ member
  change decide (request = .var 0 ∨ request = .var 2 ∨
    (request = .var 1 ∧ (point.path = Programs.crewAcquire 1 ++ [1] ∨
      point.path = Programs.crewAcquire 2 ++ [1]))) = true at checked
  rcases of_decide_eq_true checked with opened | assigned | ⟨_, one | two⟩
  · exact .inl opened
  · exact .inr assigned
  · exact False.elim (ordinary.1 one)
  · exact False.elim (ordinary.2 two)

/-- Reading an initialized leading slot reads its actual stored handle. -/
theorem leading_slot (env : List Val) (leading : env.take 5 = bindings) (index : Nat)
    (inside : index < 5) : evalTerm env (.var index) = bindings[index]? := by
  change env[index]? = bindings[index]?
  exact AnswerSlots.Prefix.read (bindings := bindings) (by exact leading) index (by exact inside)

/-- An ordinary list update cannot target the released reference after initialization. -/
theorem ordinary_update_key (total : Nat) (point : Point) (term request : Term)
    (value : Val) (key : RefKey)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (ordinary : OrdinaryPoint point) (leading : point.env.take 5 = bindings)
    (evaluated : evalTerm point.env request = some value)
    (selected : NativeOp.syncOpOf (.refUpdateWith term) point.env value =
      some (.refUpdate key term point.env)) : key.index ≠ 1 := by
  rcases ordinary_update total point term request found ordinary with opened | assigned
  · rw [opened, leading_slot point.env leading 0 (by decide)] at evaluated
    cases evaluated
    cases selected
    decide
  · rw [assigned, leading_slot point.env leading 2 (by decide)] at evaluated
    cases evaluated
    cases selected
    decide

end Test.Dogfood.Proofs.WorkersWriterCensus
