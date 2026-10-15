import Test.Dogfood.Scenario.QueueWorkers.WriterSource
import Effect4.Laws.Program.AnswerSlots.TypedAcquisition

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the concrete queue crew instantiates the protected acquired-answer graph.
Reach: every job total and the three actual acquisition paths.
Limit: the command history producer remains a separate obligation.
Consumer: QueueWorkers Assertions.logs_history and its native evaluator.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- Read the authored entry note at the selected acquisition body. -/
def note (total identity : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (Programs.queueAcquire identity ++ [0]) with
  | some (.eff (.bind first _)) => first
  | _ => .succeed (.lit .unit)

/-- Each actual acquisition body logs its entry and returns its own literal identity. -/
theorem acquisition_body (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    ∃ note, Node.at_ (.eff (Programs.queueProgram total)) (Programs.queueAcquire identity ++ [0]) =
      some (.eff (.bind note (.succeed (.lit (.nat identity))))) := by
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨note total 1, by kernel_rfl⟩
  rcases List.mem_cons.mp tail with rfl | tail
  · exact ⟨note total 2, by kernel_rfl⟩
  have selected := List.mem_singleton.mp tail
  subst identity
  exact ⟨note total 3, by kernel_rfl⟩

/-- The concrete queue source supplies the complete protected acquisition specification. -/
def spec (total : Nat) (rows : RowTable) : AnswerSlots.Typed.Spec where
  root := Programs.queueProgram total
  table := rows
  bindings := InitialSlots.bindings
  identities := [1, 2, 3]
  acquirePath := Programs.queueAcquire
  acquiredIndex := fun identity => identity + 5
  sites := by
    intro identity member
    apply WriterSource.acquisition_sites total
    change Programs.queueAcquire identity ∈
      [Programs.queueAcquire 1, Programs.queueAcquire 2, Programs.queueAcquire 3]
    rcases List.mem_cons.mp member with rfl | tail
    · exact List.mem_cons_self
    rcases List.mem_cons.mp tail with rfl | tail
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    have selected := List.mem_singleton.mp tail
    subst identity
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  complete := by
    rintro path ⟨acquire, release, found⟩
    rcases Connections.acquisition_cases total path acquire release found with first | second | third
    · exact ⟨1, by decide, first⟩
    · exact ⟨2, by decide, second⟩
    · exact ⟨3, by decide, third⟩
  acquisitionLevel := Connections.acquisition_level total
  acquisitionBody := acquisition_body total
end Test.Dogfood.Proofs.QueueWorkersFlow
