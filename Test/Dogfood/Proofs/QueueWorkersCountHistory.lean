import Test.Dogfood.Proofs.QueueWorkersCountCurrent
import Test.Dogfood.Scenario.QueueWorkers.CleanupSource
import Effect4.Laws.Program.AnswerSlots.InitializedHistory

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, when an admitted delayed reply reads the counter.
The existing initialized driver and reference-transfer history theorem carry the counter invariant.
The proof assumes neither Jobs nor Rest and adds no scheduler or command traversal.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Test.Dogfood.Proofs.QueueWorkersCountCell
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open AnswerSlots

/-- Every admitted history keeps the counter absent or Nat-valued, independently of job conservation. -/
theorem history (total : Nat) (b : Api.Built) (built : Api.Author.build (crew total) = .ok b)
    (compileFuel : Nat) (machine : NativeMachine) (reached : Run.HistoryOf b compileFuel machine) :
    Holds machine.state.refs := by
  let spec := QueueWorkersFlow.initializedSpec total b.table
  have root : spec.root = b.program := (Programs.queue_built_program total b built).symm
  have table : spec.table = b.table := rfl
  let order := Lift.pairOrder (Lift.pairOrder Lift.unitOrder Lift.unitOrder) Lift.unitOrder
  let J (_ : (Unit × Unit) × Unit) (m : NativeMachine) :=
    Initialized.DriverState spec ((), ()) m ∧ Initialized.Configuration spec m
  let I (_ : (Unit × Unit) × Unit) (m : NativeMachine) (commands : List SourceScope.SourceCommand) :=
    Initialized.DriverQueue spec ((), ()) m commands ∧ Initialized.QueueAt spec m commands
  let O (_ : (Unit × Unit) × Unit) (m : NativeMachine) (tasks : List SourceScope.SourceTask) :=
    Initialized.DriverTasks spec ((), ()) m tasks ∧ True
  have carried := Initialized.decision_lift spec (SourceFragment.queue_fragment total) (CleanupSource.control total).2
  have evaluator : evaluatorFor spec.root spec.table = evaluatorFor b.program b.table := by rw [root, table]
  rw [evaluator] at carried
  have lifted : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table) J I O (fun _ _ _ => True) := by
    simpa only [J, I, O, order, root, table] using carried
  apply RefInvariant.history Holds b order J I O (fun _ _ _ => True) lifted ?_
    (fun _ _ _ _ _ => trivial) compileFuel ?_ ?_ machine reached
  · intro world before invariant id fiber found thunk after answer current actual held
    obtain ⟨input, output, owned, stack⟩ := invariant.2.frames fiber (RunMachine.mem_of_fiber? found)
    rw [current] at owned
    have executed : (interpAt spec.root before.completedExits spec.table).syncState thunk before.state =
        some (after, answer) := by simpa only [root, table] using actual
    exact current_keeps total b.table before.completedExits ⟨fiber.id, before.state⟩ input thunk after answer
      owned executed held
  · refine ⟨(((), ()), ()), ?_, ?_⟩
    · change ((Guard.GuardState _ ∧ SourceScope.ConfigurationAt spec.root _) ∧ ParkedShape.Configuration _)
      refine ⟨⟨Guard.guardState_load b.program compileFuel, ?_⟩, ?_⟩
      · simpa only [root] using SourceScope.load_at b.program
          (SourceFragment.queue_built_fragment total b built) compileFuel
      · intro fiber member
        have same := List.mem_singleton.mp member
        subst fiber
        exact ParkedShape.unparked rfl
    · simpa only [root] using Initialized.initial_configuration spec compileFuel
  · intro value impossible
    cases impossible
end Test.Dogfood.Proofs.QueueWorkersCountCell
