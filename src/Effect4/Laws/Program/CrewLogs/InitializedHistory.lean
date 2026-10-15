import Effect4.Laws.Program.CrewLogs.Initialized
import Effect4.Laws.Program.AnswerSlots.InitializedHistory

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: actual initialized crew histories satisfy their one log observation.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
Reach: every admitted history of a certified sequential, race-free crew source.
The observation gives log membership and release debits, without progress or an outside-host claim.
-/
set_option autoImplicit false
namespace Effect4.Program.CrewLogs
open Effect4 Effect4.Machine Effect4.Program
open AnswerSlots
universe w

/-- The writer reads the same initialized configuration as the actual guarded driver. -/
def InitializedState (spec : Initialized.Spec) (machine : NativeMachine) : Prop :=
  Guard.GuardState machine ∧ ParkedShape.Configuration machine ∧ Initialized.Configuration spec machine

/-- The log reader consumes an initialized driver's actual machine and command assertions. -/
theorem initialized_history_of_lift {W : Type w} (crew : Spec) (spec : Initialized.Spec) (b : Api.Built)
    (root : spec.root = b.program) (table : spec.table = b.table)
    (contract : SyncContract crew spec)
    (sources : ∀ identity ∈ crew.identities, ReleaseWriter.Source (crew.target identity) b.program)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program)
    (order : Effect4.Laws.Effects.WorldOrder W)
    (I : W → NativeMachine → List SourceScope.SourceCommand → Prop)
    (O : W → NativeMachine → List SourceScope.SourceTask → Prop)
    (commands : ∀ world machine queue, I world machine queue → SourceScope.CommandsAt b.program queue)
    (carried : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table)
        (fun _ machine => ((Guard.GuardState machine ∧ SourceScope.ConfigurationAt b.program machine) ∧
          ParkedShape.Configuration machine) ∧ Initialized.Configuration spec machine)
        I O (fun _ _ _ => True)) (world : W) : History crew b := by
  have reordered :
      (fun (_ : W) machine => ((Guard.GuardState machine ∧ SourceScope.ConfigurationAt b.program machine) ∧
          ParkedShape.Configuration machine) ∧ Initialized.Configuration spec machine) =
      (fun _ machine => SourceScope.ConfigurationAt b.program machine ∧ InitializedState spec machine) := by
    funext index machine
    apply propext
    exact ⟨fun held => ⟨held.1.1.2, held.1.1.1, held.1.2, held.2⟩,
      fun held => ⟨⟨⟨held.2.1, held.1⟩, held.2.2.1⟩, held.2.2.2⟩⟩
  rw [reordered] at carried
  refine history crew b sources fragment sequential raceFree (InitializedState spec) ?_ ?_
    order I O (fun _ _ _ => True) commands carried (fun _ _ _ _ _ _ => trivial) ?_
  · intro machine held
    have writes := writes_of_current contract machine (fun id fiber lookup => by
      obtain ⟨input, output, current, stack⟩ := held.2.2.frames fiber (RunMachine.mem_of_fiber? lookup)
      exact ⟨input, current⟩)
    simpa only [root, table] using writes
  · intro machine owner token answer held
    refine ⟨Guard.AnswerDecision.guardState_prepareAsyncAnswer b.program b.table machine owner token answer held.1,
      held.2.1.fields rfl, ?_⟩
    have kept := (Initialized.configuration_edits spec).prepare machine owner token answer held.2.2
    simpa only [root, table] using kept
  · intro fuel
    refine ⟨world, Guard.guardState_load b.program fuel, ?_, ?_⟩
    · intro fiber member
      have same := List.mem_singleton.mp member
      subst fiber
      exact ParkedShape.unparked rfl
    · simpa only [root] using Initialized.initial_configuration spec fuel
/-- One initialized history theorem supplies both crew log obligations. -/
theorem initialized_history (crew : Spec) (spec : Initialized.Spec) (b : Api.Built)
    (root : spec.root = b.program) (table : spec.table = b.table)
    (contract : SyncContract crew spec)
    (sources : ∀ identity ∈ crew.identities, ReleaseWriter.Source (crew.target identity) b.program)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program) : History crew b := by
  have carried := Initialized.decision_lift spec (root.symm ▸ fragment) (root.symm ▸ raceFree)
  let I (_ : (Unit × Unit) × Unit) (machine : NativeMachine) (commands : List SourceScope.SourceCommand) :=
    Initialized.DriverQueue spec ((), ()) machine commands ∧ Initialized.QueueAt spec machine commands
  let O (_ : (Unit × Unit) × Unit) (machine : NativeMachine) (tasks : List SourceScope.SourceTask) :=
    Initialized.DriverTasks spec ((), ()) machine tasks ∧ True
  apply initialized_history_of_lift crew spec b root table contract sources fragment sequential raceFree
    (Lift.pairOrder (Lift.pairOrder Lift.unitOrder Lift.unitOrder) Lift.unitOrder) I O
    (fun _ _ _ held => root ▸ held.1.2) ?_ (((), ()), ())
  have evaluator : evaluatorFor spec.root spec.table = evaluatorFor b.program b.table := by rw [root, table]
  rw [evaluator] at carried
  simpa only [Initialized.DriverState, root, table] using carried

end Effect4.Program.CrewLogs
