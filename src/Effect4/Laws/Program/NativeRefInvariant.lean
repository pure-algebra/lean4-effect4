import Effect4.Laws.Program.NativeHeapReplies
import Effect4.Laws.Machine.LiftMachineFact

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the crews' log membership follows the initialized writer at each actual lookup.
Consumers: CrewLogHistory and the two application log goals.
Reach: every native decision under a supplied driver invariant and actual synchronous write contract.
The existing reference-transfer proof owns the command cases. This module adds no source permission or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.RefInvariant
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
universe w

/-- A reference predicate is retained by the current synchronous head, when that head executes. -/
def SyncKeeps (P : RefHeap → Prop) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (code : NCode) : Prop :=
  ∀ thunk next value, code = .sync thunk →
    (interpAt root m.completedExits table).syncState thunk m.state = some (next, value) →
    P m.state.refs → P next.refs

/-- The existing command transfer reads the write contract only at its actual looked-up fiber. -/
theorem command_keeps (P : RefHeap → Prop) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceCommand) (rest : List SourceCommand) (held : P m.state.refs)
    (writes : ∀ id fiber, m.fiber? id = some fiber → SyncKeeps P root table m fiber.frame.current) :
    P (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1.state.refs := by
  apply (StoreExecution.command_refTransfer root table m command rest).preserves P held
  intro id yielding fiber thunk next value found runs current unparked actual
  exact writes id fiber found thunk next value current actual held

/-- A resume command installs code and changes no reference cell. -/
theorem resume_refs (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) (rest : List SourceCommand) :
    (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m (.resume id token code) rest).1.state.refs =
      m.state.refs := by
  have transfer := StoreExecution.command_refTransfer root table m (.resume id token code) rest
  cases transfer with
  | same after refs => exact refs
  | sync owner yielding fiber thunk after value found runs current unparked actual =>
    rcases runs with impossible | impossible <;> cases impossible

/-- Every outside edit retains references; preparation may change only the other stores. -/
theorem edits (P : RefHeap → Prop) (root : NativeEff) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.MachineEdits (interpOf root table) (fun m : NativeMachine => P m.state.refs) := by
  letI := evaluatorFor root table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m owner fiber held found
    exact held
  · intro m owner task held
    exact held
  · intro m id verdict held
    rw [StatePreservation.modify_state]
    exact held
  · intro m who extra target fiber held found
    unfold Lift.interruptEdit
    dsimp only
    split <;> exact held
  · intro m held
    exact held
  · intro m millis held running
    exact held
  · intro m owed held
    rw [drain_refs]
    exact held
  · intro m id token answer held
    rw [prepare_reply_refs]
    exact held

/-- One actual-write contract extends any existing guarded decision invariant with a reference predicate. -/
theorem decision_lift {W : Type w} (P : RefHeap → Prop) (root : NativeEff) (table : RowTable)
    (order : Effect4.Laws.Effects.WorldOrder W)
    (J : W → NativeMachine → Prop)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (base : letI := evaluatorFor root table
      Lift.DecisionLift order (interpOf root table) J I O A)
    (writes : ∀ world m, J world m → ∀ id fiber, m.fiber? id = some fiber →
      SyncKeeps P root table m fiber.frame.current) :
    letI := evaluatorFor root table
    Lift.DecisionLift order (interpOf root table) (fun world m => J world m ∧ P m.state.refs) I O A := by
  letI := evaluatorFor root table
  apply base.withMachineFact (fun m => P m.state.refs) ?_ (edits P root table) ?_
  · intro tasks world m command rest running guarded held
    exact command_keeps P root table m command rest held (writes world m guarded.1)
  · intro world m id token answer invariant held running admitted
    rw [resume_refs, prepare_reply_refs]
    exact held

/-- A reference predicate follows every admitted history through the supplied decision invariant. -/
theorem history {W : Type w} (P : RefHeap → Prop) (b : Api.Built)
    (order : Effect4.Laws.Effects.WorldOrder W)
    (J : W → NativeMachine → Prop)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (base : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table) J I O A)
    (writes : ∀ world m, J world m → ∀ id fiber, m.fiber? id = some fiber →
      SyncKeeps P b.program b.table m fiber.frame.current)
    (admission : ∀ world m d, J world m →
      Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m d → A world m d)
    (compileFuel : Nat) (load : ∃ world, J world (Api.load b.program compileFuel))
    (empty : P []) (m : NativeMachine) (reached : Run.HistoryOf b compileFuel m) : P m.state.refs := by
  obtain ⟨initial, loaded⟩ := load
  have kept := Run.history_keeps b compileFuel (fun m => ∃ world, J world m ∧ P m.state.refs)
    ⟨initial, loaded, empty⟩ (fun before row held accepted => ?_) m reached
  · obtain ⟨_, _, good⟩ := kept
    exact good
  · letI := evaluatorFor b.program b.table
    obtain ⟨world, invariant, good⟩ := held
    obtain ⟨later, _, after⟩ := Lift.stepDecisionState_lift
      (decision_lift P b.program b.table order J I O A base writes)
      row.1 world before row.2 ⟨invariant, good⟩ (admission world before row.2 invariant accepted)
    exact ⟨later, after⟩
end Effect4.Program.RefInvariant
