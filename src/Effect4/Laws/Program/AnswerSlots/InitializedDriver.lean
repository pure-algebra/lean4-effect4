import Effect4.Laws.Program.AnswerSlots.InitializedChildren
import Effect4.Laws.Program.Guard.SourceLift

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the two crew histories retain initialized frames, captures and child readiness together.
Reach: the actual guarded source driver, including outside decisions and prepared replies.
Limit: the coupled command queue remains a separate producer premise.
Consumer: CrewLogs.history at the two concrete crew source instances.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The joint machine fact reads every frame, captured scope and tracked child at one store. -/
structure Configuration (spec : Spec) (machine : NativeMachine) : Prop where
  frames : FramesAt spec machine
  scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes
  children : ChildrenReady spec machine

/-- Actual command execution advances the three machine observations together. -/
theorem Configuration.command (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) (machine : NativeMachine)
    (command : Guard.NCmd) (rest : List Guard.NCmd) (held : Configuration spec machine)
    (permission : CommandPremises spec machine command) (track : TrackDemand spec machine command) :
    letI := evaluatorFor spec.root spec.table
    Configuration spec (driveStep (interpOf spec.root spec.table) machine command rest).1 := by
  obtain ⟨frames, scopes⟩ := command_scoped_frames spec fragment raceFree machine command rest permission held.frames
  exact ⟨frames, scopes, held.children.command spec machine command rest track⟩

/-- Outside administrative edits retain captured scope fields without touching their contents. -/
theorem scope_edits (spec : Spec) :
    Lift.MachineEdits (interpOf spec.root spec.table)
      (fun (machine : NativeMachine) => Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) where
  drain := fun _ _ _ held _ => held
  ran := fun _ _ _ held => held
  yield := by
    intro machine id verdict held
    rw [StatePreservation.modify_state]
    exact held
  interrupt := by
    intro machine who extra target fiber held lookup
    unfold Lift.interruptEdit
    dsimp only
    split <;> exact held
  middleware := fun _ held => held
  clock := fun _ _ held _ => held
  owed := by
    intro machine owed held
    rw [StatePreservation.drain_state]
    exact held
  prepare := by
    intro machine id token answer held
    rw [(SourceScope.prepare_reply_at spec.root spec.table machine id token answer).1]
    exact held

/-- The same outside decision preserves every part of the coupled machine fact. -/
theorem configuration_edits (spec : Spec) :
    Lift.MachineEdits (interpOf spec.root spec.table) (Configuration spec) := by
  have frames := (outside_facts spec).machineEdits
    (fun state cause fiber held => FrameAt.interruption spec ⟨fiber.id, state⟩ fiber cause held)
  have scopes := scope_edits spec
  have children := ChildrenReady.machine_edits spec
  constructor
  · intro machine owner fiber held lookup
    exact ⟨frames.drain machine owner fiber held.frames lookup,
      scopes.drain machine owner fiber held.scopes lookup, children.drain machine owner fiber held.children lookup⟩
  · intro machine owner task held
    exact ⟨frames.ran machine owner task held.frames, scopes.ran machine owner task held.scopes,
      children.ran machine owner task held.children⟩
  · intro machine id verdict held
    exact ⟨frames.yield machine id verdict held.frames, scopes.yield machine id verdict held.scopes,
      children.yield machine id verdict held.children⟩
  · intro machine who extra target fiber held lookup
    exact ⟨frames.interrupt machine who extra target fiber held.frames lookup,
      scopes.interrupt machine who extra target fiber held.scopes lookup,
      children.interrupt machine who extra target fiber held.children lookup⟩
  · intro machine held
    exact ⟨frames.middleware machine held.frames, scopes.middleware machine held.scopes,
      children.middleware machine held.children⟩
  · intro machine millis held running
    exact ⟨frames.clock machine millis held.frames running, scopes.clock machine millis held.scopes running,
      children.clock machine millis held.children running⟩
  · intro machine owed held
    exact ⟨frames.owed machine owed held.frames, scopes.owed machine owed held.scopes,
      children.owed machine owed held.children⟩
  · intro machine id token answer held
    exact ⟨frames.prepare machine id token answer held.frames, scopes.prepare machine id token answer held.scopes,
      children.prepare machine id token answer held.children⟩

/-- Source ownership and the existing driver guard carry parked shape without a new queue assertion. -/
theorem source_parked_lift (root : NativeEff) (fragment : SourceScope.Fragment root) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift (Lift.pairOrder Lift.unitOrder Lift.unitOrder) (interpOf root table)
      (fun _ machine => (Guard.GuardState machine ∧ SourceScope.ConfigurationAt root machine) ∧ ParkedShape.Configuration machine)
      (fun _ machine commands => Guard.DriverQueue root table machine commands ∧ SourceScope.CommandsAt root commands)
      (fun _ machine tasks => Guard.DriverTasks machine tasks ∧ SourceScope.TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  apply (Guard.source_decision_lift root fragment table).withMachineFact ParkedShape.Configuration
  · intro tasks world machine command rest running before held
    exact held.command root table machine command rest ((before.2 running).1.1.1.authority command (List.mem_cons_self ..))
  · exact ParkedShape.machine_edits root table
  · intro world machine id token value before held running admitted
    exact ParkedShape.Configuration.command root table _ _ _ (held.fields rfl) trivial

/-- The source begins in its actual first allocation phase with empty captures and children. -/
theorem initial_configuration (spec : Spec) (fuel : Nat) : Configuration spec (Api.load spec.root fuel) := by
  constructor
  · intro fiber member
    have same := List.mem_singleton.mp member
    subst fiber
    exact ⟨.stable .root, .stable .root, initial_code spec Stores.empty fuel [] rfl rfl, .nil _⟩
  · intro scope member
    cases member
  · exact initial_children spec fuel
end Effect4.Program.AnswerSlots.Initialized
