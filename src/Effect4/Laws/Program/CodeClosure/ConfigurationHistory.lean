import Effect4.Laws.Program.CodeClosure.ConfigurationCommands
import Effect4.Laws.Run.Frame

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: one actual decision transport serves both source configuration instances.
Consumer: lexical source ownership and full finalizer source funding.
The supplied native command, clock, and reply contracts remain explicit premises.
The transport retains the existing dispatcher snapshot across every command budget.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Run

/-- Draining returns the owned task snapshot and an empty dispatcher. -/
theorem dispatcher_drain_at (model : Model) (dispatcher : SourceDispatcher)
    (held : DispatcherAt model dispatcher) :
    TasksAt model dispatcher.drain.1 ∧ DispatcherAt model dispatcher.drain.2 := by
  refine ⟨?_, ?_⟩
  · intro task member
    obtain ⟨tasks, present, member⟩ := List.mem_flatten.mp member
    obtain ⟨bucket, stored, eq⟩ := List.mem_map.mp present
    rw [← eq] at member
    exact held bucket stored task member
  · intro bucket member; cases member

/-- A queued task's actual command list retains its resume code. -/
theorem task_commands_at (model : Model) (task : SourceTask) (held : TaskAt model task) :
    CommandsAt model (taskCmds task) := by
  cases task
  all_goals intro c member
  all_goals rcases List.mem_cons.mp member with same | later
  all_goals (aesop (add norm simp [CommandAt, List.mem_cons, TaskAt]))

/-- The existing decision lift transports the supplied code-location model. -/
theorem decision_lift (model : Model) (root : NativeEff) (table : RowTable)
    (facts : CommandFacts model root table) (allows : NativeDecision → Prop)
    (clock : ∀ millis (state : Stores), model.scopes state.scopes →
      model.scopes ((interpOf root table).clockStep millis state).2.scopes ∧
        ∀ owed ∈ ((interpOf root table).clockStep millis state).1,
          model.code owed.code ∧ TerminalReply owed.code)
    (reply : ∀ m id token answer, ConfigurationAt model m → allows (.answerAsync id token answer) →
      ConfigurationAt model {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1} ∧
        model.code (prepareAsyncAnswer (interpOf root table) m id token answer).2 ∧
          TerminalReply (prepareAsyncAnswer (interpOf root table) m id token answer).2) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt model m) (fun _ _ cmds => CommandsAt model cmds)
      (fun _ _ tasks => TasksAt model tasks) (fun _ _ d => allows d) := by
  letI := evaluatorFor root table
  refine {
    step := ?_, nil := ?_, evaluate := ?_, drain := ?_, ran := ?_, task := ?_, skip := ?_,
    yield := ?_, interrupt := ?_, middleware := ?_, clockNone := ?_, clockSome := ?_, answer := ?_ }
  · intro ts w m c rest notStuck held
    have moved := command_at model root table facts m c rest held.1 ((held.2 notStuck).1)
    exact ⟨(), trivial, moved.1, fun _ => ⟨moved.2, (held.2 notStuck).2⟩⟩
  · intro w m task member; cases member
  · intro w m id owned notStuck c member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; trivial
    · rw [List.mem_singleton.mp later]; trivial
  · intro w m owner fiber owned found
    have held := configuration_fiber model m owner fiber owned found
    have snapshot := dispatcher_drain_at model fiber.dispatcher held.dispatcher
    have updated : ConfigurationAt model (m.update {fiber with dispatcher := fiber.dispatcher.drain.2}) :=
      configuration_update model m _ owned ⟨held.frame, held.pending, snapshot.2⟩
    exact ⟨⟨updated.fibers, updated.races, updated.scopes⟩, snapshot.1⟩
  · intro w m owner task owned; exact configuration_emit model m _ owned
  · intro w m owner task rest owned notStuck held
    exact ⟨task_commands_at model task (held task (.head _)), fun t member => held t (.tail _ member)⟩
  · intro w m task rest held t member; exact held t (.tail _ member)
  · intro w m id verdict owned
    exact configuration_modify model m id _ owned (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩)
  · intro w m who extra target fiber owned found
    have held := configuration_fiber model m target fiber owned found
    have changed := facts.interruption (interruptCause (interpOf root table) who extra fiber.id) fiber held
    unfold Lift.interruptEdit
    dsimp only
    split
    · exact configuration_update model _ _ (configuration_emit model _ _ (configuration_emit model m _ owned)) changed
    · exact configuration_update model _ _ (configuration_emit model m _ owned) changed
  · intro w m owned; exact ⟨owned.fibers, owned.races, owned.scopes⟩
  · intro w m millis state owned notStuck found
    have retained := clock millis m.state owned.scopes
    rw [found] at retained
    exact ⟨(), trivial, owned.fibers, owned.races, retained.1⟩
  · intro w m millis owed state owned notStuck found
    have retained := clock millis m.state owned.scopes
    rw [found] at retained
    have moved := facts.drain {m with state} [owed] ⟨owned.fibers, owned.races, retained.1⟩
      (by intro item member; rw [List.mem_singleton.mp member]; exact retained.2 owed rfl)
    exact ⟨(), trivial, moved.1, fun _ => commands_append model _ _ moved.2
      (by intro c member; rw [List.mem_singleton.mp member]; trivial)⟩
  · intro w m id token answer owned notStuck allowed
    have prepared := reply m id token answer owned allowed
    have pending : CommandsAt model
        [.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2, .drainDue] := by
      intro command member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; exact prepared.2
      · rw [List.mem_singleton.mp later]; trivial
    have moved := command_at model root table facts _ _ [.drainDue] prepared.1 pending
    exact ⟨(), trivial, moved.1, fun _ => ⟨moved.2, by intro task member; cases member⟩⟩

end Effect4.Program.CodeClosure.Configuration
