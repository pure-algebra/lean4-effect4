import Effect4.Laws.Program.NativeCommands
import Effect4.Laws.Program.CodeClosure.ConfigurationHistory
import Effect4.Laws.Run.Frame

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The existing decision lift carries the actual drained task snapshot.
The history endpoint applies to controls at arbitrary command and compile budgets.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-- Draining returns the owned task snapshot and an empty dispatcher. -/
theorem dispatcher_drain_at (root : NativeEff) (dispatcher : SourceDispatcher)
    (held : DispatcherAt root dispatcher) :
    TasksAt root dispatcher.drain.1 ∧ DispatcherAt root dispatcher.drain.2 :=
  CodeClosure.Configuration.dispatcher_drain_at (configurationModel root) dispatcher held

/-- The clock emits only a native completion and retains scope captures. -/
theorem clock_at (root : NativeEff) (table : RowTable) (millis : ClockMillis) (state : Stores)
    (held : ScopesAt root state.scopes) :
    ScopesAt root ((interpOf root table).clockStep millis state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).clockStep millis state).1, CodeAt root owed.code ∧ TerminalReply owed.code := by
  refine ⟨held, ?_⟩
  intro owed member
  rw [Option.mem_def] at member
  obtain ⟨completion, _, eq⟩ := Option.map_eq_some_iff.mp member
  rw [← eq]
  exact owed_completion_at root completion

/-- A queued task's actual command list retains its resume code. -/
theorem task_commands_at (root : NativeEff) (task : SourceTask) (held : TaskAt root task) :
    CommandsAt root (taskCmds task) :=
  CodeClosure.Configuration.task_commands_at (configurationModel root) task held

/-- Source ownership follows the actual native decision lift, including drained snapshots. -/
theorem decision_lift_at (root : NativeEff) (fragment : Fragment root) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m) (fun _ _ cmds => CommandsAt root cmds)
      (fun _ _ tasks => TasksAt root tasks) (fun _ _ d => IsControl d) :=
  CodeClosure.Configuration.decision_lift (configurationModel root) root table
    (command_facts root fragment table) IsControl (clock_at root table)
    (by intro m id token answer owned refused; exact False.elim refused)

/-- The actual load starts with its source root and no saved callback or task. -/
theorem load_at (root : NativeEff) (fragment : Fragment root) (compileFuel : Nat) :
    ConfigurationAt root (Api.load root compileFuel) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fiber member
    rw [List.mem_singleton.mp member]
    apply fiber_make_at
    exact resolve_scoped root fragment (rootPoint compileFuel) rfl
  · intro race member; cases member
  · intro scope member; cases member

/-- Source ownership follows every control in the real history at all explicit budgets. -/
theorem history_at (b : Api.Built) (fragment : Fragment b.program) (compileFuel : Nat)
    (m : NativeMachine) (history : ControlHistory b compileFuel m) : ConfigurationAt b.program m := by
  letI := evaluatorFor b.program b.table
  obtain ⟨rows, controls, rfl⟩ := history
  have step (before : NativeMachine) (row : Nat × NativeDecision) (owned : ConfigurationAt b.program before)
      (control : IsControl row.2) : ConfigurationAt b.program (stepBy b before row) := by
    obtain ⟨_, _, held⟩ := Lift.stepDecisionState_lift (decision_lift_at b.program fragment b.table) row.1 () before row.2 owned control
    exact held
  have fold : ∀ (rows : List (Nat × NativeDecision)) (before : NativeMachine), (∀ row ∈ rows, IsControl row.2) → ConfigurationAt b.program before →
      ConfigurationAt b.program (rows.foldl (stepBy b) before) := by
    intro rows
    induction rows with
    | nil => intro before _ held; exact held
    | cons row rest ih =>
      intro before controls held
      exact ih (stepBy b before row) (fun x member => controls x (.tail _ member))
        (step before row held (controls row (.head _)))
  exact fold rows _ controls (load_at b.program fragment compileFuel)

/-- A real history supplies the source premise for its actual current synchronous writer. -/
theorem history_sync_keeps (b : Api.Built) (fragment : Fragment b.program) (compileFuel : Nat)
    (m : NativeMachine) (history : ControlHistory b compileFuel m) (id : FiberId) (fiber : SourceFiber)
    (found : m.fiber? id = some fiber) (thunk : EffThunk) (current : fiber.frame.current = .sync thunk)
    (P : Val → Prop) (sites : HeapSites.SitesKeep b.program P)
    (next : Stores) (answer : Val)
    (step : (interpAt b.program m.completedExits b.table).syncState thunk m.state = some (next, answer))
    (heap : HeapSites.HeapOk P m.state.refs) : HeapSites.HeapOk P next.refs := by
  have owned := history_at b fragment compileFuel m history
  have held := (configuration_fiber b.program m id fiber owned found).frame.1
  rw [current] at held
  exact sync_heap_at b.program m.completedExits b.table thunk m.state next answer P sites heap held step

end Effect4.Program.SourceScope
