import Effect4.Laws.Program.NativeExecutor
import Effect4.Laws.Program.CodeClosure.ConfigurationCommands
import Effect4.Laws.Program.CodeClosure.ConfigurationAdministration
import Effect4.Laws.Machine.Lift

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The command invariant retains code in the actual queue and dispatcher snapshot.
Its rules follow native evaluation, observers, resumes and scope closure.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The native loop top changes only administrative interrupt fields and its failure primitive. -/
theorem loop_top_at (root : NativeEff) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (runloopTop fiber) := by
  unfold runloopTop
  split
  · exact ⟨⟨trivial, held.frame.2⟩, held.pending, held.dispatcher⟩
  · exact held

/-- Charging an operation leaves every source-bearing slot intact. -/
theorem count_at (root : NativeEff) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (countOp fiber) := ⟨held.frame, held.pending, held.dispatcher⟩

/-- Forced yield retains the deferred program as its actual constant continuation. -/
theorem yield_at (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (it : SourceIteration) (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (found : injectYield m fiber yielding = some it) : EvaluationAt root it := by
  unfold injectYield at found
  split at found
  · cases found
    exact ⟨configuration_emit root m _ owned,
      ⟨⟨⟨trivial, held.frame.1⟩, held.frame.2⟩, held.pending, held.dispatcher⟩,
      by intro command member; cases member⟩
  · cases found

/-- One actual native iteration retains its evaluation result's source locations. -/
theorem iteration_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding) := by
  have charged := count_at root _ (loop_top_at root fiber held)
  unfold iteration
  dsimp only
  split
  · rename_i it found
    have retained := yield_at root m _ yielding it owned charged found
    exact native_at root fragment table it.machine it.fiber it.yielding retained.machine retained.fiber
  · exact native_at root fragment table m _ yielding owned charged

/-- Settling retains stored source slots and the actual pending command suffix. -/
theorem settleOutcome_at (root : NativeEff) (id : FiberId) (rest : List SourceCommand) (it : SourceIteration)
    (owned : EvaluationAt root it) (pending : CommandsAt root rest) :
    ConfigurationAt root (settleOutcome id rest it).1 ∧ CommandsAt root (settleOutcome id rest it).2 :=
  CodeClosure.Configuration.settleOutcome_at (configurationModel root) root id rest it owned pending

/-- Settlement interprets the source-preserving word before selecting its actual owner. -/
theorem settle_at (root : NativeEff) (id : FiberId) (rest : List SourceCommand) (it : SourceIteration)
    (owned : EvaluationAt root it) (pending : CommandsAt root rest) :
    ConfigurationAt root (settle id rest it).1 ∧ CommandsAt root (settle id rest it).2 :=
  CodeClosure.Configuration.settle_at (configurationModel root) root (fun _ => True.intro) id rest it owned pending

/-- Race settlement introduces only administrative cleanup and the accepted exit. -/
theorem race_settle_at (root : NativeEff) (table : RowTable) (race : Nat) (cleanup : Bool) (exit : ExitV)
    (allowed : RaceAllowed root) :
    CodeAt root ((interpOf root table).raceSettle race cleanup exit) := by
  change CodeAt root (embed (raceSettleProgram race cleanup exit))
  unfold raceSettleProgram
  split
  · refine ⟨allowed, trivial, ?_⟩
    intro _ _ wrong
    cases wrong
  · cases exit <;> trivial

/-- A native owed completion embeds only a completion primitive. -/
theorem owed_completion_at (root : NativeEff) (owed : Owed (Completion Val Err Defect FiberId Ann)) :
    CodeAt root (Owed.mapCode (fun c => embed (completionPrim c)) owed).code ∧
      TerminalReply (Owed.mapCode (fun c => embed (completionPrim c)) owed).code :=
    ⟨completion_at root owed.code, completion_reply owed.code⟩

/-- The due drain retains its scope captures and every actual completion program. -/
theorem due_at (root : NativeEff) (table : RowTable) (state : Stores) (owned : ScopesAt root state.scopes) :
    ScopesAt root ((interpOf root table).dueResumes state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).dueResumes state).1, CodeAt root owed.code ∧ TerminalReply owed.code := by
  refine ⟨owned, ?_⟩
  intro owed member
  obtain ⟨completion, _, eq⟩ := List.mem_map.mp member
  rw [← eq]
  exact owed_completion_at root completion

/-- Draining owned completions retains the posted tasks and returned resumes. -/
theorem drain_at (root : NativeEff) (m : NativeMachine) (due : List (Owed NCode))
    (owned : ConfigurationAt root m) (saved : ∀ owed ∈ due, CodeAt root owed.code ∧ TerminalReply owed.code) :
    ConfigurationAt root (drainOwed m due).1 ∧ CommandsAt root (drainOwed m due).2 :=
  CodeClosure.Configuration.drain_at (configurationModel root) m due owned saved

/-- An actual published exit removes pending callbacks while retaining its source stack. -/
theorem publish_at (root : NativeEff) (fiber : SourceFiber) (exit : ExitV) (held : FiberAt root fiber) :
    FiberAt root (fiber.publish exit) :=
  CodeClosure.Configuration.publish_at (configurationModel root) fiber exit held

/-- Exit completion clears the saved stack without introducing code. -/
theorem cleared_at (root : NativeEff) (table : RowTable) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (fiber.cleared (interpOf root table)) :=
  CodeClosure.Configuration.cleared_at (configurationModel root) root table fiber held

/-- The actual exit path retains middleware cleanup and every observer command. -/
theorem exit_fiber_at (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : SourceFiber)
    (exit : ExitV) (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    ConfigurationAt root (exitFiber (interpOf root table) m fiber exit).1 ∧
      CommandsAt root (exitFiber (interpOf root table) m fiber exit).2 :=
  CodeClosure.Configuration.exit_fiber_at (configurationModel root) root table (fun _fiber exit => success_restore_at root _ exit trivial) m fiber exit owned held

/-- Interrupting a target list changes only administrative fiber fields. -/
theorem interrupt_each_at (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (acc : NativeMachine × List SourceCommand)
    (owned : ConfigurationAt root acc.1) (pending : CommandsAt root acc.2) :
    ConfigurationAt root (interruptEach (interpOf root table) who extra targets acc).1 ∧
      CommandsAt root (interruptEach (interpOf root table) who extra targets acc).2 :=
  CodeClosure.Configuration.interrupt_each_at (configurationModel root) root table (fun _ => True.intro) who extra targets acc owned pending

/-- Updating countdown bookkeeping retains its stored continuation name. -/
theorem pending_map_at (root : NativeEff) (fiber : SourceFiber)
    (edit : Pending EffName Val Err Defect FiberId Ann → Pending EffName Val Err Defect FiberId Ann)
    (held : FiberAt root fiber) (kept : ∀ p, (edit p).resumeWith = p.resumeWith) :
    FiberAt root {fiber with pending := fiber.pending.map edit} :=
  CodeClosure.Configuration.pending_map_at (configurationModel root) fiber edit held kept

/-- Native finalizer removal retains the surviving source captures. -/
theorem drop_at (root : NativeEff) (table : RowTable) (scope key : Nat) (state next : Stores)
    (owned : ScopesAt root state.scopes)
    (found : (interpOf root table).dropFinalizer scope key state = some next) : ScopesAt root next.scopes := by
  simp only [interpOf] at found
  split at found
  · cases found
  · cases found
    exact scope_remove_at root state.scopes scope key owned

/-- Lexical ownership supplies the shared observer's terminal and scope introductions. -/
theorem observer_facts (root : NativeEff) (table : RowTable) :
    CodeClosure.Configuration.ObserverFacts (configurationModel root) root table where
  failure := fun _ => True.intro
  exitValue := exit_value_at root [] table
  countdown := countdown_program_at root [] table
  raceSettle := race_settle_at root table
  drop := drop_at root table

set_option maxHeartbeats 1200000 in
/-- Every actual observer callback retains source programs returned as resumes. -/
theorem observer_at (root : NativeEff) (table : RowTable) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List SourceCommand) (observer : Observer)
    (owned : ConfigurationAt root acc.1) (pending : CommandsAt root acc.2) :
    ConfigurationAt root (fireObserver (interpOf root table) id exit acc observer).1 ∧
      CommandsAt root (fireObserver (interpOf root table) id exit acc observer).2 :=
  CodeClosure.Configuration.observer_at (configurationModel root) root table (observer_facts root table) id exit acc observer owned pending

/-- The native await program embeds a represented park or an observed exit. -/
theorem await_code_at (root : NativeEff) (table : RowTable) (m : NativeMachine) (kind : ParkKind) :
    CodeAt root (awaitCode (interpOf root table) m kind) := by
  cases kind
  case join target mode =>
    unfold awaitCode
    dsimp only
    split
    · exact exit_value_at root [] table _ mode
    · trivial
  all_goals trivial

/-- A race entrant is spawned from the actual owned head program. -/
theorem launch_at (root : NativeEff) (table : RowTable) (race : Nat) (m : NativeMachine)
    (host : SourceFiber) (program : NCode) (site : List Nat)
    (owned : ConfigurationAt root m) (source : CodeAt root program) :
    ConfigurationAt root (launchEntrant (interpOf root table) race m host program site).1 := by
  unfold launchEntrant
  exact configuration_spawn root [] table m host program ⟨true, true, .interruptible⟩ site owned source

/-- The direct lexical instance supplies the shared command census's local facts. -/
theorem command_facts (root : NativeEff) (fragment : Fragment root) (table : RowTable) :
    CodeClosure.Configuration.CommandFacts (configurationModel root) root table where
  iteration := iteration_at root fragment table
  native := native_at root fragment table
  settle := settle_at root
  observer := observer_at root table
  due := due_at root table
  drain := drain_at root
  raceSettle := race_settle_at root table
  cancel := by intros; trivial
  interruption := interrupt_cause_at root
  awaitRestore := fun m kind => success_restore_at root _ _ (await_code_at root table m kind)
  park := by intros; trivial
  closeDone := by trivial
  link := link_at root [] table
  exit := exit_fiber_at root table

/-- Every actual native command retains configuration ownership and pending resume code. -/
theorem command_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (m : NativeMachine) (command : SourceCommand) (rest : List SourceCommand)
    (owned : ConfigurationAt root m) (pending : CommandsAt root (command :: rest)) :
    ConfigurationAt root (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1 ∧
      CommandsAt root (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).2 :=
  CodeClosure.Configuration.command_at (configurationModel root) root table
    (command_facts root fragment table) m command rest owned pending

end Effect4.Program.SourceScope
