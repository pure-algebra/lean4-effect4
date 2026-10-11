import Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue
import Effect4.Laws.Program.ReleaseCustody.ScopeRows
import Effect4.Laws.Program.NativeCommands
import Effect4.Laws.Program.Guard.Driver
import Effect4.Laws.Program.Guard.ForkLedger

/-!
Concept: scope-lifetime-finalization R11.
Question: complete native command closure serves Execution.history and Workers.releases_step.
Reach: actual source-owned native commands, sequential and race-free source, and Guard ownership.
Limit: this command assertion establishes neither scheduler closure nor progress by itself.
Unlock: the existing Lift transports the joined command assertion to admitted histories.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CommandClosure
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.CommandStacks

/-- The source-owned native countdown cannot install an arbitrary callback.
Consumer: the complete command assertion and its admitted-history lift. -/
theorem pending (root : NativeEff) (m : NativeMachine) (source : SourceScope.ConfigurationAt root m) :
    Execution.PendingShape m := by
  intro fiber member pending queued
  have owned := (source.fibers fiber member).pending pending queued
  cases resume : pending.resumeWith with
  | void => exact Or.inr (Or.inl rfl)
  | exitsValue => exact Or.inl rfl
  | continueWith name =>
    rw [resume] at owned
    exact False.elim owned

/-- Native task answers contain no foreign cleanup credit.
Consumer: dispatcher snapshots in the admitted-history lift. -/
theorem terminal_zero (q : List Nat) (code : NCode) (reply : SourceScope.TerminalReply code) :
    currentCredits q code = 0 := by
  cases reply <;> rfl

/-- The actual source predicate supplies the dispatcher accounting condition.
Consumer: the ready assertion after complete command closure. -/
theorem dispatcher (q : List Nat) (root : NativeEff) (m : NativeMachine)
    (source : SourceScope.ConfigurationAt root m) : Execution.DispatcherZero q m := by
  intro fiber member bucket stored task queued
  have owned := (source.fibers fiber member).dispatcher bucket stored task queued
  cases task with
  | start | wake => rfl
  | resume id token code => exact terminal_zero q code owned.2

theorem administrative (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (head : NCmd) (rest : List NCmd) (guard : GuardState m)
    (commands : GuardQueue root table m (head :: rest)) (scopes : Execution.ScopeRows m)
    (frames : ConfigurationKept m) (queue : QueueStable m (head :: rest))
    (source : SourceScope.ConfigurationAt root m) (code : SourceScope.CommandsAt root (head :: rest))
    (raceFree : SourceScope.RaceFreeSource root) (funded : Funded q m (head :: rest))
    (notLoop : ∀ id yielding, head ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, head ≠ .deliver id yielding) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m head rest
    Funded q out.1 out.2 ∧ ConfigurationKept out.1 ∧ QueueStable out.1 out.2 := by
  have empty := ReplySequencing.no_races root raceFree m source
  exact ⟨CommandDebit.non_evaluator root table q m head rest guard scopes (pending root m source)
    frames queue notLoop notDeliver funded,
    AdministrativeKept.non_evaluator root table m head rest frames queue
      (code head (List.mem_cons_self ..)) raceFree empty notLoop notDeliver,
    AdministrativeQueue.non_evaluator root table m head rest guard commands queue empty notLoop notDeliver⟩

/-- Every native command retains release accounting, stored frames and pending-owner stacks.
Consumer: the joint command assertion used by Execution.history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem command (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (head : NCmd) (rest : List NCmd) (guard : GuardState m)
    (commands : GuardQueue root table m (head :: rest)) (scopes : Execution.ScopeRows m)
    (frames : ConfigurationKept m) (queue : QueueStable m (head :: rest))
    (source : SourceScope.ConfigurationAt root m) (code : SourceScope.CommandsAt root (head :: rest))
    (fragment : SourceScope.Fragment root) (sequential : SourceScope.SequentialSource root)
    (raceFree : SourceScope.RaceFreeSource root) (funded : Funded q m (head :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m head rest
    Funded q out.1 out.2 ∧ ConfigurationKept out.1 ∧ QueueStable out.1 out.2 := by
  cases head with
  | loop id yielding =>
    exact LoopCommand.loop q root table m id yielding rest guard commands scopes frames queue
      source fragment sequential raceFree funded
  | deliver id yielding =>
    exact LoopCommand.deliver q root table m id yielding rest guard commands scopes frames queue
      source fragment sequential raceFree funded
  | evaluate | resume | launch | enrollRace | registrationDone | interruptTarget | afterInterrupt
    | raceCancel | trackChild | observe | exitDone | closeParAwait | link | finish | drainDue | wake =>
    exact administrative q root table m _ rest guard commands scopes frames queue source code raceFree funded
      (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong)

/-- Removing the pending command budget retains the stored release-credit bound.
Consumer: the ready assertion after a native command. -/
theorem funded_nil (q : List Nat) (m : NativeMachine) (commands : List NCmd)
    (held : Funded q m commands) : Funded q m [] := by
  simp only [Funded, List.map_nil, List.sum_nil] at held ⊢
  omega

/-- The machine facts jointly consumed by native command and scheduler closure. -/
def Held (q : List Nat) (root : NativeEff) (m : NativeMachine) : Prop :=
  Execution.Ready q m ∧ ConfigurationKept m ∧ SourceScope.ConfigurationAt root m ∧ GuardState m

/-- The existing pending queue jointly retains owners, registrations, code and credit. -/
def Queued (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (commands : List NCmd) : Prop :=
  GuardQueue root table m commands ∧ RegistrationQueue.RegistrationQueue commands ∧
    QueueStable m commands ∧ SourceScope.CommandsAt root commands ∧ Funded q m commands

/-- The actual command step retains every component of the joined custody assertion.
Consumer: the command prefix and scheduler lifts below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem joined (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (head : NCmd) (rest : List NCmd) (fragment : SourceScope.Fragment root)
    (sequential : SourceScope.SequentialSource root) (raceFree : SourceScope.RaceFreeSource root)
    (held : Held q root m) (queued : Queued q root table m (head :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m head rest
    Held q root out.1 ∧ Queued q root table out.1 out.2 := by
  letI := evaluatorFor root table
  have custody := command q root table m head rest held.2.2.2 queued.1 held.1.scopes
    held.2.1 queued.2.2.1 held.2.2.1 queued.2.2.2.1 fragment sequential raceFree queued.2.2.2.2
  have source := SourceScope.command_at root fragment table m head rest held.2.2.1 queued.2.2.2.1
  have guard := driveStep_invariants root table m head rest held.2.2.2 queued.1 queued.2.1
  have ready : Execution.Ready q (driveStep (interpOf root table) m head rest).1 :=
    ⟨ForkLedger.Invariant.Native.driveStep_ok root table m head rest held.1.fibers,
      ScopeRows.command root table m head rest held.1.scopes,
      pending root _ source.1, dispatcher q root _ source.1, funded_nil q _ _ custody.1⟩
  exact ⟨⟨ready, custody.2.1, source.1, guard.1⟩,
    guard.2.1, guard.2.2, custody.2.2, source.2, custody.1⟩

/-- Actual command prefixes retain custody at every fuel cut.
Consumer: scheduler tasks and admitted-history closure. -/
theorem drive (q : List Nat) (root : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (commands : List NCmd) (fragment : SourceScope.Fragment root)
    (sequential : SourceScope.SequentialSource root) (raceFree : SourceScope.RaceFreeSource root)
    (held : Held q root m) (queued : Queued q root table m commands) :
    letI := evaluatorFor root table
    let out := driveState (interpOf root table) fuel m commands
    Held q root out.1 ∧ Queued q root table out.1 out.2 := by
  letI := evaluatorFor root table
  exact Lift.driveState_lift_unit (interpOf root table)
    (fun next pending => Held q root next ∧ Queued q root table next pending)
    (fun next head rest _ kept => joined q root table next head rest fragment sequential raceFree kept.1 kept.2)
    fuel m commands ⟨held, queued⟩

end Effect4.Program.ReleaseCustody.CommandClosure
