import Test.Dogfood.Scenario.Atomic.StageSettlement
import Effect4.Laws.Machine.AnswerFlowGhostCommands

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the actual Atomic joint command and detached-task assertions.
Live native commands retain actual frame permission separately from dormant stored rows.
Completion commands retain the exact exit that their actual publication consumes.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- An actual completion command retains each matching request's finalized observation. -/
def CompletedAt (world : StageWorld.World) (id : FiberId) (exit : ExitV) : Prop :=
  ∀ owner ∈ requests, id = ⟨owner + 1⟩ → FinalExitAt world owner (some exit)

/-- Live command permission names the actual row read by that command. -/
def LiveAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (id : FiberId) : Prop :=
  ∀ fiber ∈ machine.fibers, fiber.id = id → StageRoles.FrameAt root table world fiber.id fiber.frame

/-- Requests receive only scheduler void replies; root and daemon may receive awaited exits. -/
inductive ReplyAt (id : FiberId) : NCode → Prop
  | unit : ReplyAt id (.success .unit)
  | read (cell : RefKey) (small : id.value < 2) : ReplyAt id (.sync (.store (.op (.refGet cell))))
  | exit (result : ExitV) (small : id.value < 2) : ReplyAt id (Prim.ofExit result)

/-- A reply owes its source class only at an actual matching parked token. -/
def ReplyPermission (machine : NativeMachine) (id : FiberId) (token : Nat) (code : NCode) : Prop :=
  ∀ fiber ∈ machine.fibers, fiber.id = id → fiber.parked = .withGuard token → ReplyAt id code

/-- An unconditional source reply class supplies every actual matching admission. -/
theorem ReplyAt.permission {machine : NativeMachine} {id : FiberId} {token : Nat} {code : NCode}
    (reply : ReplyAt id code) : ReplyPermission machine id token code := fun _ _ _ _ => reply

/-- Detached admission is conditional on the same actual parked token. -/
inductive TaskPermission (machine : NativeMachine) : Guard.NTask → Prop
  | start (id : FiberId) : TaskPermission machine (.start id)
  | resume (id : FiberId) (token : Nat) (code : NCode) (reply : ReplyPermission machine id token code) :
      TaskPermission machine (.resume id token code)

/-- Detached tasks retain the exact reply profile emitted by this source. -/
inductive TaskAt : Guard.NTask → Prop
  | start (id : FiberId) : TaskAt (.start id)
  | resume (id : FiberId) (token : Nat) (code : NCode) (reply : ReplyAt id code) : TaskAt (.resume id token code)

/-- Actual completion custody retains the terminal saved stack consumed by root middleware. -/
def FinishAt (machine : NativeMachine) (id : FiberId) : Prop :=
  ∀ fiber ∈ machine.fibers, fiber.id = id → fiber.frame.stack = []

/-- An actual after-interruption owner retains its receiving suffix at the selected world. -/
def AfterPermission (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (id : FiberId) (kind : ParkKind) : Prop :=
  ∀ fiber ∈ machine.fibers, fiber.id = id →
    (id = ⟨0⟩ → RootGraph.AfterAt root table world kind fiber.frame) ∧
    (id = ⟨1⟩ → DaemonGraph.FrameAt root table world fiber.frame)

/-- Actual command classes retain their own live role, completed exit or administrative admission. -/
inductive CommandAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) : Guard.NCmd → Prop
  | evaluate (id : FiberId) : CommandAt root table world machine (.evaluate id)
  | loop (id : FiberId) (yielding : Bool) (live : LiveAt root table world machine id) :
      CommandAt root table world machine (.loop id yielding)
  | deliver (id : FiberId) (yielding : Bool) (live : LiveAt root table world machine id) :
      CommandAt root table world machine (.deliver id yielding)
  | finish (id : FiberId) (exit : ExitV) (completed : CompletedAt world id exit) (empty : FinishAt machine id) :
      CommandAt root table world machine (.finish id exit)
  | resume (id : FiberId) (token : Nat) (code : NCode) (reply : ReplyPermission machine id token code) :
      CommandAt root table world machine (.resume id token code)
  | interrupt (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
      CommandAt root table world machine (.interruptTarget target who extra)
  | afterInterrupt (id : FiberId) (yielding : Bool) (kind : ParkKind) (small : id.value < 2) (noRace : ∀ race, kind ≠ .race race)
      (receiving : AfterPermission root table world machine id kind) :
      CommandAt root table world machine (.afterInterrupt id yielding kind)
  | track (parent child : FiberId) (rootParent : parent = ⟨0⟩) :
      CommandAt root table world machine (.trackChild parent child)
  | observe (id : FiberId) (exit : ExitV) (observer : Observer) (allowed : ObserverAt observer) :
      CommandAt root table world machine (.observe id exit observer)
  | exitDone (id : FiberId) : CommandAt root table world machine (.exitDone id)
  | drain : CommandAt root table world machine .drainDue

/-- All actual queued commands retain their class at the same stage world. -/
def QueueAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (commands : List Guard.NCmd) : Prop :=
  ∀ command ∈ commands, CommandAt root table world machine command

/-- The detached scheduler snapshot retains the same source reply profile. -/
def SnapshotAt (_world : StageWorld.World) (machine : NativeMachine) (tasks : List Guard.NTask) : Prop :=
  ∀ task ∈ tasks, TaskPermission machine task

/-- Existing command classifiers select only the actual loop and delivery owners. -/
def LiveOwners (machine : NativeMachine) (commands : List Guard.NCmd) : List FiberId :=
  commands.filterMap (fun command => if AnswerFlow.ghostAdvancing command then Guard.commandOwner machine command else none)

/-- Native owners and actual daemon interruption waits retain a strong frame certificate. -/
def FrameOwners (machine : NativeMachine) (commands : List Guard.NCmd) : List FiberId :=
  commands.filterMap (fun command =>
    if AnswerFlow.ghostAdvancing command ||
      (decide (command.ctorIdx = (Cmd.afterInterrupt ⟨1⟩ false (.awaitAll []) : Guard.NCmd).ctorIdx) &&
        decide (Guard.commandOwner machine command = some ⟨1⟩))
    then Guard.commandOwner machine command else none)

/-- The existing command certificates supply the actual selected strong rows. -/
theorem QueueAt.frame_owners (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (commands : List Guard.NCmd) (held : QueueAt root table world machine commands)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers)
    (pending : fiber.id ∈ FrameOwners machine commands) : StageRoles.FrameAt root table world fiber.id fiber.frame := by
  obtain ⟨command, present, found⟩ := List.mem_filterMap.mp pending
  split at found
  · rename_i selected
    have typed := held command present
    cases typed with
    | loop id yielding live => exact live fiber member (Option.some.inj found).symm
    | deliver id yielding live => exact live fiber member (Option.some.inj found).symm
    | afterInterrupt id yielding kind small noRace receiving =>
      have identity := (Option.some.inj found).symm
      have daemon : id = ⟨1⟩ := Option.some.inj (of_decide_eq_true selected)
      exact .daemon (identity.trans daemon) ((receiving fiber member identity).2 daemon)
    | evaluate | finish | resume | interrupt | track | observe | exitDone | drain => cases selected
  · cases found

/-- The real queued native owners retain strong row permissions independently of dormant rows. -/
theorem QueueAt.live_owners (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (commands : List Guard.NCmd) (held : QueueAt root table world machine commands)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (pending : fiber.id ∈ LiveOwners machine commands) :
    StageRoles.FrameAt root table world fiber.id fiber.frame := by
  obtain ⟨command, present, found⟩ := List.mem_filterMap.mp pending
  by_cases advancing : AnswerFlow.ghostAdvancing command = true
  · simp only [if_pos advancing] at found
    have typed := held command present
    cases typed with
    | loop id yielding live =>
      change some id = some fiber.id at found
      exact live fiber member (Option.some.inj found).symm
    | deliver id yielding live =>
      change some id = some fiber.id at found
      exact live fiber member (Option.some.inj found).symm
    | evaluate | finish | resume | interrupt | afterInterrupt | track | observe | exitDone | drain => cases advancing
  · simp only [if_neg advancing] at found
    cases found

/-- Earlier completed exits retain their finalized observation at the chosen next native world. -/
theorem CompletedAt.future (before after : StageWorld.World) (future : Future before after)
    (id : FiberId) (exit : ExitV) (held : CompletedAt before id exit) : CompletedAt after id exit :=
  fun owner member same => final_exit_future before after future owner (some exit) (held owner member same)

/-- Local machine changes transport all actual queued certificates through their four readers.
Consumer: Atomic's contextual fixed-command and native settlement producers. -/
theorem QueueAt.transport (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (first last : NativeMachine) (commands : List Guard.NCmd)
    (held : QueueAt root table before first commands)
    (live : ∀ id, id ∈ commands.filterMap (Guard.commandOwner first) →
      LiveAt root table before first id → LiveAt root table after last id)
    (finish : ∀ id, id ∈ commands.filterMap (Guard.commandOwner first) → FinishAt first id → FinishAt last id)
    (reply : ∀ id token code, .resume id token code ∈ commands →
      ReplyPermission first id token code → ReplyPermission last id token code)
    (receiving : ∀ id kind, id ∈ commands.filterMap (Guard.commandOwner first) →
      AfterPermission root table before first id kind → AfterPermission root table after last id kind) :
    QueueAt root table after last commands := by
  intro command member
  cases held command member with
  | evaluate id => exact .evaluate id
  | loop id yielding typed => exact .loop id yielding (live id (List.mem_filterMap.mpr ⟨_, member, rfl⟩) typed)
  | deliver id yielding typed => exact .deliver id yielding (live id (List.mem_filterMap.mpr ⟨_, member, rfl⟩) typed)
  | finish id exit completed empty => exact .finish id exit (completed.future before after future id exit) (finish id (List.mem_filterMap.mpr ⟨_, member, rfl⟩) empty)
  | resume id token code typed => exact .resume id token code (reply id token code member typed)
  | interrupt target who extra => exact .interrupt target who extra
  | afterInterrupt id yielding kind small noRace typed =>
    exact .afterInterrupt id yielding kind small noRace (receiving id kind (List.mem_filterMap.mpr ⟨_, member, rfl⟩) typed)
  | track parent child rootParent => exact .track parent child rootParent
  | observe id exit observer allowed => exact .observe id exit observer allowed
  | exitDone id => exact .exitDone id
  | drain => exact .drain

end Test.Dogfood.Scenario.Atomic.StageConfiguration
