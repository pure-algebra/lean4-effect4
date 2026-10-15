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
  | exit (result : ExitV) (small : id.value < 2) : ReplyAt id (Prim.ofExit result)

/-- Detached tasks retain the exact reply profile emitted by this source. -/
inductive TaskAt : Guard.NTask → Prop
  | start (id : FiberId) : TaskAt (.start id)
  | resume (id : FiberId) (token : Nat) (code : NCode) (reply : ReplyAt id code) : TaskAt (.resume id token code)

/-- Actual command classes retain their own live role, completed exit or administrative admission. -/
inductive CommandAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) : Guard.NCmd → Prop
  | evaluate (id : FiberId) : CommandAt root table world machine (.evaluate id)
  | loop (id : FiberId) (yielding : Bool) (live : LiveAt root table world machine id) :
      CommandAt root table world machine (.loop id yielding)
  | deliver (id : FiberId) (yielding : Bool) (live : LiveAt root table world machine id) :
      CommandAt root table world machine (.deliver id yielding)
  | finish (id : FiberId) (exit : ExitV) (completed : CompletedAt world id exit) :
      CommandAt root table world machine (.finish id exit)
  | resume (id : FiberId) (token : Nat) (code : NCode) (reply : ReplyAt id code) :
      CommandAt root table world machine (.resume id token code)
  | interrupt (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
      CommandAt root table world machine (.interruptTarget target who extra)
  | afterInterrupt (id : FiberId) (yielding : Bool) (kind : ParkKind) (small : id.value < 2) (noRace : ∀ race, kind ≠ .race race) :
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
def SnapshotAt (_world : StageWorld.World) (_machine : NativeMachine) (tasks : List Guard.NTask) : Prop :=
  ∀ task ∈ tasks, TaskAt task

/-- Existing command classifiers select only the actual loop and delivery owners. -/
def LiveOwners (machine : NativeMachine) (commands : List Guard.NCmd) : List FiberId :=
  commands.filterMap (fun command => if AnswerFlow.ghostAdvancing command then Guard.commandOwner machine command else none)

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

end Test.Dogfood.Scenario.Atomic.StageConfiguration
