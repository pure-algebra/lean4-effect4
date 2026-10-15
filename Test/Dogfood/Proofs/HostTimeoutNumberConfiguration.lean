import Test.Dogfood.Proofs.HostTimeoutNumberStable
import Test.Dogfood.Proofs.HostTimeoutNumberWait
import Test.Dogfood.Proofs.HostTimeoutState

/-!
Concepts: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: numeric roles and actual live-token replies advance jointly through the scheduler.
Consumer: the coupled command producer of both Timeout numeric goals.
Reach: active root regions, counted attempts, timer siblings, and retired fibers.
Limit: the initial allocation and between-attempt source phases need separate constructors.
These assertions do not supply their own preservation or an initialized history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberFlow HostTimeoutNumberRegion HostTimeoutNumberTimer
open HostTimeoutNumberWait HostTimeoutNumberPhase HostTimeoutState

/-- A role names existing numeric frames, the root's exact saved region, or the timer sibling. -/
inductive Role
  | numeric (output : HostTimeoutNumberFlow.Kind)
  | root (image : Image) (own : image.count = image.cleanups.length + 1) (suffix : List NCode)
  | timer
  | retired

/-- Role assignments are proof data indexed by existing fiber identifiers. -/
structure World where
  phase : Phase
  roles : List (FiberId × Role)

/-- The current numeric frame is checked at the actual store and completed-exit view. -/
def FrameAt (machine : Effect4.Program.NativeMachine) (role : Role)
    (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  match role with
  | .numeric output => AnswerFlow.FrameAt (model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state output frame
  | .root image own suffix => RootRegionAt machine.completedExits machine.state image own frame suffix
  | .timer => AnswerFlow.FrameAt (timerModel machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state () frame
  | .retired => True

/-- Published attempt exits retain their completed cleanup class until the form retires the role. -/
def ExitAt (machine : Effect4.Program.NativeMachine) (role : Role) (exit : ExitV) : Prop :=
  match role with
  | .numeric output => AnswerFlow.ExitAt (model machine.completedExits) machine.state output exit
  | _ => True

/-- An existing fiber carries its frame role, published exit, and actual interruption-only recording. -/
structure FiberAt (machine : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) : Prop where
  frame : FrameAt machine role fiber.frame
  exit : ∀ exit, fiber.exit = some exit → ExitAt machine role exit
  retired : role = .retired → fiber.exit.isSome = true
  recorded : ∀ cause, fiber.frame.interruptedCause = some cause → NoTypedFailure cause

/-- A reply has a numeric obligation precisely when its existing token still matches a live park. -/
def ReplyAt (world : World) (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) : Prop :=
  ∀ fiber, machine.fiber? id = some fiber → fiber.exit = none → fiber.parked = .withGuard token →
    ∀ role, (id, role) ∈ world.roles → FrameAt machine role {fiber.frame with current := code}

/-- Drained resume tasks retain the same actual-frame obligation as queued resume commands. -/
def TaskAt (world : World) (machine : Effect4.Program.NativeMachine) : NTask → Prop
  | .resume id token code => ReplyAt world machine id token code
  | .start _ => True
  | .wake _ _ => False

/-- A drained snapshot checks every task against the current live roles. -/
def Snapshot (world : World) (machine : Effect4.Program.NativeMachine) (tasks : List NTask) : Prop :=
  ∀ task ∈ tasks, TaskAt world machine task

/-- Value-bearing commands and cancellation countdowns retain their concrete numeric obligations. -/
def CommandAt (world : World) (machine : Effect4.Program.NativeMachine) : Guard.NCmd → Prop
  | .resume id token code => ReplyAt world machine id token code
  | .finish id exit => ∀ role, (id, role) ∈ world.roles → ExitAt machine role exit
  | .afterInterrupt host _ (.awaitAll targets) =>
      ∀ image own suffix, (host, Role.root image own suffix) ∈ world.roles → AwaitAt image own machine targets
  | .raceCancel _ host _ remaining visited =>
      ∀ image own suffix, (host, Role.root image own suffix) ∈ world.roles →
        AwaitAt image own machine (remaining ++ visited)
  | .trackChild _ _ | .closeParAwait _ _ _ | .link _ _ _ _ _ | .wake _ _ => False
  | _ => True

/-- Pending commands are checked together, so a fresh resume can use the same phase as its producer. -/
def Commands (world : World) (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd) : Prop :=
  ∀ command ∈ commands, CommandAt world machine command

/-- The concrete active configuration retains numeric heap order and every existing fiber's role. -/
structure Configuration (world : World) (machine : Effect4.Program.NativeMachine) : Prop where
  heap : machine.state.refs = world.phase.heap
  roles : ∀ fiber ∈ machine.fibers, ∃ role, (fiber.id, role) ∈ world.roles ∧ FiberAt machine role fiber
  unique : ∀ id first second, (id, first) ∈ world.roles → (id, second) ∈ world.roles → first = second
  dispatchers : ∀ fiber ∈ machine.fibers, ∀ bucket ∈ fiber.dispatcher.buckets, Snapshot world machine bucket.tasks

/-- An old-token reply needs no invented numeric class after its original park has disappeared. -/
theorem stale_reply (world : World) (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode)
    (stale : ∀ fiber, machine.fiber? id = some fiber → fiber.exit = none → fiber.parked ≠ .withGuard token) :
    ReplyAt world machine id token code := by
  intro fiber found live parked
  exact False.elim (stale fiber found live parked)

/-- An empty drained snapshot has no reply obligation. -/
theorem snapshot_nil (world : World) (machine : Effect4.Program.NativeMachine) : Snapshot world machine [] := by
  intro task member
  cases member

/-- Removing a drained task retains the remaining actual reply obligations. -/
theorem snapshot_tail (world : World) (machine : Effect4.Program.NativeMachine)
    (task : NTask) (tasks : List NTask) (held : Snapshot world machine (task :: tasks)) :
    Snapshot world machine tasks := by
  intro next member
  exact held next (List.mem_cons_of_mem task member)

/-- The unchanged original cleanup reader consumes the concrete configuration's actual phase. -/
theorem cleanup_observation (world : World) (run : Effect4.Run)
    (held : Configuration world run.machine) :
    (Test.Dogfood.Scenario.Timeout.observe run).cleanupKeeps = true :=
  world.phase.cleanup_observation run held.heap

end Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
