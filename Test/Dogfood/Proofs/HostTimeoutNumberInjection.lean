import Test.Dogfood.Proofs.HostTimeoutNumberOrdinary
import Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission

/-!
Concept: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: an actual scheduler injection retains the joined numeric machine, queue, and drained reply assertions.
Consumer: the injected iteration branch of both Timeout numeric history endpoints.
Reach: the actual current phase, source writer graph, and the consumed command owner's existing guard freshness.
Limit: subsequent native evaluation and initialized command history remain separate consumers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberInjection
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutState

/-- This abbreviation names the actual existing injection's fiber update. -/
def wrapped (fiber : SourceScope.SourceFiber) : SourceScope.SourceFiber :=
  {countOp fiber with yieldOverride := none, frame :=
    {fiber.frame with current := .onSuccessConst (.yieldNowWith 0) fiber.frame.current}}

/-- The generic source predicate closes the actual constant yield wrapper around the retained writer. -/
theorem source (context : CountContext) (frame : HostTimeoutFrames.NativeFrame)
    (held : HostTimeoutNumberSourceWrites.FrameAt context frame) :
    HostTimeoutNumberSourceWrites.FrameAt context
      {frame with current := .onSuccessConst (.yieldNowWith 0) frame.current} := by
  exact ⟨⟨⟨trivial, held.current⟩, held.saved⟩, ⟨trivial, held.currentWrites⟩, held.savedWrites,
    ⟨⟨trivial, held.actions.current⟩, held.actions.saved⟩⟩

/-- The actual paused class freezes the current heap while retaining the original incoming failure class. -/
theorem fiber (phase : HostTimeoutNumberPhase.Phase) (context : CountContext) (machine : NativeMachine)
    (row : SourceScope.SourceFiber) (held : FiberAt machine (.pending context) row)
    (heap : At phase machine.state) : FiberAt machine (.pending context) (wrapped row) := by
  constructor
  · constructor
    · exact source context row.frame held.frame.1
    · obtain ⟨input, code, path⟩ := held.frame.2
      exact ⟨input, CodeAt.pausing phase input 0 row.frame.current heap code, path⟩
  · exact held.exit
  · exact held.retired
  · exact held.recorded
  · exact held.immediate
  · exact held.pendingRunning
  · exact held.pendingCustody
  · exact held.pendingDeferred

/-- Actual owner freshness excludes another queued command for that same running fiber. -/
theorem command_absent (machine : NativeMachine) (pending : List Guard.NCmd) (id : FiberId)
    (fresh : id ∉ pending.filterMap (Guard.commandOwner machine)) (command : Guard.NCmd)
    (owner : Guard.commandOwner machine command = some id) : command ∉ pending := by
  intro member
  exact fresh (List.mem_filterMap.mpr ⟨command, member, owner⟩)

/-- Actual scheduler injection retains all three numeric assertions at one unchanged world. -/
theorem joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (machine : NativeMachine) (row : SourceScope.SourceFiber) (yielding : Bool)
    (pending : List Guard.NCmd) (tasks : List NTask) (result : HostTimeoutEvaluation.NativeIter)
    (found : machine.fiber? row.id = some row) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (row.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (unparked : row.parked = .notParked)
    (fresh : row.id ∉ pending.filterMap (Guard.commandOwner machine))
    (actual : injectYield machine (countOp row) yielding = some result) :
    Configuration world (result.machine.update result.fiber) ∧
      Commands world (result.machine.update result.fiber) pending ∧
      Snapshot world (result.machine.update result.fiber) tasks := by
  have classified := held.lookup world machine row.id (.pending context) assigned row found
  have provided := fiber world.phase context machine row classified held.heap
  unfold injectYield at actual
  split at actual
  · cases actual
    apply HostTimeoutNumberPendingInstall.readonly_update world context machine _ row _ pending tasks
      found ids assigned held queued detached
    · intro selected
      exact command_absent machine pending row.id fresh (.finish row.id selected) rfl
    · intro latch member
      exact False.elim (command_absent machine pending row.id fresh (.loop row.id latch) rfl member)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact unparked
    · exact HostTimeoutNumberConfigurationTransport.fiber_machine machine _ (.pending context)
        (wrapped row) rfl rfl provided
  · cases actual

end Test.Dogfood.Proofs.HostTimeoutNumberInjection
