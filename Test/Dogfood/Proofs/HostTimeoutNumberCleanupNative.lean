import Test.Dogfood.Proofs.HostTimeoutNumberCleanupAuthority

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Consumer: the actual cleanup-head branch of the full coupled Timeout native producer.
The same configuration, saved numeric owner, and actual source leaf supply the missing heap and mask permissions.
The existing cleanup evaluator equation and joined writer producer retain one next machine, queue, and detached snapshot.
Reach: the real resident owner and its charged actor, with the same saved stack and dispatcher.
This local producer establishes neither initialization nor complete application history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberCleanupNative
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutNumberPhase HostTimeoutNumberCallbacks
open HostTimeoutNumberCleanupJoint HostTimeoutState

/-- Actual numeric cleanup consumes its phase-derived runtime authority and retains the joined native result. -/
theorem joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine) (resident charged : SourceScope.SourceFiber)
    (yielding : Bool) (phase : Phase) (phaseOwn : phase.count = phase.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (census : HostTimeoutNumberPassive.OnlyAttempt world resident.id context)
    (found : machine.fiber? resident.id = some resident) (assigned : (resident.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (provided : FiberAt machine (.pending context) charged)
    (key : charged.id = resident.id) (dispatcher : charged.dispatcher = resident.dispatcher)
    (stack : charged.frame.stack = resident.frame.stack) (live : charged.exit = none)
    (unparked : charged.parked = .notParked) (heap : At phase machine.state)
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (phase.cleanup phaseOwn (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.attempt context.before context.entered (own context)) charged.frame.stack)
    (current : charged.frame.current = resolve HostTimeoutSource.program
      (({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1
        (.nat phase.count)).child 0)) :
    let next := evaluateNative HostTimeoutSource.program machine charged yielding Test.Dogfood.Scenario.Timeout.fetch.table
    Configuration {world with phase := cleaned context selected} (next.machine.update next.fiber) ∧
      Commands {world with phase := cleaned context selected} (next.machine.update next.fiber) pending ∧
      Snapshot {world with phase := cleaned context selected} (next.machine.update next.fiber) tasks ∧
      next.nested = [.drainDue] ∧ next.edits = [] ∧ next.outcome = .answered := by
  have selectedRole : (charged.id, Role.pending context) ∈ world.roles := by rw [key]; exact assigned
  obtain ⟨counted, masked, clear⟩ := HostTimeoutNumberCleanupAuthority.permission world context machine charged phase phaseOwn
    (HostTimeoutNumberSteps.interruptionFlag selected) selectedRole held provided heap saved
  have same := Phase.cleanup_heap_congr phase context.entered phaseOwn (own context)
    (HostTimeoutNumberSteps.interruptionFlag selected) (heap.symm.trans counted)
  have actual := (native_cleanup view machine charged yielding phase phaseOwn captured fuel delay n previous selected heap _ current
    (HostTimeoutNumberUniform.path view machine.state _ _ charged.frame.stack saved)).1
  rw [same] at actual
  have nonempty : resident.frame.stack ≠ [] := by
    intro empty
    have absent := stack.trans empty
    rw [absent] at saved
    cases saved
  obtain ⟨config, queue, snapshot⟩ := joint_local_value world context machine resident charged selected _ pending tasks
    census found assigned held queued detached provided key dispatcher live unparked masked counted nonempty saved ⟨same.symm, rfl⟩
  dsimp only
  rw [actual]
  exact ⟨config, queue, snapshot, rfl, rfl, rfl⟩

end Test.Dogfood.Proofs.HostTimeoutNumberCleanupNative
