import Test.Dogfood.Proofs.HostTimeoutNumberPendingFinalizer
import Test.Dogfood.Proofs.HostTimeoutNumberCountQueue

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: actual protected callback installation retains the joined numeric machine, queue, and detached tasks.
Consumer: the installed-finalizer branch of the coupled Timeout history producer for both numeric endpoints.
Reach: actual lookup, unique machine ids, the entered heap, and an unparked live pending attempt.
Limit: the source driver supplies the actual selected callback and scheduled execution permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPendingInstall
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutNumberConfigurationTransport
open HostTimeoutNumberQueueInterrupt HostTimeoutState

/-- An unparked replacement makes its old replies stale and retains every other actual reply. -/
theorem replies (world : HostTimeoutNumberConfiguration.World) (machine : NativeMachine)
    (before after : SourceScope.SourceFiber) (found : machine.fiber? before.id = some before)
    (key : after.id = before.id) (unparked : after.parked = .notParked)
    (view : (machine.update after).completedExits = machine.completedExits)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyAt world machine id token code) :
    ReplyAt world (machine.update after) id token code := by
  intro fiber selected live waiting role assigned
  by_cases same : id = before.id
  · subst id
    have self : (machine.update after).fiber? before.id = some after := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at selected
    cases selected
    rw [unparked] at waiting
    cases waiting
  · have other : id ≠ after.id := by intro equal; exact same (equal.trans key)
    rw [RunMachine.fiber?_update_other after machine id other] at selected
    exact frame_machine machine _ role _ rfl view (held fiber selected live waiting role assigned)

/-- One actual read-only native replacement retains the joined numeric machine, queue, and detached tasks.
Consumers: protected finalizer installation and ordinary running native steps. -/
theorem readonly_update (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (machine afterMachine : NativeMachine) (fiber afterFiber : SourceScope.SourceFiber)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? fiber.id = some fiber) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks)
    (finishes : ∀ exit, .finish fiber.id exit ∉ pending)
    (loopEntered : ∀ yielding, .loop fiber.id yielding ∈ pending → At context.entered machine.state)
    (state : afterMachine.state = machine.state) (fibers : afterMachine.fibers = machine.fibers)
    (completed : afterMachine.completedExits = machine.completedExits)
    (key : afterFiber.id = fiber.id) (dispatcher : afterFiber.dispatcher = fiber.dispatcher)
    (exitSame : afterFiber.exit = fiber.exit) (unparked : afterFiber.parked = .notParked)
    (provided : FiberAt afterMachine (.pending context) afterFiber) :
    Configuration world (afterMachine.update afterFiber) ∧
      Commands world (afterMachine.update afterFiber) pending ∧
      Snapshot world (afterMachine.update afterFiber) tasks := by
  have lookup : ∀ id, afterMachine.fiber? id = machine.fiber? id := by
    intro id
    change List.find? _ afterMachine.fibers = List.find? _ machine.fibers
    rw [fibers]
  have base := configuration_fields world machine afterMachine fibers state completed held
  have baseQueue := commands_fields world machine afterMachine pending state fibers completed queued
  have located : afterMachine.fiber? fiber.id = some fiber := (lookup fiber.id).symm ▸ found
  have unique : (afterMachine.fibers.map (·.id)).Nodup := fibers ▸ ids
  have viewSame := update_view afterMachine fiber afterFiber located unique key exitSame
  have reply : ∀ id token code, ReplyAt world afterMachine id token code →
      ReplyAt world (afterMachine.update afterFiber) id token code :=
    fun id token code good => replies world afterMachine fiber afterFiber located key unparked
      viewSame id token code good
  have config : Configuration world (afterMachine.update afterFiber) := by
    apply configuration_update world afterMachine fiber afterFiber located key dispatcher viewSame base
    · intro role roleAt
      have same := held.unique fiber.id role (.pending context) roleAt assigned
      rw [same]
      exact provided
    · exact reply
  have queue : Commands world (afterMachine.update afterFiber) pending := by
    intro command member
    apply command_transport world afterMachine _ pending command member (baseQueue command member) reply
    · intro id yielding member previous nextContext roleAt oldHeap after actual installedFin
      by_cases same : id = fiber.id
      · subst id
        have equal := held.unique fiber.id (.pending nextContext) (.pending context) roleAt assigned
        cases equal
        have entered : At context.entered afterMachine.state := state ▸ loopEntered yielding member
        exact False.elim (HostTimeoutNumberCountMachine.counted_heap_ne context (entered.symm.trans oldHeap))
      · have other : id ≠ afterFiber.id := by intro equal; exact same (equal.trans key)
        rw [RunMachine.fiber?_update_other afterFiber afterMachine id other] at actual
        exact previous nextContext roleAt oldHeap after actual installedFin
    · intro id selected finishMember previous
      by_cases same : id = fiber.id
      · subst id
        exact False.elim (finishes selected finishMember)
      · constructor
        · intro after actual
          have other : id ≠ afterFiber.id := by intro equal; exact same (equal.trans key)
          rw [RunMachine.fiber?_update_other afterFiber afterMachine id other] at actual
          exact previous.1 after actual
        · intro role roleAt
          exact exit_machine afterMachine _ role selected rfl viewSame (previous.2 role roleAt)
    · intro host yielding kind member previous
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
        exact ⟨fun image own suffix assigned => await_update afterMachine fiber afterFiber targets image own
          located key exitSame (previous.1 image own suffix assigned),
          fun suffix assigned => cleanup_await_update afterMachine fiber afterFiber targets
          located key exitSame (previous.2 suffix assigned)⟩
    · intro race host yielding remaining visited member previous
      exact ⟨fun image own suffix assigned => await_update afterMachine fiber afterFiber (remaining ++ visited) image own
        located key exitSame (previous.1 image own suffix assigned),
        fun suffix assigned => cleanup_await_update afterMachine fiber afterFiber (remaining ++ visited)
        located key exitSame (previous.2 suffix assigned)⟩
  exact ⟨config, queue, snapshot_replies world afterMachine _ tasks reply
    (snapshot_fields world machine afterMachine tasks fibers state completed detached)⟩

/-- The actual installed protected callback returns the full joined numeric assertions at the same world. -/
theorem joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? fiber.id = some fiber) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (live : fiber.exit = none)
    (unparked : fiber.parked = .notParked) (saved : fiber.frame.stack ≠ [])
    (heap : At context.entered machine.state) (current : fiber.frame.current = Prim.ofExit exit)
    (chosen : (fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).answer = .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
        (HostTimeoutEvaluation.exitCause exit)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    Configuration world (next.machine.update next.fiber) ∧
      Commands world (next.machine.update next.fiber) pending ∧
      Snapshot world (next.machine.update next.fiber) tasks ∧
      next.nested = [] ∧ next.edits = [] ∧ next.outcome = .continue_ := by
  let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
  have classified := held.lookup world machine fiber.id (.pending context) assigned fiber found
  obtain ⟨input, code, stack⟩ := classified.frame.2
  have owned : CodeAt machine.state input (Prim.ofExit exit) := current ▸ code
  have good := HostTimeoutNumberPhaseFinalizer.exit_class machine.state input exit owned
  obtain ⟨state, exitSame, recorded, masked⟩ := HostTimeoutNumberProtected.installed_fields view machine fiber yielding exit
    input _ body name flag program good stack classified.recorded chosen hook
  obtain ⟨fibers, completed, key, dispatcher, parked, nested, edits, outcome⟩ :=
    HostTimeoutNumberProtected.installed_metadata view machine fiber yielding exit body name flag program chosen hook
  change next.machine.state = machine.state at state
  change next.machine.fibers = machine.fibers at fibers
  change next.machine.completedExits = machine.completedExits at completed
  have provided := HostTimeoutNumberPendingFinalizer.installed context view machine fiber yielding exit body name flag program
    classified live heap current chosen hook
  obtain ⟨config, queue, snapshot⟩ := readonly_update world context machine next.machine fiber next.fiber pending tasks
    found ids assigned held queued detached
    (fun selected member => saved ((queued (.finish fiber.id selected) member).1 fiber found))
    (fun _ _ => heap) state fibers completed key dispatcher exitSame
    (parked.trans unparked) provided
  exact ⟨config, queue, snapshot, nested, edits, outcome⟩

end Test.Dogfood.Proofs.HostTimeoutNumberPendingInstall
