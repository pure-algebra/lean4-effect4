import Test.Dogfood.Proofs.HostTimeoutNumberTerminal
import Test.Dogfood.Proofs.HostTimeoutNumberPendingInstall
import Test.Dogfood.Proofs.HostTimeoutNumberConfigurationTransport
import Effect4.Laws.Program.NativeFrameRows
import Effect4.Laws.Program.Guard.ReturnFields

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: both Timeout numeric endpoint histories retain the whole pending fiber at actual terminal native returns.
Consumer: the joined pending native command producer.
Reach: actual source frame, running authority, selected terminal current, and the same numeric role.
Limit: finished retirement and command settlement keep their separate actual outcome premises.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberTerminalFiber
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutState

/-- An actual continued terminal handoff retains every pending numeric fiber permission together. -/
theorem continued (context : CountContext) (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (held : FiberAt machine (.pending context) fiber)
    (sourceMachine : SourceScope.ConfigurationAt HostTimeoutSource.program machine)
    (sourceFiber : SourceScope.FiberAt HostTimeoutSource.program fiber)
    (running : fiber.running = true) (live : fiber.exit = none)
    (current : fiber.frame.current = Prim.ofExit exit) (clear : fiber.frame.deferredInterrupt = false)
    (continues : (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit).outcome = .continue_) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    FiberAt next.machine (.pending context) next.fiber := by
  obtain ⟨input, code, saved⟩ := held.frame.2
  have owned : CodeAt machine.state input (Prim.ofExit exit) := current ▸ code
  have good := HostTimeoutNumberPhaseFinalizer.exit_class machine.state input exit owned
  have authority : At context.entered machine.state → fiber.frame.interruptible = true → input.grade ≤ 1 := by
    intro heap unmasked
    obtain ⟨point, body, source, member⟩ := held.pendingCustody context rfl heap unmasked
    exact Effect4.Contracts.Path.grade_le_of_member Kind.grade (fun _ _ _ edge => edge.ordered)
      saved (.onExit body (.fin point) false) 1 (fun _ _ edge => edge.finalizerInput _ _ _ rfl) member
  have permission := HostTimeoutNumberReturn.native_protected view context machine fiber yielding exit input _ current
    rfl (by change context.before.count + 1 = context.entered.count; rfl) good authority saved held.recorded clear
  unfold AnswerFlow.External.Native.ResultOf at permission
  rw [continues] at permission
  obtain ⟨nextInput, nextCode, nextPath, early, deferred⟩ := permission
  have source := HostTimeoutNumberSourceWrites.finalizer_native context view machine fiber yielding exit current held.frame.1
  have lexical := (SourceScope.finalizer_at HostTimeoutSource.program HostTimeoutNumberSourceSlots.fragment
    view Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding exit sourceMachine sourceFiber).fiber.frame
  have frame : FrameAt machine (.pending context)
      (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit).fiber.frame :=
    ⟨source, nextInput, nextCode, nextPath⟩
  have footprint := Moves.finalizerOr_footprint (HostTimeoutFlow.interpreter view) machine fiber yielding exit
  have recorded := Guard.Interruption.finalizerOr_interruptedCause (HostTimeoutFlow.interpreter view) machine fiber yielding exit
  have retained : FiberAt machine (.pending context)
      (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit).fiber := by
    constructor
    · exact frame
    · intro selected published
      rw [footprint.exit, live] at published
      cases published
    · intro impossible; cases impossible
    · intro cause present
      rw [recorded] at present
      exact held.recorded cause present
    · intro cause clean alive idle interruptible
      rw [footprint.running, running] at idle
      cases idle
    · intro other same heap installed
      exact footprint.running.trans running
    · intro other same heap unmasked
      cases same
      exact FrameAt.early_installed machine context _ frame lexical nextInput nextPath (early heap unmasked)
    · intro other same masked
      exact deferred
  obtain ⟨events, emitted⟩ := NativeFrameRows.finalizer_emit (HostTimeoutFlow.interpreter view) machine fiber yielding exit
  apply HostTimeoutNumberConfigurationTransport.fiber_machine machine _ (.pending context) _ _ _ retained
  · rw [emitted]; rfl
  · rw [emitted]; rfl

/-- The actual continued terminal step installs its charged row and retains the same joined numeric world. -/
theorem joint_local (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (resident charged : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? resident.id = some resident) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (resident.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (provided : FiberAt machine (.pending context) charged)
    (sourceMachine : SourceScope.ConfigurationAt HostTimeoutSource.program machine)
    (sourceCharged : SourceScope.FiberAt HostTimeoutSource.program charged)
    (key : charged.id = resident.id) (dispatcher : charged.dispatcher = resident.dispatcher)
    (exitSame : charged.exit = resident.exit) (running : charged.running = true)
    (live : charged.exit = none) (unparked : charged.parked = .notParked)
    (finishes : ∀ exit, .finish resident.id exit ∉ pending)
    (loopEntered : ∀ latch, .loop resident.id latch ∈ pending → At context.entered machine.state)
    (current : charged.frame.current = Prim.ofExit exit) (clear : charged.frame.deferredInterrupt = false)
    (continues : (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding exit).outcome = .continue_) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding exit
    Configuration world (next.machine.update next.fiber) ∧
      Commands world (next.machine.update next.fiber) pending ∧
      Snapshot world (next.machine.update next.fiber) tasks ∧
      next.nested = [] ∧ next.edits = [] ∧ next.outcome = .continue_ := by
  have retained := continued context view machine charged yielding exit provided sourceMachine sourceCharged
    running live current clear continues
  obtain ⟨events, frame, outcome, actual⟩ := NativeFrameRows.finalizer_frame_only
    (HostTimeoutFlow.interpreter view) machine charged yielding exit
  obtain ⟨config, queue, snapshot⟩ := HostTimeoutNumberPendingInstall.readonly_update world context machine
    (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding exit).machine
    resident (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding exit).fiber pending tasks
    found ids assigned held queued detached finishes loopEntered
    (by rw [actual]; rfl) (by rw [actual]; rfl) (by rw [actual]; rfl)
    (by rw [actual]; exact key) (by rw [actual]; exact dispatcher)
    (by rw [actual]; exact exitSame) (by rw [actual]; exact unparked) retained
  refine ⟨config, queue, snapshot, ?_, ?_, continues⟩
  · rw [actual]
  · rw [actual]

end Test.Dogfood.Proofs.HostTimeoutNumberTerminalFiber
