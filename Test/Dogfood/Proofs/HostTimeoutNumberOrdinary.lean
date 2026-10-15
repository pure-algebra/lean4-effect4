import Test.Dogfood.Proofs.HostTimeoutNumberPendingInstall
import Effect4.Laws.Program.Guard.ReturnFields

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: an actual ordinary running attempt retains every numeric fiber permission.
Consumer: the ordinary native branch of both Timeout numeric history endpoints.
Reach: actual Guard running authority, the entered heap, exact selected-writer graph, and existing saved path.
Limit: native installation, loop-top deferred interruption, and genuine parking keep their separate producers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberOrdinary
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutState

/-- The existing shared source head retains the stronger selected-writer annotation at the actual running frame. -/
theorem source_step (context : CountContext) (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (frame : HostTimeoutFrames.NativeFrame)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (held : HostTimeoutNumberSourceWrites.FrameAt context fiber.frame)
    (actual : fiber.frame.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running frame, events))
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    HostTimeoutNumberSourceWrites.FrameAt context frame := by
  let edge := CodeClosure.Qualified.prefixEdge (HostTimeoutNumberSourceSlots.At context)
    (AnswerSlots.Prefix (HostTimeoutNumberSourceSlots.bindings context)) (HostTimeoutNumberSourceWrites.Writes context)
  have head := CodeClosure.Qualified.prefix_head HostTimeoutSource.program HostTimeoutNumberSourceSlots.fragment
    (HostTimeoutNumberSourceSlots.At context) (AnswerSlots.Prefix (HostTimeoutNumberSourceSlots.bindings context))
    (HostTimeoutNumberSourceWrites.Writes context) (HostTimeoutNumberSourceWrites.contract context)
    (fun p held view => HostTimeoutNumberSourceSlots.completed context p view held)
    Test.Dogfood.Scenario.Timeout.fetch.table view fiber.frame.current held.currentWrites
  have path := CodeClosure.Qualified.prefix_path (HostTimeoutNumberSourceSlots.At context)
    (AnswerSlots.Prefix (HostTimeoutNumberSourceSlots.bindings context)) (HostTimeoutNumberSourceWrites.Writes context)
    fiber.frame.stack held.savedWrites
  have moved := AnswerFlow.frame_step ((HostTimeoutNumberSourceWrites.sourceSpec context).model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp edge () () () fiber.frame head path
    (by
      intro value provided current good
      rcases current with ⟨current, supplied⟩ | ⟨thunk, current, equal, supplied⟩
      · exact (noSuccess value current).elim
      · exact (noSync thunk current).elim)
    (by intro cause current good; exact (noFailure cause current).elim)
  rw [actual] at moved
  obtain ⟨input, code, saved⟩ := moved
  cases input
  have broad := HostTimeoutNumberSourceSlots.step_frame context view machine fiber yielding held.toFrameAt
    noSuccess noFailure noSync
  simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame] at broad
  exact ⟨broad, code, CodeClosure.Qualified.prefix_path_owned (HostTimeoutNumberSourceSlots.At context)
    (AnswerSlots.Prefix (HostTimeoutNumberSourceSlots.bindings context)) (HostTimeoutNumberSourceWrites.Writes context) saved⟩

/-- Actual running authority makes immediate interruption vacuous while the ordinary step retains authored finalizer custody. -/
theorem fiber (context : CountContext) (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (row : SourceScope.SourceFiber) (yielding : Bool)
    (held : FiberAt machine (.pending context) row) (running : row.running = true)
    (live : row.exit = none) (heap : At context.entered machine.state)
    (noSuccess : ∀ value, row.frame.current ≠ .success value)
    (noFailure : ∀ cause, row.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, row.frame.current ≠ .sync thunk)
    (ordinary : ∀ thunk, row.frame.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    let next := evaluatePrim.stepFrame (HostTimeoutFlow.interpreter view) machine row yielding
    FiberAt next.machine (.pending context) next.fiber := by
  obtain ⟨frame, events, actual, typed⟩ := HostTimeoutNumberPhaseHead.ordinary_running_over
    HostTimeoutNumberUniform.Edge HostTimeoutNumberUniform.head_edges view machine.state _ row.frame held.frame.2
    noSuccess noFailure noSync ordinary
  have source := source_step context view machine row yielding frame events held.frame.1 actual noSuccess noFailure noSync
  have shape := FrameFiber.step_nonresume_fields (HostTimeoutFlow.interpreter view).toPrimInterp row.frame frame
    (congrArg Prod.fst actual) noSuccess noFailure noSync
  have deferred := FrameFiber.step_nonresume_deferred (HostTimeoutFlow.interpreter view).toPrimInterp row.frame frame
    (congrArg Prod.fst actual) noSuccess noFailure noSync
  have recorded := Guard.Interruption.frame_step_interruptedCause (HostTimeoutFlow.interpreter view).toPrimInterp
    row.frame frame (congrArg Prod.fst actual)
  simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame]
  constructor
  · exact ⟨source, typed⟩
  · intro selected published
    rw [live] at published
    cases published
  · intro impossible; cases impossible
  · intro cause present
    rw [recorded] at present
    exact held.recorded cause present
  · intro cause clean alive idle interruptible
    change row.running = false at idle
    rw [running] at idle
    cases idle
  · intro next same before installed
    cases same
    exact False.elim (HostTimeoutNumberCountMachine.counted_heap_ne context (heap.symm.trans before))
  · intro next same entered interruptible
    cases same
    exact shape.2.subset (held.pendingCustody context rfl heap (shape.1.symm.trans interruptible))

  · intro next same masked
    rw [deferred]
    exact held.pendingDeferred next same (shape.1.symm.trans masked)

/-- The actual ordinary running native step retains the same joined numeric world. -/
theorem joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine) (row : SourceScope.SourceFiber)
    (yielding : Bool) (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? row.id = some row) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (row.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (running : row.running = true)
    (live : row.exit = none) (unparked : row.parked = .notParked)
    (saved : row.frame.stack ≠ []) (heap : At context.entered machine.state)
    (noSuccess : ∀ value, row.frame.current ≠ .success value)
    (noFailure : ∀ cause, row.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, row.frame.current ≠ .sync thunk)
    (ordinary : ∀ thunk, row.frame.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    let next := evaluatePrim.stepFrame (HostTimeoutFlow.interpreter view) machine row yielding
    Configuration world (next.machine.update next.fiber) ∧
      Commands world (next.machine.update next.fiber) pending ∧
      Snapshot world (next.machine.update next.fiber) tasks ∧
      next.nested = [] ∧ next.edits = [] ∧ next.outcome = .continue_ := by
  have classified := held.lookup world machine row.id (.pending context) assigned row found
  obtain ⟨frame, events, actual, _typed⟩ := HostTimeoutNumberPhaseHead.ordinary_running_over
    HostTimeoutNumberUniform.Edge HostTimeoutNumberUniform.head_edges view machine.state _ row.frame classified.frame.2
    noSuccess noFailure noSync ordinary
  have provided := fiber context view machine row yielding classified running live heap
    noSuccess noFailure noSync ordinary
  simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame] at provided ⊢
  obtain ⟨config, queue, snapshot⟩ := HostTimeoutNumberPendingInstall.readonly_update world context machine
    (machine.emit (events.map (RunEvent.frame row.id))) row {row with frame := frame} pending tasks
    found ids assigned held queued detached
    (fun selected member => saved ((queued (.finish row.id selected) member).1 row found))
    (fun _ _ => heap) rfl rfl rfl rfl rfl rfl unparked provided
  exact ⟨config, queue, snapshot, True.intro, True.intro, True.intro⟩

end Test.Dogfood.Proofs.HostTimeoutNumberOrdinary
