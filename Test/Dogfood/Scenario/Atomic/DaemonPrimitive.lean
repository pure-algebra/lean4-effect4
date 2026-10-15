import Effect4.Laws.Program.NativePrimitiveDefault
import Test.Dogfood.Scenario.Atomic.DaemonReturn
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: store-typing R4.
Consumer: the daemon actor of the actual Atomic stage command invariant.
The common primitive producer joins each real timer, refill, park and administrative result.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Every actual daemon primitive retains the same stage world and a complete live frame. -/
theorem primitive_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : FrameAt root table world fiber.frame) (heap : HeapAt world machine.state) :
    let result := evaluatePrim (interpAt root view table) machine fiber yielding
    HeapAt world result.machine.state ∧ FrameAt root table world result.fiber.frame := by
  have produced := Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt root view table) machine fiber yielding = result at produced ⊢
  dsimp only
  cases produced with
  | step noPark noAction noSync noSuccess noFailure noYield noAsync =>
    exact ⟨StatePreservation.stepFrame (interpAt root view table) (HeapAt world) machine fiber yielding heap,
      step_frame root table world view machine fiber yielding held noSuccess noFailure noSync⟩
  | finalizer exit current =>
    exact ⟨StatePreservation.finalizerOr (interpAt root view table) (HeapAt world) machine fiber yielding exit heap,
      terminal_frame root table world view machine fiber yielding exit current held⟩
  | action thunk action current noPark found =>
    have fields := action_frame root table world view machine fiber yielding thunk action held current found
    exact ⟨(by rw [fields.1]; exact heap), fields.2.2⟩
  | sync thunk state value current noPark found =>
    obtain ⟨after, answer, sync, nextHeap⟩ := sync_heap root table world machine.state thunk (current ▸ held.1) heap
    change (interpOf root table).syncState thunk machine.state = some (state, value) at found
    rw [sync] at found
    cases found
    exact ⟨nextHeap, .success _, held.2⟩
  | fallback thunk current noPark missing =>
    obtain ⟨after, answer, sync, nextHeap⟩ := sync_heap root table world machine.state thunk (current ▸ held.1) heap
    change (interpOf root table).syncState thunk machine.state = none at missing
    rw [sync] at missing
    cases missing
  | yieldNow priority current => exact ⟨heap, .success .unit, held.2⟩
  | asyncImmediate name signal cancel state next current registered =>
    obtain ⟨rfl, rfl, rfl⟩ := async_shape root table name signal cancel (current ▸ held.1)
    cases registered
  | asyncParked name signal cancel state current registered =>
    obtain ⟨rfl, rfl, rfl⟩ := async_shape root table name signal cancel (current ▸ held.1)
    change ({machine.state with timers := machine.state.timers.sleep fiber.id machine.nextToken 1000}, none) =
      (state, none) at registered
    cases registered
    exact ⟨⟨heap.witness⟩, held.1, .cons (timer_edge root table world fiber.id machine.nextToken) held.2⟩
  | rejectedPark cause park =>
    rcases park_shape root table view _ held.1 _ park with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
    all_goals cases wrong
  | racePark race park =>
    rcases park_shape root table view _ held.1 _ park with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
    all_goals cases wrong
  | countdownPark targets next returned parked edits park counted =>
    have frame := countdown_frame root table world view machine fiber targets held
    have state := StatePreservation.countdown_plan_state (interpAt root view table) machine fiber targets .exitsValue false
    rw [counted] at frame state
    exact ⟨(by rw [state]; exact heap), frame⟩
  | joinMissing target mode park missing => exact ⟨heap, held⟩
  | joinExited target mode other exit park found exited =>
    refine ⟨heap, ?_⟩
    cases mode with
    | awaitValue => exact ⟨.success _, held.2⟩
    | joinEffect => cases exit with
      | success value => exact ⟨.success value, held.2⟩
      | failure cause => exact ⟨.failure cause, held.2⟩
  | joinWaiting target mode other park found live =>
    exact ⟨heap, held.1, .cons (park_edge root table world fiber.id machine.nextToken) held.2⟩

/-- Actual daemon native dispatch has neither a scoped source entry nor a scoped saved exit. -/
theorem native_primitive_eq (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame) :
    evaluateNative root machine fiber yielding table =
      evaluatePrim (interpAt root machine.completedExits table) machine fiber yielding := by
  apply evaluateNative_primitive root table machine fiber yielding
  · intro point current body found
    rcases action_shape root table (.act point) (current ▸ held.1) with ⟨targets, who, wrong⟩ | ⟨token, wrong⟩
    all_goals cases wrong
  · intro value current body previous scope flag chosen
    obtain ⟨incoming, middle, good, edge, suffix⟩ := External.getCont_value_selected
      (model root table machine.completedExits) (interpAt root machine.completedExits table).toPrimInterp
      (Edge root table) (family root table machine.completedExits) (mask_edge root table)
      world () () fiber.frame value _ True.intro held.2 chosen
    exact edge_no_scoped root table world incoming middle _ edge body previous scope flag rfl
  · intro cause current body previous scope flag chosen
    obtain ⟨incoming, middle, delivered, carried, good, edge, suffix⟩ := External.getCont_cause_selected
      (model root table machine.completedExits) (interpAt root machine.completedExits table).toPrimInterp
      (Edge root table) (family root table machine.completedExits) (mask_edge root table)
      world () () fiber.frame cause _ True.intro (fun _ _ _ _ _ => True.intro) held.2 chosen
    exact edge_no_scoped root table world incoming middle _ edge body previous scope flag rfl

/-- The actual daemon native actor joins its unchanged stage world, heap and saved frame. -/
theorem native_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame) (heap : HeapAt world machine.state) :
    HeapAt world (evaluateNative root machine fiber yielding table).machine.state ∧
      FrameAt root table world (evaluateNative root machine fiber yielding table).fiber.frame := by
  rw [native_primitive_eq root table world machine fiber yielding held]
  exact primitive_frame root table world machine.completedExits machine fiber yielding held heap

/-- Actual charged daemon iteration retains the same shop world, including an injected scheduler yield. -/
theorem iteration_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame) (heap : HeapAt world machine.state) :
    letI := evaluatorFor root table
    HeapAt world (iteration (interpOf root table) machine fiber yielding).machine.state ∧
      FrameAt root table world (iteration (interpOf root table) machine fiber yielding).fiber.frame := by
  letI := evaluatorFor root table
  have top := loop_top root table world fiber held
  unfold iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact native_frame root table world
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true ⟨injected_code root table _ top.1, top.2⟩ heap
    · cases injected
  · exact native_frame root table world machine (countOp (runloopTop fiber)) yielding top heap

end Test.Dogfood.Scenario.Atomic.DaemonGraph
