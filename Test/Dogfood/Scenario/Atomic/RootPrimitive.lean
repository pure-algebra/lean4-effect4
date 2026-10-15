import Test.Dogfood.Scenario.Atomic.RootActionResult
import Test.Dogfood.Scenario.Atomic.RootParks
import Effect4.Laws.Program.NativeFrameRows
import Effect4.Laws.Program.PrimitiveCounter

/-!
Concept: store-typing R4.
Consumer: the root branch of the actual Atomic active command invariant.
One actual primitive result joins the chosen world, heap, parent and nonroot rows.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- A live root frame supplies its actual result permission; the root ignores its completed exit. -/
theorem result_of_frame (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (result : Moves.NIteration)
    (held : FrameAt root table world result.fiber.frame) :
    External.Native.ResultAt (model root table view) (Edge root table) world .ordinary result := by
  unfold External.Native.ResultAt
  cases actual : result.outcome with
  | finished exit => cases exit <;> exact True.intro
  | _ => exact held

/-- Every actual root primitive joins its actor, allocation counter, heap and stored child roles. -/
theorem primitive_result_with_after (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (fresh : Fresh world)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId) (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluatePrim (interpAt built.program view built.table) machine fiber yielding
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧
      External.Native.ResultAt (model built.program built.table view) (Edge built.program built.table) next .ordinary result ∧
      AfterResult built.program built.table next result ∧
      ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row := by
  obtain ⟨input, code, saved⟩ := held
  have owns := path_owned built.program built.table world input .ordinary fiber.frame.stack saved True.intro
  have produced := Moves.evaluatePrim_producer (interpAt built.program view built.table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt built.program view built.table) machine fiber yielding = result at produced ⊢
  dsimp only
  cases produced with
  | step noPark noAction noSync noSuccess noFailure noYield noAsync =>
    refine ⟨world, order.refl world, fresh, (Moves.stepFrame_nextId _ _ _ _).trans counter,
      StatePreservation.stepFrame _ (HeapAt world) machine fiber yielding heap, ?_, AfterResult.of_quiet _ _ _ _ (Moves.stepFrame_effects _ _ _ _), ?_⟩
    · exact result_of_frame built.program built.table view world _
        (step_frame built accepted world view machine fiber yielding ⟨input, code, saved⟩ noSuccess noFailure noSync)
    · rw [NativeFrameRows.step_rows]
      exact rows
  | finalizer exit current =>
    have good : ExitAt (model built.program built.table view) world input exit := by
      cases exit with
      | failure cause => exact True.intro
      | success value =>
        have typed := head built accepted world input fiber.frame.current code owns view
        rw [current] at typed
        cases typed
        assumption
    refine ⟨world, order.refl world, fresh, (Moves.finalizerOr_nextId _ _ _ _ _).trans counter,
      StatePreservation.finalizerOr _ (HeapAt world) machine fiber yielding exit heap,
      native_exit built.program built.table view world input machine fiber yielding exit current good saved, AfterResult.of_quiet _ _ _ _ (Moves.finalizerOr_effects _ _ _ _ _), ?_⟩
    rw [NativeFrameRows.finalizer_rows]
    exact rows
  | action thunk action current noPark found =>
    obtain ⟨next, future, freshNext, nextCounter, heapNext, actor, others, state⟩ :=
      action_result built accepted view world fresh machine fiber yielding input thunk action (current ▸ code)
        current heap counter saved found Other rows
    exact ⟨next, future, freshNext, nextCounter, heapNext,
      result_of_frame built.program built.table view next _ actor, state.2.2, others⟩
  | sync thunk state value current noPark found =>
    change (interpOf built.program built.table).syncState thunk machine.state = some (state, value) at found
    obtain ⟨nextHeap, good⟩ := sync_heap built accepted world input thunk machine.state (current ▸ code) heap state value found
    exact ⟨world, order.refl world, fresh, counter, nextHeap, ⟨input, .success good, saved⟩, AfterResult.of_quiet _ _ _ _ ⟨rfl, fun command member => List.mem_singleton.mp member⟩, rows⟩
  | fallback thunk current noPark missing =>
    have typed := head built accepted world input fiber.frame.current code owns view
    rw [current] at typed
    cases typed with
    | sync chosen good =>
      exact ⟨world, order.refl world, fresh, counter, heap, ⟨input, .success good, saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩
  | yieldNow priority current =>
    exact ⟨world, order.refl world, fresh, counter, heap, ⟨input,
      .success (yield_value built accepted world input priority (current ▸ code)), saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩
  | asyncImmediate name signal cancel state next current registered =>
    obtain ⟨millis, rfl, rfl, rfl, owned, ignored⟩ := async_shape built accepted world input name signal cancel (current ▸ code)
    cases registered
  | asyncParked name signal cancel state current registered =>
    obtain ⟨millis, rfl, rfl, rfl, owned, ignored⟩ := async_shape built accepted world input name signal cancel (current ▸ code)
    change ({machine.state with timers := machine.state.timers.sleep fiber.id machine.nextToken millis}, none) = (state, none) at registered
    cases registered
    exact ⟨world, order.refl world, fresh, counter, ⟨heap.witness⟩, ⟨input, code,
      .cons (timer_edge built.program built.table world input owns fiber.id machine.nextToken) saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩
  | rejectedPark cause park =>
    obtain ⟨shape, owned, ignored⟩ := park_shape built accepted world view input _ code _ park
    rcases shape with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
    all_goals cases wrong
  | racePark race park =>
    obtain ⟨shape, owned, ignored⟩ := park_shape built accepted world view input _ code _ park
    rcases shape with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
    all_goals cases wrong
  | countdownPark targets next returned parked edits park counted =>
    obtain ⟨shape, owned, ignored⟩ := park_shape built accepted world view input _ code _ park
    have frame := SourceScope.countdown_path (model built.program built.table view) (Edge built.program built.table)
      built.program view built.table world input .ordinary machine fiber targets .exitsValue false code saved
      (fun _ => .success (ignored _)) (park_edge built.program built.table world input owns fiber.id machine.nextToken)
    have state := StatePreservation.countdown_plan_state (interpAt built.program view built.table) machine fiber targets .exitsValue false
    have fields : (countdownParkEdits (interpAt built.program view built.table) machine fiber targets .exitsValue false).1.fibers = machine.fibers ∧
        (countdownParkEdits (interpAt built.program view built.table) machine fiber targets .exitsValue false).1.nextId = machine.nextId := by
      unfold countdownParkEdits
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    rw [counted] at frame state fields
    have nextHeap : HeapAt world next.state := by rw [state]; exact heap
    have nextRows : ∀ row ∈ next.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row := by rw [fields.1]; exact rows
    cases parked <;> exact ⟨world, order.refl world, fresh, fields.2.trans counter, nextHeap,
      ⟨input, frame.1, frame.2⟩, AfterResult.of_empty _ _ _ _ rfl, nextRows⟩
  | joinMissing target mode park missing =>
    exact ⟨world, order.refl world, fresh, counter, heap, ⟨input, code, saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩
  | joinExited target mode other exit park found exited =>
    obtain ⟨shape, owned, ignored⟩ := park_shape built accepted world view input _ code _ park
    refine ⟨world, order.refl world, fresh, counter, heap, ⟨input, ?_, saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩
    cases mode with
    | awaitValue => exact .success (ignored _)
    | joinEffect => cases exit with
      | success value => exact .success (ignored value)
      | failure cause => exact .failure
  | joinWaiting target mode other park found live =>
    exact ⟨world, order.refl world, fresh, counter, heap, ⟨input, code,
      .cons (park_edge built.program built.table world input owns fiber.id machine.nextToken) saved⟩, AfterResult.of_empty _ _ _ _ rfl, rows⟩


/-- The original result interface projects the same selected world and actor. -/
theorem primitive_result (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (fresh : Fresh world)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId) (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluatePrim (interpAt built.program view built.table) machine fiber yielding
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧
      External.Native.ResultAt (model built.program built.table view) (Edge built.program built.table) next .ordinary result ∧
      ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row := by
  obtain ⟨next, future, freshNext, nextCounter, heapNext, actor, recipients, others⟩ :=
    primitive_result_with_after built accepted view world fresh machine fiber yielding held heap counter Other rows
  exact ⟨next, future, freshNext, nextCounter, heapNext, actor, others⟩

/-- Actual root native dispatch excludes source scopes and selected scoped-exit frames. -/
theorem native_primitive_eq (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) :
    evaluateNative built.program machine fiber yielding built.table =
      evaluatePrim (interpAt built.program machine.completedExits built.table) machine fiber yielding := by
  obtain ⟨input, code, saved⟩ := held
  apply evaluateNative_primitive built.program built.table machine fiber yielding
  · intro point current body
    exact action_not_scoped built accepted world input point (current ▸ code) body
  · intro value current body previous scope flag chosen
    have typed := head built accepted world input fiber.frame.current code
      (path_owned built.program built.table world input .ordinary fiber.frame.stack saved True.intro) machine.completedExits
    rw [current] at typed
    have good : ValueAt world input value := by cases typed; assumption
    obtain ⟨incoming, middle, good, edge, suffix⟩ := Contextual.Hooked.getCont_value_selected
      (model built.program built.table machine.completedExits) (interpAt built.program machine.completedExits built.table).toPrimInterp
      (Edge built.program built.table) (fun _ _ => True)
      (SavedFamily.contextual _ _ _ _ (family built.program built.table machine.completedExits))
      (hook_mask built.program built.table) world input .ordinary fiber.frame value _ good saved chosen
    exact edge_no_scoped built.program built.table world incoming middle _ edge body previous scope flag rfl
  · intro cause current body previous scope flag chosen
    obtain ⟨incoming, middle, delivered, carried, good, edge, suffix⟩ := Contextual.Hooked.getCont_cause_selected
      (model built.program built.table machine.completedExits) (interpAt built.program machine.completedExits built.table).toPrimInterp
      (Edge built.program built.table) (fun _ _ => True)
      (SavedFamily.contextual _ _ _ _ (family built.program built.table machine.completedExits))
      (hook_mask built.program built.table) world input .ordinary fiber.frame cause _ True.intro
      (fun _ _ _ _ _ => True.intro) saved chosen
    exact edge_no_scoped built.program built.table world incoming middle _ edge body previous scope flag rfl

/-- The actual root native result retains one world for its heap, parent and all child roles. -/
theorem native_result_with_after (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId) (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluateNative built.program machine fiber yielding built.table
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧
      External.Native.ResultAt (model built.program built.table machine.completedExits) (Edge built.program built.table) next .ordinary result ∧
      AfterResult built.program built.table next result ∧
      ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row := by
  rw [native_primitive_eq built accepted world machine fiber yielding held]
  exact primitive_result_with_after built accepted machine.completedExits world fresh machine fiber yielding held heap counter Other rows

theorem native_result (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId) (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    let result := evaluateNative built.program machine fiber yielding built.table
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧
      External.Native.ResultAt (model built.program built.table machine.completedExits) (Edge built.program built.table) next .ordinary result ∧
      ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row := by
  rw [native_primitive_eq built accepted world machine fiber yielding held]
  exact primitive_result built accepted machine.completedExits world fresh machine fiber yielding held heap counter Other rows

/-- Actual root yield injection keeps its current root endpoint and saved source suffix. -/
theorem injected_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt root table world frame) :
    FrameAt root table world {frame with current := .onSuccessConst (.yieldNowWith 0) frame.current} := by
  obtain ⟨input, code, saved⟩ := held
  exact ⟨input, .pausing (path_owned root table world input .ordinary frame.stack saved True.intro) code, saved⟩

/-- Actual charged root iteration retains all numeric and source-role facts at the same next world. -/
theorem iteration_result (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt built.program built.table world fiber.frame) (heap : HeapAt world machine.state)
    (counter : machine.nextId = world.nextId) (Other : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, row.id ≠ ⟨0⟩ →
      StageRoles.FrameAt built.program built.table world row.id row.frame ∨ Other row) :
    letI := evaluatorFor built.program built.table
    let result := iteration (interpOf built.program built.table) machine fiber yielding
    ∃ next, Future world next ∧ Fresh next ∧ result.machine.nextId = next.nextId ∧
      HeapAt next result.machine.state ∧
      External.Native.ResultAt (model built.program built.table machine.completedExits) (Edge built.program built.table) next .ordinary result ∧
      ∀ row ∈ result.machine.fibers, row.id ≠ ⟨0⟩ →
        StageRoles.FrameAt built.program built.table next row.id row.frame ∨ Other row := by
  letI := evaluatorFor built.program built.table
  have top := loop_top built.program built.table world fiber held
  unfold iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact native_result built accepted world fresh
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true (injected_frame built.program built.table world _ top) heap counter Other rows
    · cases injected
  · exact native_result built accepted world fresh machine (countOp (runloopTop fiber)) yielding top heap counter Other rows

end Test.Dogfood.Scenario.Atomic.RootGraph
