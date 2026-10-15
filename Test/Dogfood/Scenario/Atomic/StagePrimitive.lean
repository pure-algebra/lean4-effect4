import Test.Dogfood.Scenario.Atomic.StageReturn
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual Atomic request actor transition in the coupled command/history invariant.
Every primitive chooses one next stage world for its heap, returned frame and actual finished exit.
The common primitive producer supplies the evaluator cases.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Request source suspensions are body thunks, and requests expose no native park, action or async registration. -/
theorem ordinary_shape (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (kind : StageWorld.Kind)
    (code : NCode) (owned : CodeAt root table owner world kind code) :
    (interpAt root view table).parkOf code = none ∧
      (∀ thunk, code ≠ .withFiber thunk) ∧
      (∀ name signal cancel, code ≠ .async name signal cancel) := by
  constructor
  · cases owned <;> rfl
  constructor
  · intro thunk equal
    cases owned <;> cases equal
  · intro name signal cancel equal
    cases owned <;> cases equal

/-- A represented request synchronous primitive is an actual store operation. -/
theorem sync_thunk (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (kind : StageWorld.Kind) (thunk : EffThunk)
    (owned : CodeAt root table owner world kind (.sync thunk)) : ∃ operation, thunk = .op operation := by
  cases owned <;> exact ⟨_, rfl⟩

/-- An actual request yield answers only its ignored current-phase class. -/
theorem yield_value (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (kind : StageWorld.Kind) (priority : Nat)
    (owned : CodeAt root table owner world kind (.yieldNowWith priority)) : ValueAt world kind .unit := by
  cases owned with
  | yielding waiting => exact waiting
  | pause owns => exact ⟨rfl, rfl⟩

/-- Every actual request primitive joins its next heap with its actual live result or completed exit. -/
theorem primitive_result (root : NativeEff) (table : RowTable) (owner : Nat) (member : owner ∈ requests)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (heap : HeapAt world machine.state)
    (recorded : Recorded fiber.frame) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    ∃ next, Future world next ∧ RequestChange world next owner ∧
      HeapAt next (evaluatePrim (interpAt root view table) machine fiber yielding).machine.state ∧
      External.Native.ResultAt (model root table owner view) (Edge root table owner) next (.finalized owner)
        (evaluatePrim (interpAt root view table) machine fiber yielding) := by
  obtain ⟨input, code, saved⟩ := held
  have ordinary := ordinary_shape root table owner view world input fiber.frame.current code
  have produced := Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt root view table) machine fiber yielding = result at produced ⊢
  cases produced with
  | step noPark noAction noSync noSuccess noFailure noYield noAsync =>
    refine ⟨world, order.refl world, request_change_refl world owner,
      StatePreservation.stepFrame (interpAt root view table) (HeapAt world) machine fiber yielding heap, ?_⟩
    apply External.Native.step_frame_result (model root table owner view) (interpAt root view table)
      (Edge root table owner) world (.finalized owner) machine fiber yielding
    have owns := path_input_owned root table owner world input (.finalized owner) fiber.frame.stack saved rfl
    rcases head_or_sync root table owner view world input fiber.frame.current code owns with head | ⟨operation, current⟩
    · apply frame_step (model root table owner view) (interpAt root view table).toPrimInterp
        (Edge root table owner) world input (.finalized owner) fiber.frame head saved
      · intro value provided supplied good
        rcases supplied with ⟨current, supplied⟩ | ⟨thunk, current, same, supplied⟩
        · exact (noSuccess value current).elim
        · exact (noSync thunk current).elim
      · intro cause current good
        exact (noFailure cause current).elim
    · exact (noSync (.op operation) current).elim
  | finalizer exit current =>
    have good : ExitAt (model root table owner view) world input exit := by
      cases exit
      all_goals rw [current] at code
      all_goals (cases code; assumption)
    exact ⟨world, order.refl world, request_change_refl world owner,
      StatePreservation.finalizerOr (interpAt root view table) (HeapAt world) machine fiber yielding exit heap,
      native_exit root table owner view world input (.finalized owner) machine fiber yielding exit
        current good saved recorded consistent⟩
  | sync thunk state value current noPark found =>
    obtain ⟨operation, rfl⟩ := sync_thunk root table owner world input thunk (current ▸ code)
    obtain ⟨next, after, answer, actual, future, change, nextHeap, good⟩ :=
      sync_heap root table owner member world input operation (current ▸ code) machine.state heap
    change syncOpStep operation machine.state = some (state, value) at found
    rw [actual] at found
    cases found
    exact ⟨next, future, change, nextHeap, input, .success good,
      saved.map (edge_future root table owner world next future)⟩
  | fallback thunk current noPark missing =>
    obtain ⟨operation, rfl⟩ := sync_thunk root table owner world input thunk (current ▸ code)
    obtain ⟨next, after, answer, actual, future, change, nextHeap, good⟩ :=
      sync_heap root table owner member world input operation (current ▸ code) machine.state heap
    change syncOpStep operation machine.state = none at missing
    rw [actual] at missing
    cases missing
  | yieldNow priority current =>
    exact ⟨world, order.refl world, request_change_refl world owner, heap, input,
      .success (yield_value root table owner world input priority (current ▸ code)), saved⟩
  | action thunk action current noPark found => exact (ordinary.2.1 thunk current).elim
  | asyncImmediate name signal cancel state next current registered => exact (ordinary.2.2 name signal cancel current).elim
  | asyncParked name signal cancel state current registered => exact (ordinary.2.2 name signal cancel current).elim
  | rejectedPark cause park | racePark race park
    | countdownPark targets next returned parked edits park counted
    | joinMissing target mode park missing | joinExited target mode other exit park found exited
    | joinWaiting target mode other park found live =>
    rw [ordinary.1] at park
    cases park
/-- Actual request native dispatch has neither scoped entry nor a scoped-exit callback. -/
theorem native_primitive_eq (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (recorded : Recorded fiber.frame) :
    evaluateNative root machine fiber yielding table =
      evaluatePrim (interpAt root machine.completedExits table) machine fiber yielding := by
  obtain ⟨input, code, saved⟩ := held
  have ordinary := ordinary_shape root table owner machine.completedExits world input fiber.frame.current code
  unfold evaluateNative
  split
  · rename_i point current
    exact (ordinary.2.1 (.act point) current).elim
  · rename_i value current
    have good : ValueAt world input value := by rw [current] at code; cases code; assumption
    have excluded (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool) :
        (fiber.frame.getCont .contA false).answer ≠ .frame (.onExit body (.scopedExit previous scope) flag) := by
      intro chosen
      obtain ⟨incoming, middle, good, edge, suffix⟩ := Contextual.Hooked.getCont_value_selected
        (model root table owner machine.completedExits) (interpAt root machine.completedExits table).toPrimInterp
        (Edge root table owner) StageFinalizer.Allowed (family root table owner machine.completedExits)
        (hook_mask root table owner) world input (.finalized owner) fiber.frame value _ good saved chosen
      exact edge_no_scoped root table owner world incoming middle _ edge body previous scope flag rfl
    unfold exitScoped
    dsimp only
    split
    · rename_i body previous scope flag chosen
      exact (excluded body previous scope flag chosen).elim
    · simp only [evaluatePrim, current]
      rfl
  · rename_i cause current
    have good : CauseAt world input cause := by rw [current] at code; cases code; assumption
    have excluded (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool) :
        (fiber.frame.getCont .contE true (some cause)).answer ≠ .frame (.onExit body (.scopedExit previous scope) flag) := by
      intro chosen
      obtain ⟨incoming, middle, delivered, carried, good, edge, suffix⟩ := Contextual.Hooked.getCont_cause_selected
        (admitted := recorded_allowed world fiber.frame recorded)
        (model root table owner machine.completedExits) (interpAt root machine.completedExits table).toPrimInterp
        (Edge root table owner) StageFinalizer.Allowed (family root table owner machine.completedExits)
        (hook_mask root table owner) world input (.finalized owner) fiber.frame cause _ good
        (recorded_absorbs root table owner machine.completedExits world fiber.frame recorded) saved chosen
      exact edge_no_scoped root table owner world incoming middle _ edge body previous scope flag rfl
    unfold exitScoped
    dsimp only
    split
    · rename_i body previous scope flag chosen
      exact (excluded body previous scope flag chosen).elim
    · simp only [evaluatePrim, current]
      rfl
  · rfl

/-- The actual native request actor returns one world for heap, live frame and published-exit permission. -/
theorem native_result (root : NativeEff) (table : RowTable) (owner : Nat) (member : owner ∈ requests)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (heap : HeapAt world machine.state)
    (recorded : Recorded fiber.frame) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    ∃ next, Future world next ∧ RequestChange world next owner ∧
      HeapAt next (evaluateNative root machine fiber yielding table).machine.state ∧
      External.Native.ResultAt (model root table owner machine.completedExits) (Edge root table owner) next (.finalized owner)
        (evaluateNative root machine fiber yielding table) := by
  rw [native_primitive_eq root table owner world machine fiber yielding held recorded]
  exact primitive_result root table owner member machine.completedExits world machine fiber yielding held heap recorded consistent

end Test.Dogfood.Scenario.Atomic.StageGraph
