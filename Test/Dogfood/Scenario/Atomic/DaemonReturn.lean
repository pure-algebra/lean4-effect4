import Test.Dogfood.Scenario.Atomic.DaemonIteration
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: store-typing R4.
Consumer: the actual daemon native transition in `Atomic.Store.shop_stages`.
The ignored daemon answers reuse the common terminal dispatcher and saved-family return proof.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Actual restoring masks retain the daemon's ignored answer and saved source suffix. -/
theorem mask_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World) (kind : Unit) :
    Edge root table world kind kind (.setInterruptible true) := by
  cases kind
  apply RecursiveFamilyEdge.saved
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro view
    exact saved_mask (model root table view) (interpAt root view table).toPrimInterp world () true
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal
  · intro body previous scope flag equal
    cases equal

/-- An actual timer cancellation retains its incoming failure through the cancellation program. -/
theorem async_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World) (name : EffName)
    (cancel : ∀ view cause, CodeAt root table ((interpAt root view table).cancelThenFail name cause)) :
    Edge root table world () () (.asyncFinalizer name) := by
  apply RecursiveFamilyEdge.saved
  refine ⟨⟨?_, ?_, ?_⟩, (by intro body previous scope flag equal; cases equal)⟩
  · intro view
    refine .mk world () () _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro after future value good absent
      exact True.intro
    · intro after future cause good absent
      cases absent
    · intro after future value provided next pushed good supplied absent arm
      cases arm
    · intro after future cause provided next pushed good supplied absent arm
      change some (if cause.hasInterrupts then (interpAt root view table).cancelThenFail name cause
        else .failure cause, []) = some (next, pushed) at arm
      cases arm
      refine .mk after () () _ [] ?_ (.nil after ())
      split
      · exact cancel view cause
      · exact .failure cause
    · intro after future exit next good program
      cases program
    · intro after future fiber cause delivered good selected interrupted skipped
      exact True.intro
  · intro loop cursor equal
    cases equal
  · intro generator cursor equal
    cases equal

/-- The actual sleep cancellation runs its stored timer cleanup and then restores the incoming cause. -/
theorem timer_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (waiter : FiberId) (token : Nat) :
    Edge root table world () () (.asyncFinalizer (.withWaiter (.store .cancelSleep) waiter token)) := by
  apply async_edge root table world _
  intro view cause
  exact .bound (.cancelClock waiter token) (fun _ _ => .failure cause)

/-- The daemon's actual administrative action preserves its heap and complete saved frame. -/
theorem action_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (thunk : EffThunk) (action : WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (held : FrameAt root table world fiber.frame) (current : fiber.frame.current = .withFiber thunk)
    (found : (interpAt root view table).withFiberOf thunk = some action) :
    let result := evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action
    result.machine.state = machine.state ∧ result.machine.fibers = machine.fibers ∧
      FrameAt root table world result.fiber.frame := by
  rcases action_shape root table thunk (current ▸ held.1) with ⟨targets, who, same⟩ | ⟨token, same⟩
  · subst thunk
    change some (.interruptAll targets who) = some action at found
    cases found
    exact ⟨rfl, rfl, held⟩
  · subst thunk
    change some (.dropObservers token) = some action at found
    cases found
    exact ⟨rfl, rfl, .success .unit, held.2⟩

/-- The daemon's actual terminal dispatcher retains its current and ordered saved suffix. -/
theorem terminal_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (held : FrameAt root table world fiber.frame) :
    FrameAt root table world
      (evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit).fiber.frame := by
  have good : ExitAt (model root table view) world () exit := by
    cases exit <;> exact True.intro
  obtain ⟨result, incoming, code, saved⟩ := External.Native.finalizer_frame
    (model root table view) (interpAt root view table) (Edge root table)
    (family root table view) (mask_edge root table) world () () machine fiber yielding exit
    current held.1 held.2 good (fun _ _ => True.intro) (fun _ _ => rfl)
  cases result
  cases incoming
  exact ⟨code, saved⟩

end Test.Dogfood.Scenario.Atomic.DaemonGraph
