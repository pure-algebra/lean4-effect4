import Test.Dogfood.Scenario.Atomic.RootNativeShape

/-!
Concept: store-typing R4.
Consumer: actual root timer and countdown native results in `Atomic.Store.shop_stages`.
Cancellation retains the root's actual answer endpoint and captured allocation counter.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Actual asynchronous cancellation retains the receiving root endpoint through every interpreter view. -/
theorem async_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (owns : Owns kind) (name : EffName)
    (cancel : ∀ after view cause, CodeAt root table after kind ((interpAt root view table).cancelThenFail name cause)) :
    Edge root table world kind kind (.asyncFinalizer name) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, owns, owns, (by intro body previous scope flag equal; cases equal)⟩
  · intro view
    refine .mk world kind kind _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro after future value good absent
      exact good
    · intro after future cause good absent
      cases absent
    · intro after future value provided next pushed good supplied absent arm
      cases arm
    · intro after future cause provided next pushed good supplied absent arm
      change some (if cause.hasInterrupts then (interpAt root view table).cancelThenFail name cause
        else .failure cause, []) = some (next, pushed) at arm
      cases arm
      refine .mk after kind kind _ [] ?_ (.nil after kind)
      split
      · exact cancel after view cause
      · exact .failure
    · intro after future exit next good program
      cases program
    · intro after future fiber cause delivered good selected interrupted skipped
      exact True.intro
  · intro loop cursor equal
    cases equal
  · intro generator cursor equal
    cases equal

/-- Actual timer cleanup runs under the saved root answer endpoint. -/
theorem timer_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (owns : Owns kind) (waiter : FiberId) (token : Nat) :
    Edge root table world kind kind (.asyncFinalizer (.withWaiter (.store .cancelSleep) waiter token)) := by
  apply async_edge root table world kind owns _
  intro after view cause
  exact .bound (input := .ordinary) True.intro (.ignored (.cancelClock waiter token)) (fun _ _ _ _ _ => .failure)

/-- Actual observer cleanup runs under the saved root answer endpoint. -/
theorem park_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (owns : Owns kind) (waiter : FiberId) (token : Nat) :
    Edge root table world kind kind (.asyncFinalizer (.withWaiter (.store .cancelPark) waiter token)) := by
  apply async_edge root table world kind owns _
  intro after view cause
  exact .bound (input := .ordinary) True.intro (.ignored (.dropObservers token)) (fun _ _ _ _ _ => .failure)

end Test.Dogfood.Scenario.Atomic.RootGraph
