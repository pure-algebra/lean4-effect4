import Test.Dogfood.Scenario.SourceOpportunity
open Effect4 Effect4.Program Effect4.Machine Effect4.Laws.Auto
open Effect4.Program.SourceScope.Opportunities

-- A synthetic source callback is excluded from the actual native Async producer family.
example : ¬ SourceScope.AsyncCancelAt (.cont (rootPoint 1)) := by
  intro held
  cases held

-- The stale Async current and a newly pushed callback would count the same source twice.
-- This finite projection reader is outside the checked native source configurations.
example (root : NativeEff) :
    frame root [1] {FrameFiber.start (.async .abort true (some (.cont (rootPoint 1)))) with
      stack := []} = 1 ∧
    frame root [1] {FrameFiber.start (.async .abort true (some (.cont (rootPoint 1)))) with
      stack := [.asyncFinalizer (.withWaiter (.cont (rootPoint 1)) ⟨0⟩ 0)]} = 2 := by
  constructor <;> kernel_rfl
