import Effect4.Laws.Program.Typed.State

namespace Test.Program.TypedStateRulesRed
open Effect4.Program.Typed

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  W : Type
  P : Preds W
  w : W
  e : Expect
  x : Effect4.Program.Sched.RSaved
  saved : P.SavedOk w e x
  ⊢ RSavedOk P w e x
-/
#guard_msgs (error) in
example {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RSaved)
    (saved : P.SavedOk w e x) : RSavedOk P w e x := by
  aesop

theorem from_owner {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RSaved) (saved : P.SavedOk w e x) : RSavedOk P w e x := by
  aesop (rule_sets := [Effect4.TypedState])

#print axioms from_owner
end Test.Program.TypedStateRulesRed
