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
  current : P.program w e x.current
  stack : P.StackOk w e x.stack
  interrupted : P.InterruptOnly w e x.interruptedCause
  ⊢ RSavedOk P w e x
-/
#guard_msgs (error) in
example {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RSaved)
    (current : P.program w e x.current) (stack : P.StackOk w e x.stack)
    (interrupted : P.InterruptOnly w e x.interruptedCause) : RSavedOk P w e x := by
  aesop

#print axioms Effect4.Program.Typed.saved_from_clauses
end Test.Program.TypedStateRulesRed
