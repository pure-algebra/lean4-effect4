import Effect4.Laws.Program.EvaluateR
import Lean

/-! Actual dependent answer carriers and a raw protocol marker's machine behavior.
This is a focused check at the review base, not an implementation of answer_gate. -/
set_option autoImplicit false
namespace FoundationsReview.AnswerShape
open Effect4 Effect4.Program Effect4.Machine Effect4.Program.Sched

theorem forkScoped_answer (p : Point) (options : Supervision.ForkOptions) :
    (FiberOp.forkScoped p options).answer = ExitV := rfl
theorem fork_answer (body : Body) (options : Supervision.ForkOptions) :
    (FiberOp.fork body options).answer = Val := rfl
theorem guard_answer (kind : GuardKind) : (FiberOp.guard_ kind).answer = Option ExitV := rfl
theorem construction_answer : FiberOp.construction.answer = List (FiberId × ExitV) := rfl
theorem raceRegister_answer (race : Nat) : (FiberOp.raceRegister race).answer = ExitV := rfl
theorem frontier_answer (reason : PendingReason) (p : Point) :
    (FiberOp.frontier reason p).answer = ExitV := rfl

theorem raw_scopeExit_badShape (interp : RInterp) (m : RState) (f : RFiber)
    (yielding : Bool) (previous : Ctx) (scope : Nat) (ex : ExitV)
    (next : ExitV → RProgram) :
    (evaluateFiberR interp m f yielding (.scopeExit previous scope ex) next).fiber.frame.current =
      .pure Effect4.Program.Denote.badShapeExit := rfl

#print axioms raw_scopeExit_badShape
#print axioms forkScoped_answer
#print axioms fork_answer
#print axioms guard_answer
#print axioms construction_answer
#print axioms raceRegister_answer
#print axioms frontier_answer
end FoundationsReview.AnswerShape

open Lean Elab Command in
run_cmd do
  for name in [``Effect4.Machine.SyncOp, ``Effect4.Program.Sched.FiberOp] do
    let .inductInfo info ← getConstInfo name | throwError "expected an inductive"
    logInfo m!"{name}: {info.ctors.length} constructors"
    for ctor in info.ctors do
      logInfo m!"  {ctor}"
