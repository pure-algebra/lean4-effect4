import Effect4.Laws.Program.ReleaseCustody.Producers

/-!
Concept: scope-lifetime-finalization, R11.
Question: continuation removal serves Execution.command_custody, then Workers.Assertions.releases_step.
Reach: the actual native frame pop, including constant continuations and response-sensitive scope callbacks.
Limit: the helpers establish no progress, source-use uniqueness or host agreement.
Unlock: the evaluator clause of the existing Machine.Lift command interface.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Pop
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control
abbrev Frame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev Result := FramePop EffName EffThunk Val Err Defect FiberId Ann

/-- The actual value answer retains the code or callback removed from the stack.
Consumer: value continuation debit in Execution.command_custody. -/
def valueAnswer (q : List Nat) (active : NCode)
    (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann) (stack : List NCode) : Nat :=
  match answer with
  | .frame (.onSuccessConst _ next) => currentCredits q next + stackCredits q next stack
  | .frame (.onSuccess _ (.afterScopeAdd _ fin)) => responseCredits q fin active + stackCap q stack
  | .frame frame => futureCredits q frame + stackCap q stack
  | .replacement next => currentCredits q next + stackCredits q next stack
  | .deferred cause => stackCredits q (.failure cause) stack
  | .empty => 0

def valueCredits (q : List Nat) (active : NCode) (pop : Result) : Nat :=
  valueAnswer q active pop.answer pop.fiber.stack

/-- Value popping transfers at most the reservations held by the saved frames.
Consumer: the sharper current-response value pop below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem value_cap (q : List Nat) (active : NCode) (frames : List NCode) (fiber : Frame)
    (empty : fiber.stack = []) :
    valueCredits q active (FrameFiber.popFrom .contA false frames fiber) ≤ stackCap q frames := by
  have aa : (Arm.contA == Arm.contA) = true := rfl
  have ae : (Arm.contA == Arm.contE) = false := rfl
  have aAll : (Arm.contA == Arm.contAll) = false := rfl
  induction frames generalizing fiber with
  | nil => exact Nat.zero_le _
  | cons frame rest ih =>
    have recursive (next : Frame) (nil : next.stack = []) := ih next nil
    cases frame
    case onExit body finalizer flag =>
      cases hi : fiber.interruptible <;> cases flag <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hi, Bool.false_and,
          Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_eq_true,
          if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        aa, ae, List.contains_nil, Bool.or_false, Bool.true_or, if_true,
        valueCredits, valueAnswer, empty,
        List.cons_append, List.nil_append, stackCap, futureCredits, Nat.zero_add]
      all_goals exact Nat.le_refl _
    case setInterruptible flag =>
      cases hc : fiber.interruptedCause <;> cases flag <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hc, Bool.false_eq_true, if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        aAll, List.contains_nil, Bool.or_false, Bool.false_eq_true, if_false, Bool.false_and,
        FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed, empty,
        valueCredits, valueAnswer, currentCredits, stackCap, futureCredits, Nat.zero_add, List.nil_append]
      case some.true cause => exact stack_credits_bounded q (.failure cause) rest
      all_goals apply recursive; rfl
    case asyncFinalizer name =>
      cases hi : fiber.interruptible <;> cases hc : fiber.interruptedCause <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hi, hc, Bool.false_eq_true, if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        ae, aAll, List.contains_nil, Bool.or_false, Bool.false_eq_true, if_false,
        Bool.false_and, FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed,
        Prim.ensure, if_true, empty, valueCredits, valueAnswer, currentCredits, stackCap, futureCredits,
        Nat.zero_add, List.nil_append]
      case true.some cause => exact stack_credits_bounded q (.failure cause) rest
      case false.none => exact ih fiber empty
      case false.some => exact ih fiber empty
      all_goals apply recursive; rfl
    all_goals simp (config := { failIfUnchanged := false }) only [FrameFiber.popFrom,
      Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons, List.contains_nil,
      Bool.false_and, Bool.false_eq_true, if_false, aa, ae, Bool.or_false, if_true,
      FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed, empty,
      List.nil_append, valueCredits, valueAnswer, stackCap, futureCredits, Nat.zero_add]
    case success => exact ih fiber empty
    case failure => exact ih fiber empty
    case sync => exact ih fiber empty
    case suspend => exact ih fiber empty
    case withFiber => exact ih fiber empty
    case yieldableError => exact ih fiber empty
    case onFailure body name => exact Nat.le_trans (ih fiber empty) (Nat.le_add_left _ _)
    case yieldNowWith => exact ih fiber empty
    case async => exact ih fiber empty
    case iterator => exact Nat.le_refl _
    case onSuccessConst => exact Nat.le_refl _
    case onSuccessAndFailure => exact Nat.le_refl _
    case exitFrame => exact Nat.le_refl _
    case whileLoop => exact Nat.le_refl _
    case onSuccess body name =>
      cases name <;> simp (config := { failIfUnchanged := false }) only [stackCap, futureCredits]
      case afterScopeAdd a fin =>
        exact Nat.add_le_add_right (response_credits_bounded q fin active) _
      all_goals exact Nat.le_refl _

/-- The actual value pop consumes the active response projection rather than an independent stack sum.
Consumer: native resumeValue debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_value (q : List Nat) (active : NCode) (fiber : Frame) :
    valueCredits q active (fiber.getCont .contA false) ≤ stackCredits q active fiber.stack := by
  unfold FrameFiber.getCont
  split
  · simp only [valueCredits, valueAnswer]
    exact Evaluation.failure_stack_le q fiber.pendingCause active fiber.stack
  · have bound := value_cap q active fiber.stack {fiber with stack := [], deferredInterrupt := false} rfl
    cases hs : fiber.stack with
    | nil =>
      rw [hs] at bound
      exact bound
    | cons frame rest =>
      rw [hs] at bound
      cases frame <;> simp (config := { failIfUnchanged := false }) only [stackCredits, stackCap] at bound ⊢
      case onSuccess body name =>
        cases name <;> simp (config := { failIfUnchanged := false }) only [stackCredits, stackCap] at bound ⊢
        case afterScopeAdd a fin =>
          have aa : (Arm.contA == Arm.contA) = true := rfl
          simp only [FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
            List.contains_cons, List.contains_nil, aa, Bool.or_false, if_true, Bool.false_and,
            Bool.false_eq_true, if_false, List.nil_append, valueCredits]
          exact Nat.le_refl _
        all_goals exact bound
      all_goals exact bound

/-- Invoking the selected native value arm consumes its retained answer reservation.
Consumer: resumeValue debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armA (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (frame : NCode) (value : Val) (provided : Option ExitV)
    (next : NCode) (pushed rest : List NCode)
    (found : frame.armA (interpAt root completed table).toPrimInterp value provided = some (next,pushed)) :
    currentCredits q next + stackCredits q next (pushed ++ rest) ≤
      valueAnswer q (.success value) (.frame frame) rest := by
  fun_cases Prim.armA (interpAt root completed table).toPrimInterp frame value provided
  case case6 loop cursor advanced body step =>
    have producer := Producers.interp_loopResume q root completed table loop cursor value
    rw [step] at producer
    simp only [Producers.loopCredits] at producer
    simp only [Prim.armA, step] at found
    cases found
    simp only [List.cons_append, List.nil_append, stackCredits, futureCredits, valueAnswer,
      producer, Nat.zero_add]
    exact Nat.le_refl _
  case case7 loop cursor body step =>
    have producer := Producers.interp_loopResume q root completed table loop cursor value
    rw [step] at producer
    simp only [Producers.loopCredits] at producer
    simp only [Prim.armA, step] at found
    cases found
    simp only [List.nil_append, valueAnswer, futureCredits, producer, Nat.zero_add]
    exact stack_credits_bounded q next rest
  case case8 generator cursor result step =>
    simp only [Prim.armA, step] at found
    cases found
    simp only [List.nil_append, valueAnswer, currentCredits, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q (.success result) rest) (Nat.le_add_left _ _)
  case case9 generator cursor cause step =>
    simp only [Prim.armA, step] at found
    cases found
    simp only [List.nil_append, valueAnswer, currentCredits, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q (.failure cause) rest) (Nat.le_add_left _ _)
  case case10 generator cursor body continueAs step =>
    have producer := Producers.interp_iter q root completed table generator value
    rw [step] at producer
    simp only [Producers.iterCredits] at producer
    simp only [Prim.armA, step] at found
    cases found
    change currentCredits q next + (futureCredits q (.iterator continueAs cursor) + stackCap q rest) ≤
      futureCredits q (.iterator generator cursor) + stackCap q rest
    have original : futureCredits q (.iterator generator cursor) =
        futureCredits q (.iterator generator Val.unit) := Producers.iterator_future q generator cursor Val.unit
    have residual : futureCredits q (.iterator continueAs cursor) =
        futureCredits q (.iterator continueAs Val.unit) := Producers.iterator_future q continueAs cursor Val.unit
    rw [original, residual]
    omega
  all_goals simp only [Prim.armA] at found
  all_goals cases found
  case case1.refl body name =>
    have producer := Producers.interp_contA q root completed table name value
    have lower := stack_credits_bounded q ((interpAt root completed table).contA name value) rest
    simp only [List.nil_append]
    cases name
    case afterScopeAdd a fin =>
      change currentCredits q (contAOf root (.afterScopeAdd a fin) value) +
        stackCredits q (contAOf root (.afterScopeAdd a fin) value) rest ≤
        afterAddCredits q fin value + stackCap q rest
      rw [after_add_code_credits]
      exact Nat.add_le_add_left lower _
    all_goals simp only [valueAnswer, futureCredits, nameCredits] at producer ⊢
    all_goals omega
  case case2.refl =>
    simp only [List.nil_append, valueAnswer]
    exact Nat.le_refl _
  case case3.refl body a e =>
    have producer := Producers.interp_contA q root completed table a value
    have lower := stack_credits_bounded q ((interpAt root completed table).contA a value) rest
    simp only [List.nil_append, valueAnswer, futureCredits]
    omega
  case case4.refl =>
    simp only [List.nil_append, valueAnswer, futureCredits, currentCredits, Nat.zero_add]
    exact stack_credits_bounded q _ rest
  case case5.refl =>
    simp only [List.nil_append, valueAnswer, Evaluation.exit_credits, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q _ rest) (Nat.le_add_left _ _)

/-- A running frame step retains its active code and remaining continuation credits.
Consumer: native evaluator debit in Execution.command_custody. -/
def stepCredits (q : List Nat) : FrameStep EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .running frame => currentCredits q frame.current + stackCredits q frame.current frame.stack
  | .finished _ => 0

/-- Resuming an actual native value consumes the credits transferred by getCont.
Consumer: native evaluator debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeValue (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (value : Val) (provided : Option ExitV) :
    stepCredits q (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1 ≤
      stackCredits q (.success value) fiber.stack := by
  have bound := getCont_value q (.success value) fiber
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  case case1 => exact Nat.zero_le _
  case case2 cause answer =>
    unfold valueCredits at bound
    rw [answer] at bound
    simp only [valueAnswer] at bound
    simp only [stepCredits, currentCredits, Nat.zero_add]
    exact bound
  case case3 next answer =>
    unfold valueCredits at bound
    rw [answer] at bound
    exact bound
  case case4 frame answer next pushed found =>
    have debit := armA q root completed table frame value provided next pushed
      (fiber.getCont .contA false).fiber.stack found
    unfold valueCredits at bound
    rw [answer] at bound
    exact Nat.le_trans debit bound
  case case5 => exact Nat.zero_le _

end Effect4.Program.ReleaseCustody.Pop
