import Effect4.Laws.Program.ReleaseCustody.Pop

/-!
Concept: scope-lifetime-finalization, R11.
Question: failure continuation debit serves Execution.command_custody and Workers.Assertions.releases_step.
Reach: the actual failure pop and its interrupted-handler skipping and live mask hooks.
Limit: the helper proves no source uniqueness, progress or host agreement.
Unlock: the native evaluator's failure branch.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CausePop
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Pop (Frame Result)

def failureStack (q : List Nat) (frames : List NCode) : Nat :=
  stackCredits q (.failure (.die Defect.badName)) frames

/-- Cause payloads change no reservation in a remaining failure stack.
Consumer: native cause resumption below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem failure_stack_eq (q : List Nat) (cause : CauseV) (frames : List NCode) :
    stackCredits q (.failure cause) frames = failureStack q frames := by
  unfold failureStack stackCredits
  split <;> rfl

def answerCredits (q : List Nat) (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (stack : List NCode) : Nat :=
  match answer with
  | .frame frame => futureCredits q frame + stackCap q stack
  | .replacement next => currentCredits q next + stackCredits q next stack
  | .deferred _ => failureStack q stack
  | .empty => 0

def popCredits (q : List Nat) (pop : Result) : Nat :=
  answerCredits q pop.answer pop.fiber.stack

/-- Failure popping discards skipped constants and transfers the selected cause reservation.
Consumer: getCont_cause and native cause resumption. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem popFrom_cause (q : List Nat) (frames : List NCode) (fiber : Frame) (empty : fiber.stack = []) :
    popCredits q (FrameFiber.popFrom .contE true frames fiber) ≤ failureStack q frames := by
  have ee : (Arm.contE == Arm.contE) = true := rfl
  have ea : (Arm.contE == Arm.contA) = false := rfl
  have eAll : (Arm.contE == Arm.contAll) = false := rfl
  induction frames generalizing fiber with
  | nil => exact Nat.zero_le _
  | cons frame rest ih =>
    have recursive (next : Frame) (nil : next.stack = []) := ih next nil
    have cap := stack_credits_bounded q (.failure (.die Defect.badName)) rest
    cases frame
    case onExit body finalizer flag =>
      cases hi : fiber.interruptible <;> cases hc : fiber.interruptedCause <;> cases flag <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hi, hc,
          Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_eq_true,
          if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        ee, ea, eAll, List.contains_nil, Bool.or_false, Bool.false_or, if_true,
        FrameFiber.interrupted, hi, hc, Option.isSome_none, Option.isSome_some,
        Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false,
        popCredits, answerCredits, empty, List.cons_append, List.nil_append,
        failureStack, stackCredits, stackCap, futureCredits, Nat.zero_add,
        FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed]
      case true.some.true => exact Nat.le_trans (Nat.le_trans (ih fiber empty) cap) (Nat.le_add_left _ _)
      all_goals exact Nat.le_refl _
    case setInterruptible flag =>
      cases hc : fiber.interruptedCause <;> cases flag <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hc, Bool.false_eq_true, if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        eAll, List.contains_nil, Bool.or_false, Bool.false_eq_true, if_false, Bool.true_and,
        FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed, empty,
        popCredits, answerCredits, failureStack, stackCredits,
        futureCredits, Nat.zero_add, List.nil_append]
      all_goals simp (config := { failIfUnchanged := false }) only [FrameFiber.interrupted, Option.isSome_some, Bool.true_and, if_true, FrameFiber.skippedCause]
      all_goals apply Nat.le_trans (recursive _ _) cap
      all_goals rfl
    case asyncFinalizer name =>
      cases hi : fiber.interruptible <;> cases hc : fiber.interruptedCause <;>
        simp only [FrameFiber.popFrom, Prim.ensure, hi, hc, Bool.false_eq_true, if_false, if_true]
      all_goals simp only [Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons,
        ee, eAll, List.contains_nil, Bool.or_false, Bool.false_eq_true, if_false,
        FrameFiber.interrupted, hi, hc, Option.isSome_none, Option.isSome_some,
        Bool.true_and, Bool.false_and, FrameFiber.passOn, FrameFiber.joinPushed,
        FrameFiber.passPushed, Prim.ensure, if_true, empty, popCredits, answerCredits,
        failureStack, stackCredits, stackCap, futureCredits, Nat.zero_add,
        List.nil_append, List.cons_append]
      all_goals exact Nat.le_refl _
    all_goals simp (config := { failIfUnchanged := false }) only [FrameFiber.popFrom,
      Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms, List.contains_cons, List.contains_nil,
      Bool.true_and, Bool.false_eq_true, if_false, ee, ea, Bool.or_false, Bool.false_or, if_true,
      FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed, empty,
      List.nil_append, popCredits, answerCredits, failureStack, stackCredits,
      futureCredits, Nat.zero_add]
    case success => exact Nat.le_trans (ih fiber empty) cap
    case failure => exact Nat.le_trans (ih fiber empty) cap
    case sync => exact Nat.le_trans (ih fiber empty) cap
    case suspend => exact Nat.le_trans (ih fiber empty) cap
    case withFiber => exact Nat.le_trans (ih fiber empty) cap
    case yieldableError => exact Nat.le_trans (ih fiber empty) cap
    case yieldNowWith => exact Nat.le_trans (ih fiber empty) cap
    case async => exact Nat.le_trans (ih fiber empty) cap
    case iterator => exact Nat.le_trans (Nat.le_trans (ih fiber empty) cap) (Nat.le_add_left _ _)
    case whileLoop => exact Nat.le_trans (ih fiber empty) cap
    case onSuccess body name =>
      cases name <;> simp (config := { failIfUnchanged := false }) only [stackCredits, futureCredits, responseCredits, Nat.zero_add]
      case afterScopeAdd => exact Nat.le_trans (ih fiber empty) cap
      all_goals have bound := Nat.le_trans (ih fiber empty) cap
      all_goals simp only [popCredits, answerCredits, futureCredits, failureStack] at bound
      all_goals omega
    case onSuccessConst body next =>
      exact Nat.le_trans (Nat.le_trans (ih fiber empty) (Evaluation.failure_stack_le q (.die Defect.badName) next rest)) (Nat.le_add_left _ _)
    case onFailure body name =>
      cases interrupted : fiber.interrupted <;> simp only [Bool.false_eq_true, if_false, if_true, FrameFiber.skippedCause]
      case false => exact Nat.le_refl _
      case true => exact Nat.le_trans (Nat.le_trans (ih fiber empty) cap) (Nat.le_add_left _ _)
    case onSuccessAndFailure body a e =>
      cases interrupted : fiber.interrupted <;> simp only [Bool.false_eq_true, if_false, if_true, FrameFiber.skippedCause]
      case false => exact Nat.le_refl _
      case true => exact Nat.le_trans (Nat.le_trans (ih fiber empty) cap) (Nat.le_add_left _ _)
    case exitFrame =>
      cases interrupted : fiber.interrupted <;> simp only [Bool.false_eq_true, if_false, if_true, FrameFiber.skippedCause, Nat.zero_add]
      case false => exact Nat.le_refl _
      case true => exact Nat.le_trans (ih fiber empty) cap
/-- The actual failure pop retains no more than the interrupted failure stack.
Consumer: native resumeCause below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_cause (q : List Nat) (fiber : Frame) (cause : CauseV) :
    popCredits q (fiber.getCont .contE true (some cause)) ≤ stackCredits q (.failure cause) fiber.stack := by
  unfold popCredits
  rw [FrameFiber.getCont_answer_cause, FrameFiber.getCont_fiber_cause]
  change popCredits q (fiber.getCont .contE true) ≤ stackCredits q (.failure cause) fiber.stack
  rw [failure_stack_eq]
  simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
  exact popFrom_cause q fiber.stack {fiber with stack := [], deferredInterrupt := false} rfl

/-- Invoking the selected failure handler consumes its retained reservation.
Consumer: resumeCause below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armE (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (frame : NCode) (cause : CauseV) (provided : Option ExitV)
    (next : NCode) (pushed rest : List NCode)
    (found : frame.armE (interpAt root completed table).toPrimInterp cause provided = some (next,pushed)) :
    currentCredits q next + stackCredits q next (pushed ++ rest) ≤
      answerCredits q (.frame frame) rest := by
  fun_cases Prim.armE (interpAt root completed table).toPrimInterp frame cause provided
  all_goals simp only [Prim.armE] at found
  all_goals cases found
  case case1.refl body name =>
    have producer := Producers.interp_contE q root completed table name cause
    simp only [answerCredits, List.nil_append, producer, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q _ rest) (Nat.le_add_left _ _)
  case case2.refl body a e =>
    have producer := Producers.interp_contE q root completed table e cause
    simp only [answerCredits, List.nil_append, producer, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q _ rest) (Nat.le_add_left _ _)
  case case3.refl =>
    simp only [answerCredits, List.nil_append, currentCredits, Nat.zero_add, futureCredits]
    exact stack_credits_bounded q _ rest
  case case4.refl =>
    simp only [answerCredits, List.nil_append, Evaluation.exit_credits, Nat.zero_add]
    exact Nat.le_trans (stack_credits_bounded q _ rest) (Nat.le_add_left _ _)
  case case5.refl name =>
    have producer : currentCredits q (if cause.hasInterrupts then
        (interpAt root completed table).cancelThenFail name cause else .failure cause) = 0 := by
      change currentCredits q (if cause.hasInterrupts then
        .onSuccess (cancelProgramOf name) (.reFail cause) else .failure cause) = 0
      split
      · simp only [currentCredits, Producers.cancel]
      · rfl
    simp only [answerCredits, List.nil_append, producer, Nat.zero_add, futureCredits]
    exact stack_credits_bounded q _ rest

/-- Native failure resumption consumes the actual saved stack reservation.
Consumer: evaluator debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeCause (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (cause : CauseV) (provided : Option ExitV) :
    Pop.stepCredits q (fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1 ≤
      stackCredits q (.failure cause) fiber.stack := by
  have bound := getCont_cause q fiber cause
  fun_cases FrameFiber.resumeCause (interpAt root completed table).toPrimInterp fiber cause provided
  case case1 => exact Nat.zero_le _
  case case2 deferred answer =>
    unfold popCredits at bound
    rw [answer] at bound
    simp only [answerCredits, failure_stack_eq] at bound
    simp only [Pop.stepCredits, currentCredits, Nat.zero_add, failure_stack_eq]
    exact bound
  case case3 next answer =>
    unfold popCredits at bound
    rw [answer] at bound
    exact bound
  case case4 frame answer next pushed found =>
    have debit := armE q root completed table frame
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
      (provided.map (fiber.getCont .contE true (some cause)).deliveredExit)
      next pushed (fiber.getCont .contE true (some cause)).fiber.stack found
    unfold popCredits at bound
    rw [answer] at bound
    exact Nat.le_trans debit bound
  case case5 => exact Nat.zero_le _
end Effect4.Program.ReleaseCustody.CausePop
