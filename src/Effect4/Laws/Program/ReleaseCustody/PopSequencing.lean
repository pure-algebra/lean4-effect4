import Effect4.Laws.Program.ReleaseCustody.Sequencing

/-!
Concept: scope-lifetime-finalization, R11.
Question: continuation removal serves Execution.history and Workers.Assertions.releases_step.
Reach: the actual native frame pop over existing frame lists.
Limit: these local stack transports establish no admitted-history or command closure.
Unlock: callback sequencing through native value and cause continuation removal.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.PopSequencing
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.Pop (Frame)

/-- The answering saved frame cannot introduce the absent transient callback.
Consumer: native value and cause arm sequencing. -/
def AnswerClean : ContAnswer EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .frame frame => ∀ body a fin, frame ≠ .onSuccess body (.afterScopeAdd a fin)
  | _ => True

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_tail (head : NCode) {rest : List NCode} (held : NoAdd (head :: rest)) : NoAdd rest :=
  fun frame member => held frame (List.mem_cons_of_mem head member)

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_append (first second : List NCode) (left : NoAdd first) (right : NoAdd second) :
    NoAdd (first ++ second) := by
  intro frame member
  rcases List.mem_append.mp member with a | b
  · exact left frame a
  · exact right frame b

/-- Ensure pushes only masks, preserving absence of transient scope callbacks.
Consumer: the actual fused pop below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem ensure_noAdd (frame : NCode) (fiber : Frame) (held : NoAdd fiber.stack) :
    NoAdd (frame.ensure fiber).1.stack := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (add norm simp [NoAdd, List.mem_cons]) (add safe apply [noAdd_mask])

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem answerOf_clean (frame : NCode) (demand : Effect4.Arm) (replacement : Option NCode)
    (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (clean : ∀ body a fin, frame ≠ .onSuccess body (.afterScopeAdd a fin))
    (found : Prim.answerOf frame demand replacement = some answer) : AnswerClean answer := by
  unfold Prim.answerOf at found
  repeat' split at found
  all_goals aesop (add norm simp [AnswerClean, Option.mem_def])

/-- The hook's single drain preserves the remaining clean stack and answering frame.
Consumer: popFrom_noAdd. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem passPushed_noAdd (demand : Effect4.Arm) (skip : Bool) (fiber : Frame) (cause : Option CauseV)
    (held : NoAdd fiber.stack) :
    NoAdd (FrameFiber.passPushed demand skip fiber cause).fiber.stack ∧
      AnswerClean (FrameFiber.passPushed demand skip fiber cause).answer := by
  unfold FrameFiber.passPushed
  cases stack : fiber.stack with
  | nil => exact ⟨held, trivial⟩
  | cons frame rest =>
    simp only []
    have clean : ∀ body a fin, frame ≠ .onSuccess body (.afterScopeAdd a fin) :=
      held frame (by rw [stack]; exact .head _)
    have tail : NoAdd rest := noAdd_tail frame (by rw [← stack]; exact held)
    have ensured := ensure_noAdd frame {fiber with stack := rest} tail
    refine ⟨ensured, ?_⟩
    split
    · split
      · trivial
      · exact answerOf_clean frame demand _ _ clean (by assumption)
    · trivial

/-- The actual fused pop preserves clean saved stacks, including hook pushes.
Consumer: the native clean-stack value and cause continuation cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem popFrom_noAdd (demand : Effect4.Arm) (skip : Bool) (frames : List NCode)
    (fiber : Frame) (cause : Option CauseV) (held : NoAdd frames) (scratch : NoAdd fiber.stack) :
    NoAdd (FrameFiber.popFrom demand skip frames fiber cause).fiber.stack ∧
      AnswerClean (FrameFiber.popFrom demand skip frames fiber cause).answer := by
  induction frames generalizing fiber cause with
  | nil => exact ⟨scratch, trivial⟩
  | cons frame rest ih =>
    have clean : ∀ body a fin, frame ≠ .onSuccess body (.afterScopeAdd a fin) :=
      held frame (.head _)
    have tail := noAdd_tail frame held
    have ensured := ensure_noAdd frame fiber scratch
    have pushed := passPushed_noAdd demand skip (frame.ensure fiber).1 none ensured
    have recursive := ih (FrameFiber.passPushed demand skip (frame.ensure fiber).1 none).fiber
      none tail pushed.1
    have answering (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
        (found : Prim.answerOf frame demand (frame.ensure fiber).2 = some answer) : AnswerClean answer :=
      answerOf_clean frame demand _ answer clean found
    unfold FrameFiber.popFrom
    dsimp only
    repeat' split
    all_goals aesop (add norm simp [FrameFiber.passOn, FrameFiber.joinPushed,
      FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
      FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]) (add safe apply [answering, noAdd_append])

/-- The actual deferred-interrupt branch retains the original clean stack.
Consumer: native resumeValue and resumeCause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_noAdd (fiber : Frame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV)
    (held : NoAdd fiber.stack) :
    NoAdd (fiber.getCont demand skip cause).fiber.stack ∧ AnswerClean (fiber.getCont demand skip cause).answer := by
  unfold FrameFiber.getCont
  split
  · exact ⟨held, trivial⟩
  · exact popFrom_noAdd demand skip fiber.stack {fiber with stack := [], deferredInterrupt := false}
      cause held noAdd_empty

/-- Native value arms push only iterator or loop frames.
Consumer: actual clean-stack value resumption. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armA_noAdd (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : frame.armA (interpAt root completed table).toPrimInterp value provided = some (next, pushed)) :
    NoAdd pushed := by
  fun_cases Prim.armA (interpAt root completed table).toPrimInterp frame value provided
  all_goals aesop (add norm simp [Prim.armA, NoAdd, List.mem_cons])

/-- Native cause arms push no new frame.
Consumer: actual clean-stack failure resumption. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armE_noAdd (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : frame.armE (interpAt root completed table).toPrimInterp cause provided = some (next, pushed)) :
    NoAdd pushed := by
  fun_cases Prim.armE (interpAt root completed table).toPrimInterp frame cause provided
  all_goals simp only [Prim.armE] at found
  all_goals cases found
  all_goals exact noAdd_empty

/-- A native value resumption over a clean stack retains callback sequencing.
Consumer: the clean case of admitted frame evaluation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeValue_clean (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Frame) (value : Val) (provided : Option ExitV) (held : NoAdd fiber.stack) :
    match (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  have clean := (getCont_noAdd fiber .contA false none held).1
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  case case4 frame answer next pushed found =>
    have extra := armA_noAdd root completed table frame value provided next pushed found
    dsimp (config := { zetaDelta := true }) only
    exact .clean _ _ (noAdd_append _ _ extra clean)
  all_goals dsimp (config := { zetaDelta := true }) only
  all_goals aesop (add safe apply [Kept.clean])

/-- Native failure resumption over a clean stack retains callback sequencing.
Consumer: the clean case of admitted frame evaluation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeCause_clean (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Frame) (cause : CauseV) (provided : Option ExitV) (held : NoAdd fiber.stack) :
    match (fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  have clean := (getCont_noAdd fiber .contE true (some cause) held).1
  fun_cases FrameFiber.resumeCause (interpAt root completed table).toPrimInterp fiber cause provided
  case case4 pop delivered frame answer next pushed found =>
    have extra := armE_noAdd root completed table frame _ _ next pushed found
    dsimp (config := { zetaDelta := true }) only
    exact .clean _ _ (noAdd_append _ _ extra clean)
  all_goals dsimp (config := { zetaDelta := true }) only
  all_goals aesop (add safe apply [Kept.clean])

/-- Failure passes every transient value callback and saved constant.
Consumer: actual cause resumption, including pending scope-add cuts. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem popFrom_cause_kept {active : NCode} {frames : List NCode} (held : Kept active frames)
    (fiber : Frame) (cause : Option CauseV) (empty : fiber.stack = []) :
    NoAdd (FrameFiber.popFrom .contE true frames fiber cause).fiber.stack := by
  have ea : (Arm.contE == Arm.contA) = false := rfl
  have eAll : (Arm.contE == Arm.contAll) = false := rfl
  induction held generalizing fiber cause with
  | clean active frames held =>
    exact (popFrom_noAdd .contE true frames fiber cause held (by rw [empty]; exact noAdd_empty)).1
  | add active scope a fin rest tail phase =>
    have clean := (popFrom_noAdd .contE true rest fiber cause tail (by rw [empty]; exact noAdd_empty)).1
    simpa only [FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
      List.contains_cons, List.contains_nil, ea, eAll, Bool.or_false, Bool.false_or,
      Bool.false_eq_true, Bool.true_and, Bool.false_and, if_false, if_true, FrameFiber.passOn, FrameFiber.joinPushed,
      FrameFiber.passPushed, empty, List.nil_append] using clean
  | constant priority phase held ih =>
    have clean := ih fiber cause empty
    simpa only [FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
      List.contains_cons, List.contains_nil, ea, eAll, Bool.or_false, Bool.false_or,
      Bool.false_eq_true, Bool.true_and, Bool.false_and, if_false, if_true, FrameFiber.passOn, FrameFiber.joinPushed,
      FrameFiber.passPushed, empty, List.nil_append] using clean

/-- The actual cause pop discards all transient value callback positions.
Consumer: resumeCause_kept. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_cause_kept (fiber : Frame) (cause : CauseV) (held : Kept fiber.current fiber.stack) :
    NoAdd (fiber.getCont .contE true (some cause)).fiber.stack := by
  simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
  exact popFrom_cause_kept held {fiber with stack := [], deferredInterrupt := false} (some cause) rfl

/-- Actual failure continuation removal closes every Kept sequence case.
Consumer: native failure primitive and scoped-exit evaluation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeCause_kept (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Frame) (cause : CauseV) (provided : Option ExitV) (held : Kept fiber.current fiber.stack) :
    match (fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  have clean := getCont_cause_kept fiber cause held
  fun_cases FrameFiber.resumeCause (interpAt root completed table).toPrimInterp fiber cause provided
  case case4 pop delivered frame answer next pushed found =>
    have extra := armE_noAdd root completed table frame _ _ next pushed found
    dsimp (config := { zetaDelta := true }) only
    exact .clean _ _ (noAdd_append _ _ extra clean)
  all_goals dsimp (config := { zetaDelta := true }) only
  all_goals aesop (add safe apply [Kept.clean])

/-- A value pop reaching an exit callback passes the transient registration completely.
Consumer: the stateful finalizer evaluator retains a clean residual stack. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem popFrom_value_finalizer {active : NCode} {frames : List NCode}
    (held : Kept active frames) (fiber : Frame) (empty : fiber.stack = [])
    (body : NCode) (name : EffName) (flag : Bool)
    (found : (FrameFiber.popFrom .contA false frames fiber).answer = .frame (.onExit body name flag)) :
    NoAdd (FrameFiber.popFrom .contA false frames fiber).fiber.stack := by
  have aa : (Arm.contA == Arm.contA) = true := rfl
  induction held generalizing fiber with
  | clean active frames clean =>
    exact (popFrom_noAdd .contA false frames fiber none clean (by rw [empty]; exact noAdd_empty)).1
  | add active scope acquired fin rest clean phase =>
    simp only [FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
      List.contains_cons, List.contains_nil, aa, Bool.or_false, if_true] at found
    cases found
  | constant priority phase held ih =>
    simp only [FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
      List.contains_cons, List.contains_nil, aa, Bool.or_false, if_true] at found
    cases found

/-- The actual continuation getter reaching a finalizer has no pending registration below it.
Consumer: both native stateful exit routes. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_value_finalizer (fiber : Frame) (held : Kept fiber.current fiber.stack)
    (body : NCode) (name : EffName) (flag : Bool)
    (found : (fiber.getCont .contA false).answer = .frame (.onExit body name flag)) :
    NoAdd (fiber.getCont .contA false).fiber.stack := by
  cases deferred : fiber.deferredInterrupt
  · simp only [FrameFiber.getCont, deferred, Bool.false_and, Bool.false_eq_true, if_false] at found ⊢
    exact popFrom_value_finalizer held {fiber with stack := [], deferredInterrupt := false}
      rfl body name flag found
  · simp only [FrameFiber.getCont, deferred, Bool.not_false, Bool.true_and, if_true] at found
    cases found

/-- The ordinary value pop closes every pending callback, mask and saved-yield case.
Consumer: resumeValue_kept's deferred-interrupt split. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeValue_kept_clear (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (value : Val) (provided : Option ExitV) {active : NCode} {frames : List NCode}
    (held : Kept active frames) (fiber : Frame) (stack : fiber.stack = frames)
    (deferred : fiber.deferredInterrupt = false) :
    match (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  induction held generalizing fiber with
  | clean active frames held =>
    exact resumeValue_clean root completed table fiber value provided (by rw [stack]; exact held)
  | add active scope a fin rest tail phase =>
    simp only [FrameFiber.resumeValue, FrameFiber.getCont, deferred, Bool.false_and,
      Bool.false_eq_true, if_false, stack, FrameFiber.popFrom, Prim.ensure, Prim.answerOf,
      Prim.hasArm, Prim.arms, List.contains_cons, List.contains_nil, Bool.or_false,
      Prim.armA, List.nil_append]
    exact .clean _ _ tail
  | constant priority phase held ih =>
    rename_i active' next rest
    let base : Frame := {fiber with stack := rest}
    have same : ({base with stack := .onSuccessConst (.yieldNowWith priority) next :: base.stack} : Frame) = fiber := by
      change ({fiber with stack := .onSuccessConst (.yieldNowWith priority) next :: rest} : Frame) = fiber
      rw [← stack]
    rw [← same, FrameFiber.resumeValue_onSuccessConst (interpAt root completed table).toPrimInterp
      base (.yieldNowWith priority) next value provided deferred]
    exact held

/-- Actual native value resumption preserves callback sequencing through deferred interrupts too.
Consumer: native success, sync and scoped-exit evaluator branches. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeValue_kept (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Frame) (value : Val) (provided : Option ExitV) (held : Kept fiber.current fiber.stack) :
    match (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  cases deferred : fiber.deferredInterrupt
  · exact resumeValue_kept_clear root completed table value provided held fiber rfl deferred
  · simp only [FrameFiber.resumeValue, FrameFiber.getCont, deferred, Bool.not_false, Bool.true_and, if_true]
    exact interrupt held fiber.pendingCause

/-- The saved constant retains the exact phase below its injected yield.
Consumer: constant_push_kept. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem forced_unwrap (priority : Nat) {next : NCode} {frames : List NCode}
    (held : Kept (.onSuccessConst (.yieldNowWith priority) next) frames) : Kept next frames := by
  cases held
  case clean held => exact .clean _ _ held
  case add scope a fin rest tail phase =>
    cases phase with
    | forced priority phase => exact .add _ scope a fin rest tail phase
  case constant saved next' rest held phase =>
    cases phase with
    | forced priority phase => exact .constant saved phase held

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_cons (head : NCode) {rest : List NCode}
    (clean : ∀ body a fin, head ≠ .onSuccess body (.afterScopeAdd a fin)) (held : NoAdd rest) :
    NoAdd (head :: rest) := by
  intro frame member body a fin same
  cases List.mem_cons.mp member with
  | inl first => cases first; exact clean body a fin same
  | inr tail => exact held frame tail body a fin same

/-- The actual constant push either saves the pending phase or pushes an ordinary frame.
Consumer: the native onSuccessConst primitive case. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem constant_push_kept (body next : NCode) {frames : List NCode}
    (held : Kept (.onSuccessConst body next) frames) :
    Kept body (.onSuccessConst body next :: frames) := by
  cases body
  case yieldNowWith priority => exact forced_push (forced_unwrap priority held) priority
  all_goals
    have missing := opaque_noAdd held (by intro fin phase; cases phase) (by intro phase; cases phase)
    exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)

end Effect4.Program.ReleaseCustody.PopSequencing
