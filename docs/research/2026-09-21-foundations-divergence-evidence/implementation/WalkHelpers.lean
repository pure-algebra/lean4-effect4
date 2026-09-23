import Effect4.Laws.Program.Simulation.Hooks

/-!
# The pop walk (P3, step 4a)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). Delivering an
exit walks the saved slots: the frame's `getCont`/`popFrom` over `Prim` frames, the term's
`popR` over `ScopeFrame` slots. On related stacks the two walks agree slot by slot: both
pass the same slots, both stop at the same one, and what they leave behind is related
(`walk_rel`). The frame's answer is characterised (`WalkRel`) so that the three frame
paths that consume it — the scoped exit callback, an `OnExit` finalizer program, and the
plain arm — can each be matched by the evaluator lemma.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
  Effect4.FrameFiber

/-! ## The exit's demand, skip and arm -/

/-- The frame's demand for an exit (`finalizerOr`, `exitScoped`, `step`). -/
def demandOf : ExitV → Effect4.Arm
  | .success _ => .contA
  | .failure _ => .contE

/-- Whether interrupted handlers are skipped for an exit. -/
def skipOf : ExitV → Bool
  | .success _ => false
  | .failure _ => true

/-- The term's failure flag. -/
def failingOf : ExitV → Bool
  | .failure _ => true
  | _ => false

/-- The arm the frame runs on the answering frame, with the exit provided (`step`). -/
def armOf (interp : NInterp) (ex : ExitV) (fr : NCode) : Option (NCode × List NCode) :=
  match ex with
  | .success v => fr.armA interp v (some ex)
  | .failure c => fr.armE interp c (some ex)

theorem armOf_onSuccess (interp : NInterp) (v : Val) (body : NCode) (n : EffName) :
    armOf interp (.success v) (Prim.onSuccess body n) = some (interp.contA n v, []) := rfl

theorem armOf_onSuccessConst (interp : NInterp) (v : Val) (body next : NCode) :
    armOf interp (.success v) (Prim.onSuccessConst body next) = some (next, []) := rfl

theorem armOf_onFailure (interp : NInterp) (c : CauseV) (body : NCode) (n : EffName) :
    armOf interp (.failure c) (Prim.onFailure body n) = some (interp.contE n c, []) := rfl

theorem armOf_onBoth_succ (interp : NInterp) (v : Val) (body : NCode) (a e : EffName) :
    armOf interp (.success v) (Prim.onSuccessAndFailure body a e) = some (interp.contA a v, []) := rfl

theorem armOf_onBoth_fail (interp : NInterp) (c : CauseV) (body : NCode) (a e : EffName) :
    armOf interp (.failure c) (Prim.onSuccessAndFailure body a e) = some (interp.contE e c, []) := rfl

theorem armOf_exitFrame (interp : NInterp) (ex : ExitV) (body : NCode) :
    armOf interp ex (Prim.exitFrame body) = some (Prim.success (interp.reifyExit ex), []) := by
  cases ex <;> rfl

theorem armOf_iterator (interp : NInterp) (v : Val) (g : EffName) (cursor : Val) :
    armOf interp (.success v) (Prim.iterator g cursor) =
      (match (interp.iterNext g v).2 with
       | .done r => some (Prim.success r, [])
       | .halt c => some (Prim.failure c, [])
       | .resume next cont => some (next, [Prim.iterator cont cursor])) := by
  unfold armOf Prim.armA
  dsimp only
  cases (interp.iterNext g v).2 <;> rfl

theorem armOf_whileLoop (interp : NInterp) (v : Val) (l : EffName) (cursor : Val) :
    armOf interp (.success v) (Prim.whileLoop l cursor) =
      (match interp.loopResume l cursor v with
       | .continue next body => some (body, [Prim.whileLoop l next])
       | .finish code => some (code, [])) := by
  show (Prim.whileLoop l cursor).armA interp v (some (.success v)) = _
  cases h : interp.loopResume l cursor v <;> simp only [Prim.armA, h]

theorem armOf_asyncFinalizer (interp : NInterp) (c : CauseV) (name : EffName) :
    armOf interp (.failure c) (Prim.asyncFinalizer name) =
      some (if c.hasInterrupts then interp.cancelThenFail name c else Prim.failure c, []) := rfl

/-! ## The term's walk, one slot at a time -/

section popREqs

variable (i : RInterp) (T : List ScopeFrame) (frame : RSaved)

theorem popR_nil (ex : ExitV) : popR i ex [] frame = ({ frame with stack := [] }, some ex) := rfl

theorem popR_answer (ex : ExitV) (next : ExitV → RProgram) :
    popR i ex (.answer next :: T) frame =
      (match next ex with
       | .pure ex' => popR i ex' T { frame with stack := T }
       | .vis (.inr (.unguard ex')) _ => popR i ex' T { frame with stack := T }
       | code => ({ frame with stack := T, current := code }, none)) := rfl

theorem popR_mask (ex : ExitV) (flag : Bool) (s : ScopeFrame)
    (hs : s = .restoreMask flag ∨ s = .finalizerMask flag) :
    popR i ex (s :: T) frame =
      (match frame.interruptedCause with
       | some cause =>
         if flag && !failingOf ex then
           ({ frame with stack := T, interruptible := flag, current := .pure (.failure cause) }, none)
         else popR i ex T { frame with stack := T, interruptible := flag }
       | none => popR i ex T { frame with stack := T, interruptible := flag }) := by
  rcases hs with rfl | rfl <;> rfl

theorem popR_mask_false (ex : ExitV) (s : ScopeFrame)
    (hs : s = .restoreMask false ∨ s = .finalizerMask false) :
    popR i ex (s :: T) frame = popR i ex T { frame with stack := T, interruptible := false } := by
  rw [popR_mask i T frame ex false s hs]
  cases frame.interruptedCause <;> rfl

theorem popR_resume_onSuccess (v : Val) (K : ExitV → RProgram) :
    popR i (.success v) (.resume .onSuccess K :: T) frame =
      ({ frame with stack := T, current := K (.success v) }, none) := rfl

theorem popR_resume_onSuccess_fail (c : CauseV) (K : ExitV → RProgram) :
    popR i (.failure c) (.resume .onSuccess K :: T) frame =
      popR i (.failure c) T { frame with stack := T } := by
  cases frame with
  | mk current stack flag interrupted deferred => cases interrupted <;> rfl

theorem popR_resume_onFailure_succ (v : Val) (K : ExitV → RProgram) :
    popR i (.success v) (.resume .onFailure K :: T) frame =
      popR i (.success v) T { frame with stack := T } := rfl

theorem popR_resume_onFailure (c : CauseV) (K : ExitV → RProgram)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = false) :
    popR i (.failure c) (.resume .onFailure K :: T) frame =
      ({ frame with stack := T, current := K (.failure c) }, none) := by
  simp [popR, GuardKind.hasExitArm, hint]

theorem popR_resume_onFailure_skip (c : CauseV) (K : ExitV → RProgram)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = true) :
    popR i (.failure c) (.resume .onFailure K :: T) frame =
      popR i (.failure (Cause.sanitize c frame.pendingCause)) T { frame with stack := T }   := by
  cases frame with
  | mk current stack flag interrupted deferred =>
    cases interrupted with
    | none =>
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true] at hint
    | some interrupted =>
      simp only [Option.isSome_some, Bool.and_true] at hint
      subst flag
      rfl

theorem popR_resume_all_succ (v : Val) (K : ExitV → RProgram) :
    popR i (.success v) (.resume .all K :: T) frame =
      ({ frame with stack := T, current := K (.success v) }, none) := rfl

theorem popR_resume_all (c : CauseV) (K : ExitV → RProgram)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = false) :
    popR i (.failure c) (.resume .all K :: T) frame =
      ({ frame with stack := T, current := K (.failure c) }, none) := by
  simp [popR, GuardKind.hasExitArm, hint]

theorem popR_resume_all_skip (c : CauseV) (K : ExitV → RProgram)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = true) :
    popR i (.failure c) (.resume .all K :: T) frame =
      popR i (.failure (Cause.sanitize c frame.pendingCause)) T { frame with stack := T }   := by
  cases frame with
  | mk current stack flag interrupted deferred =>
    cases interrupted with
    | none =>
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true] at hint
    | some interrupted =>
      simp only [Option.isSome_some, Bool.and_true] at hint
      subst flag
      rfl

theorem popR_resume_onExit (ex : ExitV) (K : ExitV → RProgram) :
    popR i ex (.resume (.onExit false) K :: T) frame =
      ({ frame with
          stack := .finalizerMask frame.interruptible :: T
          interruptible := false
          current := K ex }, none) := by
  cases ex <;> rfl

theorem popR_asyncFinalizer_succ (v : Val) (name : EffName)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = true) :
    popR i (.success v) (.asyncFinalizer name :: T) frame =
      ({ frame with stack := T, current := .pure (.failure frame.pendingCause) }, none) := by
  simp [popR, hint, RSaved.pendingCause]

theorem popR_asyncFinalizer_succ_pass (v : Val) (name : EffName)
    (hint : (frame.interruptible && frame.interruptedCause.isSome) = false) :
    popR i (.success v) (.asyncFinalizer name :: T) frame =
      popR i (.success v) T { frame with stack := T } := by
  simp [popR, hint]

theorem popR_asyncFinalizer_fail (c : CauseV) (name : EffName) :
    popR i (.failure c) (.asyncFinalizer name :: T) frame =
      ({ frame with
          stack := if frame.interruptible then .restoreMask true :: T else T,
          interruptible := false,
          current := if c.hasInterrupts then i.cancelThenFail name c else .pure (.failure c) },
        none) := rfl

theorem popR_iter_fail (c : CauseV) (g : EffName) :
    popR i (.failure c) (.iter g :: T) frame = popR i (.failure c) T { frame with stack := T } := rfl

theorem popR_iter_succ (v : Val) (g : EffName) :
    popR i (.success v) (.iter g :: T) frame =
      (match (i.iterNext g v).2 with
       | .done r => ({ frame with stack := T, current := .pure (.success r) }, none)
       | .halt c => ({ frame with stack := T, current := .pure (.failure c) }, none)
       | .resume code next => ({ frame with stack := .iter next :: T, current := code }, none)) := rfl

theorem popR_loop_fail (c : CauseV) (name : EffName) (cursor : Val) :
    popR i (.failure c) (.loop name cursor :: T) frame =
      popR i (.failure c) T { frame with stack := T } := rfl

theorem popR_loop_succ (v : Val) (name : EffName) (cursor : Val) :
    popR i (.success v) (.loop name cursor :: T) frame =
      (match i.loopResume name cursor v with
       | .continue next body =>
         ({ frame with stack := .loop name next :: T, current := body }, none)
       | .finish code => ({ frame with stack := T, current := code }, none)) := by
  cases h : i.loopResume name cursor v <;> simp only [popR, h]

end popREqs

/-! ## The frame's walk, one frame at a time -/

/-- A frame whose hook does nothing and that declares the demanded arm answers with itself,
leaving the frames below. -/
theorem popFrom_plain_answer (demand : Effect4.Arm) (skip : Bool) {f : NCode} {rest : List NCode}
    {fiber : FFiber} (hens : f.ensure fiber = (fiber, none)) (harm : f.hasArm demand = true)
    (hskip : (skip && fiber.interrupted) = false) (hstack : fiber.stack = []) :
    (popFrom demand skip (f :: rest) fiber).answer = .frame f ∧
      (popFrom demand skip (f :: rest) fiber).fiber = { fiber with stack := rest } := by
  have hanswer : f.answerOf demand (f.ensure fiber).snd = some (.frame f) := by
    rw [hens]; exact Prim.answerOf_arm f demand harm
  have hskip' : (skip && (f.ensure fiber).fst.interrupted) = false := by rw [hens]; exact hskip
  refine ⟨popFrom_answer_answer demand skip f rest fiber _ hanswer hskip', ?_⟩
  rw [popFrom_answer_fiber demand skip f rest fiber _ hanswer hskip', hens]
  simp [hstack]

/-- A frame whose hook pushes nothing and that does not answer is passed. -/
theorem popFrom_plain_pass (demand : Effect4.Arm) (skip : Bool) {f : NCode} {rest : List NCode}
    {fiber : FFiber} (hpush : (f.ensure fiber).fst.stack = fiber.stack)
    (h : f.answerOf demand (f.ensure fiber).snd = none ∨
      (skip && (f.ensure fiber).fst.interrupted) = true)
    (hstack : fiber.stack = []) :
    (popFrom demand skip (f :: rest) fiber).answer =
        (popFrom demand skip rest (f.ensure fiber).fst).answer ∧
      (popFrom demand skip (f :: rest) fiber).fiber =
        (popFrom demand skip rest (f.ensure fiber).fst).fiber := by
  rw [popFrom_continue_answer demand skip f rest fiber h, popFrom_continue_fiber demand skip f rest fiber h,
    popFrom_pass_no_push demand skip f rest fiber hstack hpush]
  exact ⟨rfl, rfl⟩

/-- An `OnExit` frame answers on either arm, masked, with its restoring frame pushed exactly
when the fiber was interruptible. -/
theorem popFrom_onExit (demand : Effect4.Arm) (skip : Bool) (body : NCode) (fin : EffName)
    (rest : List NCode) (fiber : FFiber) (hstack : fiber.stack = []) :
    (popFrom demand skip (Prim.onExit body fin false :: rest) fiber).answer =
        .frame (Prim.onExit body fin false) ∧
      (popFrom demand skip (Prim.onExit body fin false :: rest) fiber).fiber =
        ⟨fiber.current, (if fiber.interruptible then [Prim.setInterruptible true] else []) ++ rest,
          false, fiber.interruptedCause, fiber.deferredInterrupt⟩ := by
  have harm : (Prim.onExit body fin false : NCode).hasArm demand = true := by
    cases demand <;> rfl
  cases hflag : fiber.interruptible with
  | true =>
    have hens := Prim.ensure_onExit_masks body fin fiber hflag
    have hanswer : (Prim.onExit body fin false : NCode).answerOf demand
        ((Prim.onExit body fin false : NCode).ensure fiber).snd =
        some (.frame (Prim.onExit body fin false)) := by
      rw [hens]; exact Prim.answerOf_arm _ demand harm
    have hskip : (skip && ((Prim.onExit body fin false : NCode).ensure fiber).fst.interrupted) = false := by
      rw [hens]; simp [FrameFiber.interrupted]
    refine ⟨popFrom_answer_answer demand skip _ rest fiber _ hanswer hskip, ?_⟩
    rw [popFrom_answer_fiber demand skip _ rest fiber _ hanswer hskip, hens]
    simp [hstack]
  | false =>
    have hens := Prim.ensure_onExit_already_masked body fin false fiber hflag
    have hanswer : (Prim.onExit body fin false : NCode).answerOf demand
        ((Prim.onExit body fin false : NCode).ensure fiber).snd =
        some (.frame (Prim.onExit body fin false)) := by
      rw [hens]; exact Prim.answerOf_arm _ demand harm
    have hskip : (skip && ((Prim.onExit body fin false : NCode).ensure fiber).fst.interrupted) = false := by
      rw [hens]; simp [FrameFiber.interrupted, hflag]
    refine ⟨popFrom_answer_answer demand skip _ rest fiber _ hanswer hskip, ?_⟩
    rw [popFrom_answer_fiber demand skip _ rest fiber _ hanswer hskip, hens]
    simp [hstack, hflag]

/-- The parking finalizer on a failure: answers masked, its restoring frame pushed exactly
when the fiber was interruptible. -/
theorem popFrom_asyncFinalizer_fail (name : EffName) (rest : List NCode) (fiber : FFiber)
    (hstack : fiber.stack = []) :
    (popFrom .contE true (Prim.asyncFinalizer name :: rest) fiber).answer =
        .frame (Prim.asyncFinalizer name) ∧
      (popFrom .contE true (Prim.asyncFinalizer name :: rest) fiber).fiber =
        ⟨fiber.current, (if fiber.interruptible then [Prim.setInterruptible true] else []) ++ rest,
          false, fiber.interruptedCause, fiber.deferredInterrupt⟩ := by
  have harm : (Prim.asyncFinalizer name : NCode).hasArm .contE = true := rfl
  cases hflag : fiber.interruptible with
  | true =>
    have hens := Prim.ensure_asyncFinalizer_masks name fiber hflag
    have hanswer : (Prim.asyncFinalizer name : NCode).answerOf .contE
        ((Prim.asyncFinalizer name : NCode).ensure fiber).snd =
        some (.frame (Prim.asyncFinalizer name)) := by
      rw [hens]; exact Prim.answerOf_arm _ _ harm
    have hskip : (true && ((Prim.asyncFinalizer name : NCode).ensure fiber).fst.interrupted) = false := by
      rw [hens]; simp [FrameFiber.interrupted]
    refine ⟨popFrom_answer_answer .contE true _ rest fiber _ hanswer hskip, ?_⟩
    rw [popFrom_answer_fiber .contE true _ rest fiber _ hanswer hskip, hens]
    simp [hstack]
  | false =>
    have hens := Prim.ensure_asyncFinalizer_already_masked name fiber hflag
    have hanswer : (Prim.asyncFinalizer name : NCode).answerOf .contE
        ((Prim.asyncFinalizer name : NCode).ensure fiber).snd =
        some (.frame (Prim.asyncFinalizer name)) := by
      rw [hens]; exact Prim.answerOf_arm _ _ harm
    have hskip : (true && ((Prim.asyncFinalizer name : NCode).ensure fiber).fst.interrupted) = false := by
      rw [hens]; simp [FrameFiber.interrupted, hflag]
    refine ⟨popFrom_answer_answer .contE true _ rest fiber _ hanswer hskip, ?_⟩
    rw [popFrom_answer_fiber .contE true _ rest fiber _ hanswer hskip, hens]
    simp [hstack, hflag]

/-- The parking finalizer on a success, from an interruptible fiber: its pushed mask is
popped inside the same walk, substituting the pending cause or restoring the flag. -/
theorem popFrom_asyncFinalizer_succ (name : EffName) (rest : List NCode) (fiber : FFiber)
    (hstack : fiber.stack = []) (hflag : fiber.interruptible = true) :
    (∀ cause, fiber.interruptedCause = some cause →
      (popFrom .contA false (Prim.asyncFinalizer name :: rest) fiber).answer =
          .replacement (Prim.failure cause) ∧
        (popFrom .contA false (Prim.asyncFinalizer name :: rest) fiber).fiber =
          ⟨fiber.current, rest, true, fiber.interruptedCause, fiber.deferredInterrupt⟩) ∧
    (fiber.interruptedCause = none →
      (popFrom .contA false (Prim.asyncFinalizer name :: rest) fiber).answer =
          (popFrom .contA false rest fiber).answer ∧
        (popFrom .contA false (Prim.asyncFinalizer name :: rest) fiber).fiber =
          (popFrom .contA false rest fiber).fiber) := by
  have hpass : (Prim.asyncFinalizer name : NCode).answerOf .contA
      ((Prim.asyncFinalizer name : NCode).ensure fiber).snd = none := by
    rw [Prim.ensure_asyncFinalizer_no_replacement]
    exact Prim.answerOf_missing _ _ (Prim.hasArm_asyncFinalizer_contA_false name)
  have hmask := Prim.ensure_asyncFinalizer_masks name fiber hflag
  have hfib : FrameFiber.mk fiber.current fiber.stack true fiber.interruptedCause
      fiber.deferredInterrupt = fiber := by
    rw [← hflag]
  refine ⟨fun cause hcause => ?_, fun hcause => ?_⟩
  · have hdrain : passPushed .contA false ((Prim.asyncFinalizer name : NCode).ensure fiber).fst =
        FramePop.mk (.replacement (Prim.failure cause)) [Prim.setInterruptible true]
          ((Prim.setInterruptible true : NCode).passEvents (some (Prim.failure cause)))
          (FrameFiber.mk fiber.current fiber.stack true fiber.interruptedCause
            fiber.deferredInterrupt) none := by
      rw [hmask]
      exact passPushed_setInterruptible_substitutes .contA _ fiber.stack cause rfl hcause
    have hne : (ContAnswer.replacement (Prim.failure cause) :
        ContAnswer EffName EffThunk Val Err Defect FiberId Ann) ≠ .empty := by simp
    rw [popFrom_continue_answer .contA false _ rest fiber (Or.inl hpass),
      popFrom_continue_fiber .contA false _ rest fiber (Or.inl hpass)]
    unfold continueFrom
    rw [joinPushed_of_answer .contA false _ rest _ _ hne (by rw [hdrain]), hdrain]
    exact ⟨rfl, by simp [hstack]⟩
  · have hdrain : passPushed .contA false ((Prim.asyncFinalizer name : NCode).ensure fiber).fst =
        FramePop.mk .empty [Prim.setInterruptible true]
          ((Prim.setInterruptible true : NCode).passEvents none)
          (FrameFiber.mk fiber.current fiber.stack true fiber.interruptedCause
            fiber.deferredInterrupt) none := by
      rw [hmask]
      exact passPushed_setInterruptible_no_pending .contA false _ fiber.stack rfl rfl hcause
    rw [popFrom_continue_answer .contA false _ rest fiber (Or.inl hpass),
      popFrom_continue_fiber .contA false _ rest fiber (Or.inl hpass)]
    unfold continueFrom
    rw [joinPushed_of_empty .contA false _ rest _ (by rw [hdrain]), hdrain, hfib]
    exact ⟨rfl, rfl⟩

theorem ensure_mask_cause (flag : Bool) (fiber : FFiber) :
    ((Prim.setInterruptible flag : NCode).ensure fiber).fst.interruptedCause =
      fiber.interruptedCause := by
  cases hcause : fiber.interruptedCause <;> cases flag <;> simp [Prim.ensure, hcause]

theorem ensure_mask_deferred (flag : Bool) (fiber : FFiber) :
    ((Prim.setInterruptible flag : NCode).ensure fiber).fst.deferredInterrupt =
      fiber.deferredInterrupt := by
  cases hcause : fiber.interruptedCause <;> cases flag <;> simp [Prim.ensure, hcause]

theorem ensure_mask_current (flag : Bool) (fiber : FFiber) :
    ((Prim.setInterruptible flag : NCode).ensure fiber).fst.current = fiber.current := by
  cases hcause : fiber.interruptedCause <;> cases flag <;> simp [Prim.ensure, hcause]

/-- The failure explicitly supplied by exit delivery; a success has no failure carrier. -/
def causeOf : ExitV → Option CauseV
  | .success _ => none
  | .failure cause => some cause

/-- The exit carried through the compiled walk, before a consumer runs its answer. -/
def walkExit (ex : ExitV) (stack : List NCode) (fiber : FFiber) : ExitV :=
  (popFrom (demandOf ex) (skipOf ex) stack fiber (causeOf ex)).deliveredExit ex

theorem walkExit_success (value : Val) (stack : List NCode) (fiber : FFiber) :
    walkExit (.success value) stack fiber = .success value := rfl

theorem walkExit_nil (ex : ExitV) (fiber : FFiber) : walkExit ex [] fiber = ex := by
  cases ex <;> rfl

private theorem skippedCause_isSome (demand : Effect4.Arm) (frame : NCode) (fiber : FFiber)
    (cause : Option CauseV) :
    (skippedCause demand frame fiber cause).isSome = cause.isSome := by
  cases cause with
  | none => rfl
  | some cause =>
    simp only [skippedCause]
    split
    · split <;> rfl
    · rfl

private theorem passPushed_carried_isSome (demand : Effect4.Arm) (skip : Bool) (fiber : FFiber)
    (cause : Option CauseV) :
    (passPushed demand skip fiber cause).carriedCause.isSome = cause.isSome := by
  unfold passPushed
  split
  · rfl
  · dsimp only
    split
    · split
      · exact skippedCause_isSome _ _ _ _
      · rfl
    · rfl

private theorem popFrom_carried_isSome (demand : Effect4.Arm) (skip : Bool)
    (stack : List NCode) (fiber : FFiber) (cause : Option CauseV) :
    (popFrom demand skip stack fiber cause).carriedCause.isSome = cause.isSome := by
  induction stack generalizing fiber cause with
  | nil => rfl
  | cons frame rest ih =>
    simp only [popFrom]
    split
    · split
      · simp only [passOn, joinPushed]
        split <;> simp only [ih, passPushed_carried_isSome, skippedCause_isSome]
      · rfl
    · simp only [passOn, joinPushed]
      split <;> simp only [ih, passPushed_carried_isSome]

/-- A frame that answers without preemption retains the incoming exit. -/
theorem walkExit_answer (ex : ExitV) (frame : NCode) (rest : List NCode) (fiber : FFiber)
    (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (ha : frame.answerOf (demandOf ex) (frame.ensure fiber).snd = some answer)
    (hs : (skipOf ex && (frame.ensure fiber).fst.interrupted) = false) :
    walkExit ex (frame :: rest) fiber = ex := by
  simp only [walkExit, popFrom, ha, hs, Bool.false_eq_true, ↓reduceIte]
  cases ex <;> rfl

/-- A guard miss, or a passed non-handler such as the restoring mask, leaves the exit alone. -/
theorem walkExit_pass (ex : ExitV) (frame : NCode) (rest : List NCode) (fiber : FFiber)
    (hstack : (frame.ensure fiber).fst.stack = [])
    (h : frame.answerOf (demandOf ex) (frame.ensure fiber).snd = none ∨
      (skipOf ex && (frame.ensure fiber).fst.interrupted) = true)
    (hc : skippedCause (demandOf ex) frame (frame.ensure fiber).fst (causeOf ex) = causeOf ex) :
    walkExit ex (frame :: rest) fiber = walkExit ex rest (frame.ensure fiber).fst := by
  rcases h with ha | hs
  · simp only [walkExit, popFrom, ha, passOn, joinPushed, passPushed, hstack, FramePop.deliveredExit]
  · cases ha : frame.answerOf (demandOf ex) (frame.ensure fiber).snd with
    | none => simp only [walkExit, popFrom, ha, passOn, joinPushed, passPushed, hstack, FramePop.deliveredExit]
    | some answer =>
      simp only [walkExit, popFrom, ha, hs, ↓reduceIte, hc, passOn, joinPushed, passPushed, hstack, FramePop.deliveredExit]

/-- The answering failure handler is skipped under interruption; the remainder of the
walk receives the sanitized cause. This is U-01, checkpoint.exit-failcause-skip. -/
theorem walkExit_preempted (cause interrupted : CauseV) (frame : NCode) (rest : List NCode)
    (fiber : FFiber) (hens : frame.ensure fiber = (fiber, none))
    (hstack : fiber.stack = []) (harm : frame.hasArm .contE = true)
    (hint : fiber.interrupted = true) (hc : fiber.interruptedCause = some interrupted) :
    walkExit (.failure cause) (frame :: rest) fiber =
      walkExit (.failure (Cause.sanitize cause interrupted)) rest fiber := by
  have ha : frame.answerOf .contE none = some (.frame frame) := Prim.answerOf_arm _ _ harm
  simp only [walkExit, demandOf, skipOf, causeOf, popFrom, ha, hens, hint, Bool.true_and,
    ↓reduceIte, skippedCause, harm, hc, BEq.rfl, passOn, joinPushed, passPushed, hstack,
    FramePop.deliveredExit]
  have hp := popFrom_carried_isSome .contE true rest fiber (some (Cause.sanitize cause interrupted))
  cases he : (popFrom .contE true rest fiber
      (some (Cause.sanitize cause interrupted))).carriedCause with
  | none => rw [he] at hp; cases hp
  | some result => rfl

/-- A masking finalizer answers before the interruption skip can fire. -/
theorem walkExit_onExit (ex : ExitV) (body : NCode) (fin : EffName) (rest : List NCode)
    (fiber : FFiber) : walkExit ex (Prim.onExit body fin false :: rest) fiber = ex := by
  cases fiber with
  | mk current stack flag interrupted deferred => cases ex <;> cases flag <;> rfl

theorem walkExit_asyncFinalizer_failure (cause : CauseV) (name : EffName) (rest : List NCode)
    (fiber : FFiber) :
    walkExit (.failure cause) (Prim.asyncFinalizer name :: rest) fiber = .failure cause := by
  cases fiber with
  | mk current stack flag interrupted deferred => cases flag <;> rfl

/-- Restoring a mask passes failures without changing their payload. -/
theorem walkExit_mask_failure (cause : CauseV) (flag : Bool) (rest : List NCode)
    (fiber : FFiber) (hstack : fiber.stack = []) :
    walkExit (.failure cause) (Prim.setInterruptible flag :: rest) fiber =
      walkExit (.failure cause) rest ((Prim.setInterruptible flag : NCode).ensure fiber).fst := by
  cases fiber with
  | mk current stack prior interrupted deferred =>
    dsimp only at hstack
    subst stack
    cases interrupted <;> cases flag <;> rfl



end Effect4.Program.Sched
