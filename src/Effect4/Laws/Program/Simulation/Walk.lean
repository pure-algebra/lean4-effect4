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
      (if interp.loopTest l (interp.loopStep l cursor v) then
        some (interp.loopBody l (interp.loopStep l cursor v),
          [Prim.whileLoop l (interp.loopStep l cursor v)])
      else some (Prim.success (interp.loopDone l), [])) := rfl

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
      popR i (.failure c) T { frame with stack := T } := rfl

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
      popR i (.failure c) T { frame with stack := T } := by
  simp [popR, GuardKind.hasExitArm, hint]

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
      popR i (.failure c) T { frame with stack := T } := by
  simp [popR, GuardKind.hasExitArm, hint]

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
      (if i.loopTest name (i.loopStep name cursor v) then
        ({ frame with
            stack := .loop name (i.loopStep name cursor v) :: T
            current := i.loopBody name (i.loopStep name cursor v) }, none)
      else ({ frame with stack := T, current := .pure (.success (i.loopDone name)) }, none)) := rfl

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
            fiber.deferredInterrupt) := by
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
            fiber.deferredInterrupt) := by
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

/-! ## What the two walks may leave -/

/-- The frame's pop and the term's walk agree: both finish with the exit, or the frame
answers — a substituted failure, the scoped exit callback, an `OnExit` finalizer, or a plain
arm — and the term has installed the related work. -/
inductive WalkRel (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    (cur : RProgram) : NPop → RSaved → Option ExitV → Prop
  | finished {pop : NPop} {frame' : RSaved} (ha : pop.answer = .empty) (hs : pop.fiber.stack = [])
      (hs' : frame'.stack = []) (hi : pop.fiber.interruptible = frame'.interruptible)
      (hc : pop.fiber.interruptedCause = frame'.interruptedCause)
      (hd : pop.fiber.deferredInterrupt = frame'.deferredInterrupt)
      (hcur : frame'.current = cur) :
      WalkRel root completed ex cur pop frame' (some ex)
  | replaced {pop : NPop} {frame' : RSaved} (cause : CauseV)
      (ha : pop.answer = .replacement (Prim.failure cause))
      (hcur : frame'.current = .pure (.failure cause))
      (hst : StackMeans root pop.fiber.stack frame'.stack)
      (hi : pop.fiber.interruptible = frame'.interruptible)
      (hc : pop.fiber.interruptedCause = frame'.interruptedCause)
      (hd : pop.fiber.deferredInterrupt = frame'.deferredInterrupt)
      (hm : MaskInv frame'.interruptible frame'.stack) :
      WalkRel root completed ex cur pop frame' none
  | scopedExit {pop : NPop} {frame' : RSaved} (body : NCode) (previous : Ctx) (scope : Nat)
      (k : ExitV → RProgram)
      (ha : pop.answer = .frame (Prim.onExit body (.scopedExit previous scope) false))
      (hcur : frame'.current = .vis (.inr (.scopeExit previous scope ex)) k) (hk : Delivers k)
      (hst : StackMeans root pop.fiber.stack frame'.stack)
      (hi : pop.fiber.interruptible = frame'.interruptible)
      (hc : pop.fiber.interruptedCause = frame'.interruptedCause)
      (hd : pop.fiber.deferredInterrupt = frame'.deferredInterrupt)
      (hm : MaskInv frame'.interruptible frame'.stack) :
      WalkRel root completed ex cur pop frame' none
  | finalizer {pop : NPop} {frame' : RSaved} (body : NCode) (fin : EffName)
      (ha : pop.answer = .frame (Prim.onExit body fin false))
      (hns : ∀ previous scope, fin ≠ .scopedExit previous scope)
      (hK : ∀ program, (interpAt root completed).finalizerProgram fin ex = some program →
        CodeMeans root (finalizerCodeAt root completed ex program) (prepareR completed frame'.current))
      (hsome : ((interpAt root completed).finalizerProgram fin ex).isSome = true)
      (hst : StackMeans root pop.fiber.stack frame'.stack)
      (hi : pop.fiber.interruptible = frame'.interruptible)
      (hc : pop.fiber.interruptedCause = frame'.interruptedCause)
      (hd : pop.fiber.deferredInterrupt = frame'.deferredInterrupt)
      (hm : MaskInv frame'.interruptible frame'.stack) :
      WalkRel root completed ex cur pop frame' none
  | arm {pop : NPop} {frame' : RSaved} (fr : NCode) (ha : pop.answer = .frame fr)
      (hnot : ∀ body fin flag, fr ≠ Prim.onExit body fin flag)
      (harm : ∀ next pushed,
        armOf (interpAt root completed).toPrimInterp ex fr = some (next, pushed) →
          CodeMeans root next (prepareR completed frame'.current) ∧
            StackMeans root (pushed ++ pop.fiber.stack) frame'.stack)
      (hsome : (armOf (interpAt root completed).toPrimInterp ex fr).isSome = true)
      (hi : pop.fiber.interruptible = frame'.interruptible)
      (hc : pop.fiber.interruptedCause = frame'.interruptedCause)
      (hd : pop.fiber.deferredInterrupt = frame'.deferredInterrupt)
      (hm : MaskInv frame'.interruptible frame'.stack) :
      WalkRel root completed ex cur pop frame' none

/-- The relation reads only the pop's answer and fiber. -/
theorem WalkRel.of_eq {root : NativeEff} {completed : List (FiberId × ExitV)} {ex : ExitV}
    {cur : RProgram} {pop pop' : NPop} {frame' : RSaved} {done : Option ExitV}
    (ha : pop'.answer = pop.answer) (hf : pop'.fiber = pop.fiber)
    (h : WalkRel root completed ex cur pop frame' done) :
    WalkRel root completed ex cur pop' frame' done := by
  cases h with
  | finished ha' hs hs' hi hc hd hcur =>
    exact .finished (ha.trans ha') (by rw [hf]; exact hs) hs' (by rw [hf]; exact hi)
      (by rw [hf]; exact hc) (by rw [hf]; exact hd) hcur
  | replaced cause ha' hcur hst hi hc hd hm =>
    exact .replaced cause (ha.trans ha') hcur (by rw [hf]; exact hst) (by rw [hf]; exact hi)
      (by rw [hf]; exact hc) (by rw [hf]; exact hd) hm
  | scopedExit body previous scope k ha' hcur hk hst hi hc hd hm =>
    exact .scopedExit body previous scope k (ha.trans ha') hcur hk (by rw [hf]; exact hst)
      (by rw [hf]; exact hi) (by rw [hf]; exact hc) (by rw [hf]; exact hd) hm
  | finalizer body fin ha' hns hK hsome hst hi hc hd hm =>
    exact .finalizer body fin (ha.trans ha') hns hK hsome (by rw [hf]; exact hst)
      (by rw [hf]; exact hi) (by rw [hf]; exact hc) (by rw [hf]; exact hd) hm
  | arm fr ha' hnot harm hsome hi hc hd hm =>
    exact .arm fr (ha.trans ha') hnot
      (fun next pushed h => ⟨(harm next pushed h).1, by rw [hf]; exact (harm next pushed h).2⟩)
      hsome (by rw [hf]; exact hi) (by rw [hf]; exact hc) (by rw [hf]; exact hd) hm

theorem toPrimInterp_contA (i : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (n : EffName) (v : Val) : i.toPrimInterp.contA n v = i.contA n v := rfl

theorem toPrimInterp_contE (i : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (n : EffName) (c : CauseV) : i.toPrimInterp.contE n c = i.contE n c := rfl

theorem toPrimInterp_iterNext (i : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (n : EffName) (v : Val) : i.toPrimInterp.iterNext n v = i.iterNext n v := rfl

/-! ## The mask slot -/

/-- The mask frame and the term's mask slot (restoring or a finalizer's): the same flag is
restored, and a pending cause substitutes the failure exactly on a success. -/
theorem walk_mask (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    (cur : RProgram) {S' : List NCode} {T' : List ScopeFrame} (rest : StackMeans root S' T')
    (ih : ∀ (fiber : FFiber) (frame : RSaved), fiber.stack = [] →
      fiber.interruptible = frame.interruptible → fiber.interruptedCause = frame.interruptedCause →
      fiber.deferredInterrupt = frame.deferredInterrupt → MaskInv frame.interruptible T' →
      frame.current = cur →
      WalkRel root completed ex cur (popFrom (demandOf ex) (skipOf ex) S' fiber)
        (popR (interpRAt root completed) ex T' frame).1 (popR (interpRAt root completed) ex T' frame).2)
    (flag : Bool) (s : ScopeFrame) (hs : s = .restoreMask flag ∨ s = .finalizerMask flag)
    (fiber : FFiber) (frame : RSaved) (hstack : fiber.stack = [])
    (hi : fiber.interruptible = frame.interruptible)
    (hc : fiber.interruptedCause = frame.interruptedCause)
    (hd : fiber.deferredInterrupt = frame.deferredInterrupt) (hm : MaskInv flag T')
    (hcur : frame.current = cur) :
    WalkRel root completed ex cur
      (popFrom (demandOf ex) (skipOf ex) (Prim.setInterruptible flag :: S') fiber)
      (popR (interpRAt root completed) ex (s :: T') frame).1
      (popR (interpRAt root completed) ex (s :: T') frame).2 := by
  rw [popR_mask _ _ _ ex flag s hs]
  have hpush : ((Prim.setInterruptible flag : NCode).ensure fiber).fst.stack = fiber.stack :=
    Prim.ensure_setInterruptible_stack flag fiber
  have hmissing : (Prim.setInterruptible flag : NCode).hasArm (demandOf ex) = false := by
    cases ex <;> rfl
  have hstack' : ((Prim.setInterruptible flag : NCode).ensure fiber).fst.stack = [] := by
    rw [hpush, hstack]
  have hi' : ((Prim.setInterruptible flag : NCode).ensure fiber).fst.interruptible =
      ({ frame with stack := T', interruptible := flag } : RSaved).interruptible :=
    Prim.ensure_setInterruptible_flag flag fiber
  have hd' : ((Prim.setInterruptible flag : NCode).ensure fiber).fst.deferredInterrupt =
      ({ frame with stack := T', interruptible := flag } : RSaved).deferredInterrupt := by
    rw [ensure_mask_deferred]; exact hd
  cases hcause : frame.interruptedCause with
  | none =>
    have hens := Prim.ensure_setInterruptible_no_pending flag fiber (hc.trans hcause)
    have hp := popFrom_plain_pass (demandOf ex) (skipOf ex) (f := Prim.setInterruptible flag)
      (rest := S') (fiber := fiber) hpush
      (Or.inl (by rw [hens]; exact Prim.answerOf_missing _ _ hmissing)) hstack
    exact WalkRel.of_eq hp.1 hp.2
      (ih _ _ hstack' hi' (by rw [ensure_mask_cause]; exact hc.trans hcause) hd' hm hcur)
  | some cause =>
    cases flag with
    | false =>
      have hens := Prim.ensure_setInterruptible_false_no_replacement (ν := EffName) (σ := EffThunk)
        (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) fiber
      have hp := popFrom_plain_pass (demandOf ex) (skipOf ex) (f := Prim.setInterruptible false)
        (rest := S') (fiber := fiber) hpush
        (Or.inl (by rw [hens]; exact Prim.answerOf_missing _ _ hmissing)) hstack
      exact WalkRel.of_eq hp.1 hp.2
        (ih _ _ hstack' hi' (by rw [ensure_mask_cause]; exact hc.trans hcause) hd' hm hcur)
    | true =>
      have hens := Prim.ensure_setInterruptible_substitutes cause fiber (hc.trans hcause)
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hanswer : (Prim.setInterruptible true : NCode).answerOf .contA
            ((Prim.setInterruptible true : NCode).ensure fiber).snd =
            some (.replacement (Prim.failure cause)) := by
          rw [hens]; rfl
        have hskip : (false && ((Prim.setInterruptible true : NCode).ensure fiber).fst.interrupted) =
            false := rfl
        have hp₁ := popFrom_answer_answer .contA false _ S' fiber _ hanswer hskip
        have hp₂ := popFrom_answer_fiber .contA false _ S' fiber _ hanswer hskip
        rw [hens] at hp₂
        simp only [failingOf, Bool.not_false, Bool.and_true, ↓reduceIte]
        refine WalkRel.replaced cause hp₁ rfl ?_ ?_ ?_ ?_ hm
        · rw [hp₂]; simp only [hstack, List.nil_append]; exact rest
        · rw [hp₂]
        · rw [hp₂]; exact hc.trans hcause
        · rw [hp₂]; exact hd
      | failure c =>
        simp only [demandOf, skipOf]
        have hskip : (true && ((Prim.setInterruptible true : NCode).ensure fiber).fst.interrupted) =
            true := by
          rw [hens]; simp [FrameFiber.interrupted, hc, hcause]
        have hp := popFrom_plain_pass .contE true (f := Prim.setInterruptible true) (rest := S')
          (fiber := fiber) hpush (Or.inr hskip) hstack
        simp only [failingOf, Bool.not_true, Bool.and_false]
        exact WalkRel.of_eq hp.1 hp.2
          (ih _ _ hstack' hi' (by rw [ensure_mask_cause]; exact hc.trans hcause) hd' hm hcur)

/-! ## The walk -/

/-- **The two walks agree.** -/
theorem walk_rel (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    (cur : RProgram) :
    ∀ {S : List NCode} {T : List ScopeFrame}, StackMeans root S T →
    ∀ (fiber : FFiber) (frame : RSaved), fiber.stack = [] →
      fiber.interruptible = frame.interruptible → fiber.interruptedCause = frame.interruptedCause →
      fiber.deferredInterrupt = frame.deferredInterrupt → MaskInv frame.interruptible T →
      frame.current = cur →
      WalkRel root completed ex cur (popFrom (demandOf ex) (skipOf ex) S fiber)
        (popR (interpRAt root completed) ex T frame).1
        (popR (interpRAt root completed) ex T frame).2 := by
  intro S T h
  induction h with
  | nil =>
    intro fiber frame hstack hi hc hd _ hcur
    exact WalkRel.finished rfl hstack rfl hi hc hd hcur
  | @slot f s S' T' hs rest ih =>
    intro fiber frame hstack hi hc hd hm hcur
    -- the frame's skip test agrees with the term's interruption test
    have hint : (fiber.interruptible && fiber.interruptedCause.isSome) =
        (frame.interruptible && frame.interruptedCause.isSome) := by rw [hi, hc]
    cases hs with
    | onSuccess body n K hK =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_answer .contA false (f := Prim.onSuccess body n) (rest := S')
          rfl rfl rfl hstack
        rw [popR_resume_onSuccess]
        refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
          (by rw [hp.2]; exact hd) hm
        intro next pushed harm
        rw [armOf_onSuccess, toPrimInterp_contA, interpAt_contA] at harm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
        exact ⟨hK completed v, by rw [hp.2]; exact rest⟩
      | failure c =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_pass .contE true (f := Prim.onSuccess body n) (rest := S')
          (fiber := fiber) rfl (Or.inl (Prim.answerOf_missing _ _ rfl)) hstack
        rw [popR_resume_onSuccess_fail]
        exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | onSuccessConst body next K hK =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_answer .contA false (f := Prim.onSuccessConst body next) (rest := S')
          rfl rfl rfl hstack
        rw [popR_resume_onSuccess]
        refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
          (by rw [hp.2]; exact hd) hm
        intro next' pushed harm
        rw [armOf_onSuccessConst] at harm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
        exact ⟨hK completed v, by rw [hp.2]; exact rest⟩
      | failure c =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_pass .contE true (f := Prim.onSuccessConst body next) (rest := S')
          (fiber := fiber) rfl (Or.inl (Prim.answerOf_missing _ _ rfl)) hstack
        rw [popR_resume_onSuccess_fail]
        exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | onFailure body n K hK =>
      cases ex with
      | success v =>
        have hp := popFrom_plain_pass .contA false (f := Prim.onFailure body n) (rest := S')
          (fiber := fiber) rfl (Or.inl (Prim.answerOf_missing _ _ rfl)) hstack
        rw [popR_resume_onFailure_succ]
        exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
      | failure c =>
        simp only [demandOf, skipOf]
        rcases hb : (frame.interruptible && frame.interruptedCause.isSome) with _ | _
        · have hp := popFrom_plain_answer .contE true (f := Prim.onFailure body n) (rest := S')
            rfl rfl (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = false; rw [Bool.true_and, hint, hb]) hstack
          rw [popR_resume_onFailure _ _ _ _ _ hb]
          refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          intro next pushed harm
          rw [armOf_onFailure, toPrimInterp_contE, interpAt_contE] at harm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
          exact ⟨hK completed c, by rw [hp.2]; exact rest⟩
        · have hp := popFrom_plain_pass .contE true (f := Prim.onFailure body n) (rest := S')
            (fiber := fiber) rfl
            (Or.inr (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = true; rw [Bool.true_and, hint, hb])) hstack
          rw [popR_resume_onFailure_skip _ _ _ _ _ hb]
          exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | onBoth body a e K hA hE =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_answer .contA false (f := Prim.onSuccessAndFailure body a e)
          (rest := S') rfl rfl rfl hstack
        rw [popR_resume_all_succ]
        refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
          (by rw [hp.2]; exact hd) hm
        intro next pushed harm
        rw [armOf_onBoth_succ, toPrimInterp_contA, interpAt_contA] at harm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
        exact ⟨hA completed v, by rw [hp.2]; exact rest⟩
      | failure c =>
        simp only [demandOf, skipOf]
        rcases hb : (frame.interruptible && frame.interruptedCause.isSome) with _ | _
        · have hp := popFrom_plain_answer .contE true (f := Prim.onSuccessAndFailure body a e)
            (rest := S') rfl rfl
            (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = false; rw [Bool.true_and, hint, hb]) hstack
          rw [popR_resume_all _ _ _ _ _ hb]
          refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          intro next pushed harm
          rw [armOf_onBoth_fail, toPrimInterp_contE, interpAt_contE] at harm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
          exact ⟨hE completed c, by rw [hp.2]; exact rest⟩
        · have hp := popFrom_plain_pass .contE true (f := Prim.onSuccessAndFailure body a e)
            (rest := S') (fiber := fiber) rfl
            (Or.inr (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = true; rw [Bool.true_and, hint, hb])) hstack
          rw [popR_resume_all_skip _ _ _ _ _ hb]
          exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | exitFrame body K hK =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_answer .contA false (f := Prim.exitFrame body) (rest := S')
          rfl rfl rfl hstack
        rw [popR_resume_all_succ]
        refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
          (by rw [hp.2]; exact hd) hm
        intro next pushed harm
        rw [armOf_exitFrame] at harm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
        exact ⟨hK completed (.success v), by rw [hp.2]; exact rest⟩
      | failure c =>
        simp only [demandOf, skipOf]
        rcases hb : (frame.interruptible && frame.interruptedCause.isSome) with _ | _
        · have hp := popFrom_plain_answer .contE true (f := Prim.exitFrame body) (rest := S')
            rfl rfl
            (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = false; rw [Bool.true_and, hint, hb]) hstack
          rw [popR_resume_all _ _ _ _ _ hb]
          refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          intro next pushed harm
          rw [armOf_exitFrame] at harm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
          exact ⟨hK completed (.failure c), by rw [hp.2]; exact rest⟩
        · have hp := popFrom_plain_pass .contE true (f := Prim.exitFrame body) (rest := S')
            (fiber := fiber) rfl
            (Or.inr (by show (true && (fiber.interruptible && fiber.interruptedCause.isSome)) = true; rw [Bool.true_and, hint, hb])) hstack
          rw [popR_resume_all_skip _ _ _ _ _ hb]
          exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | onExit body fin K hK hsome_prog =>
      have hp := popFrom_onExit (demandOf ex) (skipOf ex) body fin S' fiber hstack
      rw [popR_resume_onExit]
      refine WalkRel.finalizer body fin hp.1 ?_ (fun program hprog => hK completed ex program hprog)
        (hsome_prog completed ex) ?_ (by rw [hp.2]) (by rw [hp.2]; exact hc) (by rw [hp.2]; exact hd)
        ⟨rfl, hm⟩
      · intro previous scope heq
        subst heq
        have := hsome_prog completed ex
        simp [interpAt, interpOf] at this
      · rw [hp.2, ← hi]
        cases fiber.interruptible
        · exact StackMeans.finMaskFalse rest
        · exact StackMeans.finMaskTrue rest
    | scopedFrame body previous scope K k hk hK =>
      have hp := popFrom_onExit (demandOf ex) (skipOf ex) body (.scopedExit previous scope) S' fiber hstack
      rw [popR_resume_onExit]
      refine WalkRel.scopedExit body previous scope k hp.1 (hK ex) hk ?_ (by rw [hp.2])
        (by rw [hp.2]; exact hc) (by rw [hp.2]; exact hd) ⟨rfl, hm⟩
      rw [hp.2, ← hi]
      cases fiber.interruptible
      · exact StackMeans.finMaskFalse rest
      · exact StackMeans.finMaskTrue rest
    | iterator g cursor =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_answer .contA false (f := Prim.iterator g cursor) (rest := S')
          rfl rfl rfl hstack
        rw [popR_iter_succ]
        have hstep := (iterNext_means root completed g v).2
        generalize hs₁ : ((interpAt root completed).iterNext g v).2 = s₁ at hstep
        generalize hs₂ : ((interpRAt root completed).iterNext g v).2 = s₂ at hstep ⊢
        cases hstep with
        | done r =>
          refine WalkRel.arm _ hp.1 (by nofun) ?_ ?_ (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          · intro next pushed harm
            rw [armOf_iterator, toPrimInterp_iterNext, hs₁] at harm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
            exact ⟨CodeMeans.success r, by rw [hp.2]; exact rest⟩
          · rw [armOf_iterator, toPrimInterp_iterNext, hs₁]; rfl
        | halt c =>
          refine WalkRel.arm _ hp.1 (by nofun) ?_ ?_ (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          · intro next pushed harm
            rw [armOf_iterator, toPrimInterp_iterNext, hs₁] at harm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
            exact ⟨CodeMeans.failure c, by rw [hp.2]; exact rest⟩
          · rw [armOf_iterator, toPrimInterp_iterNext, hs₁]; rfl
        | resume name hcode =>
          refine WalkRel.arm _ hp.1 (by nofun) ?_ ?_ (by rw [hp.2]; exact hi) (by rw [hp.2]; exact hc)
            (by rw [hp.2]; exact hd) hm
          · intro next pushed harm
            rw [armOf_iterator, toPrimInterp_iterNext, hs₁] at harm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
            exact ⟨hcode.prepare completed,
              by rw [hp.2]; exact StackMeans.slot (SlotMeans.iterator name cursor) rest⟩
          · rw [armOf_iterator, toPrimInterp_iterNext, hs₁]; rfl
      | failure c =>
        simp only [demandOf, skipOf]
        have hp := popFrom_plain_pass .contE true (f := Prim.iterator g cursor) (rest := S')
          (fiber := fiber) rfl (Or.inl (Prim.answerOf_missing _ _ rfl)) hstack
        rw [popR_iter_fail]
        exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | whileLoop p p' cursor hp =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        have hp0 := popFrom_plain_answer .contA false (f := Prim.whileLoop (.loop p') cursor)
          (rest := S') rfl rfl rfl hstack
        rw [popR_loop_succ, loopTest_eq, loopStep_eq, ← loopTest_congr root completed hp,
          ← loopStep_congr root completed hp]
        by_cases ht : (interpAt root completed).loopTest (.loop p')
            ((interpAt root completed).loopStep (.loop p') cursor v) = true
        · rw [if_pos ht]
          refine WalkRel.arm _ hp0.1 (by nofun) ?_ ?_ (by rw [hp0.2]; exact hi)
            (by rw [hp0.2]; exact hc) (by rw [hp0.2]; exact hd) hm
          · intro next pushed harm
            rw [armOf_whileLoop] at harm
            simp only [ht] at harm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
            exact ⟨(loopBody_means' root completed hp _).prepare completed,
              by rw [hp0.2]; exact StackMeans.slot (SlotMeans.whileLoop p p' _ hp) rest⟩
          · rw [armOf_whileLoop]; simp only [ht]; rfl
        · rw [if_neg ht]
          refine WalkRel.arm _ hp0.1 (by nofun) ?_ ?_ (by rw [hp0.2]; exact hi)
            (by rw [hp0.2]; exact hc) (by rw [hp0.2]; exact hd) hm
          · intro next pushed harm
            rw [armOf_whileLoop] at harm
            simp only [ht] at harm
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
            exact ⟨CodeMeans.success _, by rw [hp0.2]; exact rest⟩
          · rw [armOf_whileLoop]; simp only [ht]; rfl
      | failure c =>
        simp only [demandOf, skipOf]
        have hp0 := popFrom_plain_pass .contE true (f := Prim.whileLoop (.loop p') cursor)
          (rest := S') (fiber := fiber) rfl (Or.inl (Prim.answerOf_missing _ _ rfl)) hstack
        rw [popR_loop_fail]
        exact WalkRel.of_eq hp0.1 hp0.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
    | mask flag =>
      exact walk_mask root completed ex cur rest ih flag (.restoreMask flag) (Or.inl rfl) fiber frame
        hstack hi hc hd hm hcur
    | asyncFinalizer name =>
      cases ex with
      | success v =>
        simp only [demandOf, skipOf]
        cases hflag : fiber.interruptible with
        | true =>
          have hp := popFrom_asyncFinalizer_succ name S' fiber hstack hflag
          cases hcause : fiber.interruptedCause with
          | some cause =>
            have hb : (frame.interruptible && frame.interruptedCause.isSome) = true := by
              rw [← hint, hflag, hcause]; rfl
            rw [popR_asyncFinalizer_succ _ _ _ _ _ hb]
            have hq := hp.1 cause hcause
            refine WalkRel.replaced cause hq.1 ?_ ?_ (by rw [hq.2, ← hi, hflag]) (by rw [hq.2]; exact hc)
              (by rw [hq.2]; exact hd) hm
            · show Effects.Program.pure (Exit.failure frame.pendingCause) = _
              rw [← pendingCause_eq hc]
              simp [FrameFiber.pendingCause, hcause]
            · rw [hq.2]; exact rest
          | none =>
            have hb : (frame.interruptible && frame.interruptedCause.isSome) = false := by
              rw [← hint, hcause]; simp
            rw [popR_asyncFinalizer_succ_pass _ _ _ _ _ hb]
            have hq := hp.2 hcause
            exact WalkRel.of_eq hq.1 hq.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
        | false =>
          have hb : (frame.interruptible && frame.interruptedCause.isSome) = false := by
            rw [← hint, hflag]; rfl
          rw [popR_asyncFinalizer_succ_pass _ _ _ _ _ hb]
          have hens := Prim.ensure_asyncFinalizer_already_masked name fiber hflag
          have hp := popFrom_plain_pass .contA false (f := Prim.asyncFinalizer name) (rest := S')
            (fiber := fiber) (by rw [hens])
            (Or.inl (by rw [hens]; exact Prim.answerOf_missing _ _ (Prim.hasArm_asyncFinalizer_contA_false name)))
            hstack
          rw [hens] at hp
          exact WalkRel.of_eq hp.1 hp.2 (ih fiber { frame with stack := T' } hstack hi hc hd hm hcur)
      | failure c =>
        simp only [demandOf, skipOf]
        have hp := popFrom_asyncFinalizer_fail name S' fiber hstack
        rw [popR_asyncFinalizer_fail]
        refine WalkRel.arm _ hp.1 (by nofun) ?_ rfl (by rw [hp.2]) (by rw [hp.2]; exact hc)
          (by rw [hp.2]; exact hd) ?_
        · intro next pushed harm
          rw [armOf_asyncFinalizer] at harm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj harm)
          refine ⟨?_, ?_⟩
          · by_cases hint' : c.hasInterrupts = true
            · simp only [hint', ↓reduceIte]
              exact (cancelThenFail_means root name c).prepare completed
            · simp only [hint', Bool.false_eq_true, ↓reduceIte]
              exact CodeMeans.failure c
          · rw [hp.2, ← hi]
            cases fiber.interruptible
            · exact rest
            · exact StackMeans.slot (SlotMeans.mask true) rest
        · show MaskInv false (if frame.interruptible then .restoreMask true :: T' else T')
          cases hfl : frame.interruptible
          · rw [hfl] at hm; exact hm
          · rw [hfl] at hm; exact hm
  | @answer S' T' next hd' rest ih =>
    intro fiber frame hstack hi hc hd hm hcur
    rw [popR_answer]
    rcases hd' ex with h1 | ⟨k', h1⟩
    · rw [h1]; exact ih fiber { frame with stack := T' } hstack hi hc hd hm hcur
    · rw [h1]; exact ih fiber { frame with stack := T' } hstack hi hc hd hm hcur
  | @finMaskTrue S' T' rest ih =>
    intro fiber frame hstack hi hc hd hm hcur
    exact walk_mask root completed ex cur rest ih true (.finalizerMask true) (Or.inr rfl) fiber frame
      hstack hi hc hd hm.2 hcur
  | @finMaskFalse S' T' rest ih =>
    intro fiber frame hstack hi hc hd hm hcur
    rw [popR_mask_false _ _ _ ex (.finalizerMask false) (Or.inr rfl)]
    exact ih fiber { frame with stack := T', interruptible := false } hstack (hi.trans hm.1) hc hd hm.2
      hcur

end Effect4.Program.Sched
