import Effect4.Runtime.Runtime

/-!
# Live continuation-stack traversal

The independent packet in `test/contracts/live-stack.contract.md` owns the
additive public surface. The primitive, fiber, result and event carriers
remain owned by `Runtime.lean`. Every recursive call consumes the actual
post-hook stack; the existing detached traversal occurs only in proofs.
-/

set_option autoImplicit false

namespace Effect4.FrameFiber
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

private def prefixPop (frame : Prim ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (result : FramePop ν σ β ε δ ι α) : FramePop ν σ β ε δ ι α :=
  { result with popped := frame :: result.popped, events := events ++ result.events }

-- OWED: `continuing_stack` --- "a frame that does not answer leaves the stack
-- alone" --- is genuinely false once `AsyncFinalizer` exists, and is therefore
-- left out rather than restated. On a `contA` demand `AsyncFinalizer` declares
-- no arm, so it passes, and its `contAll` has already pushed
-- `SetInterruptible(true)` (`internal/effect.ts:1149-1154`): a passing frame
-- can grow the stack. It was private and only ever carried the traversal's
-- decreasing argument and two proof steps; `live_measure_lt` below replaces the
-- first and `Runtime.ensure_stack_cases` the other two. No public statement of
-- `test/contracts/live-stack.contract.md` depended on it.

/-- `Runtime.ensure_stack_cases` as the live traversal's decreasing step: a hook
pushes at most one frame and can only do so by clearing the interruptible flag
it found set, so two per frame plus one while the fiber is interruptible
strictly decreases across every hook. -/
private theorem live_measure_lt (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    2 * (frame.ensure fiber).fst.stack.length +
        (if (frame.ensure fiber).fst.interruptible = true then 1 else 0) <
      2 * fiber.stack.length + 2 + (if fiber.interruptible = true then 1 else 0) := by
  rcases ensure_stack_cases frame fiber with h | ⟨hpush, hflag, hafter⟩
  · rw [h]
    split <;> split <;> omega
  · rw [hpush, hafter, hflag]
    simp <;> omega

/-- Consume the actual stack left by each hook, testing interruption after
that hook. A hook may grow the stack -- `AsyncFinalizer` and a masking `OnExit`
push the restoring `SetInterruptible(true)` -- so the traversal decreases on
`live_measure_lt`, not on the stack length alone.
census: rule.frames-are-primitives -/
def popLive (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool) :
    FramePop ν σ β ε δ ι α :=
  match _stackEq : self.stack with
  | [] => ⟨.empty, [], [], self⟩
  | frame :: rest =>
    let after := frame.ensure { self with stack := rest }
    match _answerEq : frame.answerOf demand after.snd with
    | none => prefixPop frame (frame.passEvents after.snd) (popLive after.fst demand skip)
    | some answer =>
      if _skipping : skip && after.fst.interrupted then
        prefixPop frame (frame.passEvents after.snd) (popLive after.fst demand skip)
      else ⟨answer, [frame], frame.passEvents after.snd, after.fst⟩
termination_by 2 * self.stack.length + (if self.interruptible = true then 1 else 0)
decreasing_by
  all_goals
    have step := live_measure_lt frame { self with stack := rest }
    simp only [_stackEq, List.length_cons] at step ⊢
    omega

/-- Observe deferred interruption before the outer loop decides whether to
discard its answer. Even a discarded answer retains its event.
census: checkpoint.getcont-deferred -/
def getContLive (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (skipInterrupted : Bool) : FramePop ν σ β ε δ ι α :=
  let cleared := { self with deferredInterrupt := false }
  if self.deferredInterrupt then
    if skipInterrupted && self.interrupted then
      let next := cleared.popLive demand skipInterrupted
      { next with events := .deferred self.pendingCause :: next.events }
    else ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause], cleared⟩
  else cleared.popLive demand skipInterrupted

private def appendStack (fiber : FrameFiber ν σ β ε δ ι α)
    (suffix : List (Prim ν σ β ε δ ι α)) : FrameFiber ν σ β ε δ ι α :=
  { fiber with stack := fiber.stack ++ suffix }

private theorem interrupted_appendStack (fiber : FrameFiber ν σ β ε δ ι α)
    (suffix : List (Prim ν σ β ε δ ι α)) :
    (appendStack fiber suffix).interrupted = fiber.interrupted := rfl

private theorem ensure_appendStack (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (suffix : List (Prim ν σ β ε δ ι α)) :
    frame.ensure (appendStack fiber suffix) =
      (appendStack (frame.ensure fiber).fst suffix, (frame.ensure fiber).snd) := by
  cases frame <;> try rfl
  case onExit body name flag =>
    cases mask : fiber.interruptible <;> cases flag <;>
      simp [Prim.ensure, appendStack, mask]
  case asyncFinalizer name =>
    cases mask : fiber.interruptible <;>
      simp [Prim.ensure, appendStack, mask]
  case setInterruptible flag =>
    cases cause : fiber.interruptedCause <;> cases flag <;>
      simp [Prim.ensure, appendStack, cause]

private theorem clear_empty_stack (fiber : FrameFiber ν σ β ε δ ι α)
    (empty : fiber.stack = []) : { fiber with stack := [] } = fiber := by
  cases fiber
  cases empty
  rfl

private theorem with_stack_self (fiber : FrameFiber ν σ β ε δ ι α) :
    { fiber with stack := fiber.stack } = fiber := by
  cases fiber
  rfl

/-- The detached loop's pass step as a whole result, not field by field. -/
private theorem popFrom_pass (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (continues : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    popFrom demand skip (frame :: rest) fiber =
      passOn frame (frame.ensure fiber).snd (continueFrom demand skip frame rest fiber) := by
  rcases continues with hnone | hskip
  · simp [popFrom, continueFrom, hnone]
  · cases hanswer : frame.answerOf demand (frame.ensure fiber).snd with
    | none => simp [popFrom, continueFrom, hanswer]
    | some answer => simp [popFrom, continueFrom, hanswer, hskip]

/-- A hook that pushed nothing: the detached loop simply continues on the frames
that were left, which is `Runtime.popFrom_pass_no_push` read through the scratch
stack. -/
private theorem popFrom_scratch_nil (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
    (_detachedEmpty : fiber.stack = [])
    (empty : (frame.ensure fiber).fst.stack = []) :
    popFrom demand skip ((frame.ensure fiber).fst.stack ++ rest)
        { (frame.ensure fiber).fst with stack := [] } =
      continueFrom demand skip frame rest fiber := by
  have drained := passPushed_nil demand skip (frame.ensure fiber).fst empty
  unfold continueFrom
  rw [joinPushed_of_empty demand skip (frame.ensure fiber).fst rest _ (by rw [drained]),
    drained, empty, List.nil_append, clear_empty_stack (frame.ensure fiber).fst empty]
  simp

private theorem answer_nonempty (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) (answer : ContAnswer ν σ β ε δ ι α)
    (selected : frame.answerOf demand replacement = some answer) : answer ≠ .empty := by
  intro empty
  subst answer
  cases replacement <;> cases arm : frame.hasArm demand <;>
    simp [Prim.answerOf, arm] at selected
/-- A hook that pushed the restoring frame: the detached loop pops that frame
next, and that is exactly the frame `passPushed` drains, so the two agree. -/
private theorem popFrom_scratch_one (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
    (pushed : (frame.ensure fiber).fst.stack = [Prim.setInterruptible true]) :
    popFrom demand skip ((frame.ensure fiber).fst.stack ++ rest)
        { (frame.ensure fiber).fst with stack := [] } =
      continueFrom demand skip frame rest fiber := by
  have hook : FrameFiber ν σ β ε δ ι α := (frame.ensure fiber).fst
  have hgstack : ({ (frame.ensure fiber).fst with
      stack := ([] : List (Prim ν σ β ε δ ι α)) }).stack = [] := rfl
  have hsiStack : ((Prim.setInterruptible true : Prim ν σ β ε δ ι α).ensure
        { (frame.ensure fiber).fst with stack := [] }).fst.stack =
      ({ (frame.ensure fiber).fst with stack := [] }).stack :=
    Prim.ensure_setInterruptible_stack true _
  have hdrainAnswer := passPushed_answer demand skip (frame.ensure fiber).fst
    (Prim.setInterruptible true) [] pushed
  have hdrainPopped := passPushed_popped demand skip (frame.ensure fiber).fst
    (Prim.setInterruptible true) [] pushed
  have hdrainEvents := passPushed_events demand skip (frame.ensure fiber).fst
    (Prim.setInterruptible true) [] pushed
  have hdrainFiber := passPushed_fiber demand skip (frame.ensure fiber).fst
    (Prim.setInterruptible true) [] pushed
  unfold continueFrom
  rw [pushed, List.singleton_append]
  cases selected : Prim.answerOf (Prim.setInterruptible true) demand
      ((Prim.setInterruptible true : Prim ν σ β ε δ ι α).ensure
        { (frame.ensure fiber).fst with stack := [] }).snd with
  | none =>
    have hempty : (passPushed demand skip (frame.ensure fiber).fst).answer =
        ContAnswer.empty := by
      rw [hdrainAnswer, selected]
    rw [popFrom_pass demand skip (Prim.setInterruptible true) rest _ (Or.inl selected),
      popFrom_pass_no_push demand skip (Prim.setInterruptible true) rest _ hgstack hsiStack,
      joinPushed_of_empty demand skip (frame.ensure fiber).fst rest _ hempty,
      hdrainPopped, hdrainEvents, hdrainFiber]
    rfl
  | some answer =>
    cases guard : skip && ((Prim.setInterruptible true : Prim ν σ β ε δ ι α).ensure
        { (frame.ensure fiber).fst with stack := [] }).fst.interrupted with
    | true =>
      have hempty : (passPushed demand skip (frame.ensure fiber).fst).answer =
          ContAnswer.empty := by
        rw [hdrainAnswer, selected]
        simp [guard]
      rw [popFrom_pass demand skip (Prim.setInterruptible true) rest _ (Or.inr guard),
        popFrom_pass_no_push demand skip (Prim.setInterruptible true) rest _ hgstack hsiStack,
        joinPushed_of_empty demand skip (frame.ensure fiber).fst rest _ hempty,
        hdrainPopped, hdrainEvents, hdrainFiber]
      rfl
    | false =>
      have hne : answer ≠ ContAnswer.empty :=
        answer_nonempty (Prim.setInterruptible true) demand _ answer selected
      have hans : (passPushed demand skip (frame.ensure fiber).fst).answer = answer := by
        rw [hdrainAnswer, selected]
        simp [guard]
      rw [joinPushed_of_answer demand skip (frame.ensure fiber).fst rest _ answer hne hans,
        hdrainPopped, hdrainEvents, hdrainFiber]
      simp [popFrom, selected, guard]

private theorem popLive_stack_eq_aux (demand : Arm) (skip : Bool) :
    forall (fuel : Nat) (stack : List (Prim ν σ β ε δ ι α))
      (fiber : FrameFiber ν σ β ε δ ι α),
      2 * stack.length + (if fiber.interruptible = true then 1 else 0) ≤ fuel ->
        popLive { fiber with stack := stack } demand skip =
          popFrom demand skip stack { fiber with stack := [] } := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack fiber bound
    cases stack with
    | nil => rw [popLive]; rfl
    | cons frame rest =>
      exact absurd bound (by simp only [List.length_cons]; omega)
  | succ fuel ih =>
    intro stack fiber bound
    cases stack with
    | nil => rw [popLive]; rfl
    | cons frame rest =>
      have hook : frame.ensure { fiber with stack := rest } =
          (appendStack (frame.ensure { fiber with stack := [] }).fst rest,
            (frame.ensure { fiber with stack := [] }).snd) := by
        simpa [appendStack] using ensure_appendStack frame { fiber with stack := [] } rest
      have step := live_measure_lt frame { fiber with stack := rest }
      rw [hook] at step
      have tailBound :
          2 * (appendStack (frame.ensure { fiber with stack := [] }).fst rest).stack.length +
            (if (appendStack (frame.ensure { fiber with stack := [] }).fst rest).interruptible
              = true then 1 else 0) ≤ fuel := by
        simp only [List.length_cons] at bound
        simp only [appendStack, List.length_append] at step ⊢
        omega
      have tail := ih (appendStack (frame.ensure { fiber with stack := [] }).fst rest).stack
        (appendStack (frame.ensure { fiber with stack := [] }).fst rest) tailBound
      rw [with_stack_self (appendStack (frame.ensure { fiber with stack := [] }).fst rest)]
        at tail
      have split : popFrom demand skip
            (appendStack (frame.ensure { fiber with stack := [] }).fst rest).stack
            { appendStack (frame.ensure { fiber with stack := [] }).fst rest with stack := [] } =
          continueFrom demand skip frame rest { fiber with stack := [] } := by
        show popFrom demand skip
            ((frame.ensure { fiber with stack := [] }).fst.stack ++ rest)
            { (frame.ensure { fiber with stack := [] }).fst with stack := [] } = _
        rcases ensure_stack_cases frame { fiber with stack := [] } with hnone | ⟨hpush, _, _⟩
        · exact popFrom_scratch_nil demand skip frame { fiber with stack := [] } rest rfl
            (by rw [hnone])
        · exact popFrom_scratch_one demand skip frame { fiber with stack := [] } rest
            (by rw [hpush])
      rw [popLive]
      dsimp only
      rw [hook]
      cases answer : frame.answerOf demand (frame.ensure { fiber with stack := [] }).snd with
      | none =>
        rw [popFrom_pass demand skip frame rest { fiber with stack := [] } (Or.inl answer)]
        rw [tail, split]
        rfl
      | some selected =>
        cases discard :
            skip && (frame.ensure { fiber with stack := [] }).fst.interrupted with
        | false =>
          simp only [interrupted_appendStack, discard, Bool.false_eq_true, ↓reduceDIte]
          simp [popFrom, answer, discard, appendStack]
        | true =>
          simp only [interrupted_appendStack, discard, ↓reduceDIte]
          rw [popFrom_pass demand skip frame rest { fiber with stack := [] } (Or.inr discard)]
          rw [tail, split]
          rfl

private theorem popLive_stack_eq (demand : Arm) (skip : Bool)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    popLive { fiber with stack := stack } demand skip =
      popFrom demand skip stack { fiber with stack := [] } :=
  popLive_stack_eq_aux demand skip _ stack fiber (Nat.le_refl _)

/-- Whole-result equality on every existing primitive, arm and skip flag,
`AsyncFinalizer` included: the restoring frame its hook pushes is popped by the
live traversal on its next step and drained by `passPushed` on the detached
side. census: rule.frames-are-primitives -/
theorem popLive_eq_popFrom (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) :
    self.popLive demand skip = popFrom demand skip self.stack { self with stack := [] } :=
  popLive_stack_eq demand skip self.stack self

/-- The legacy entry agrees when there is no deferred observation to lose.
census: checkpoint.getcont-deferred -/
theorem getContLive_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = false) :
    self.getContLive demand skip = self.getCont demand skip := by
  simp [getContLive, getCont, hdeferred, popLive_eq_popFrom]

/-- A single, non-skipping inner call agrees in every representable state.
census: checkpoint.getcont-deferred -/
theorem getContLive_false_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) : self.getContLive demand false = self.getCont demand false := by
  simp [getContLive, getCont, popLive_eq_popFrom]

/-- Keep the full deferred result whenever post-entry interruption is not
being skipped. census: checkpoint.getcont-deferred -/
theorem getContLive_deferred_kept (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = true)
    (hkeep : (skip && self.interrupted) = false) :
    self.getContLive demand skip =
      ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause],
        { self with deferredInterrupt := false }⟩ := by
  simp [getContLive, hdeferred, hkeep]

/-- Discarding the deferred answer does not discard its chronological event.
census: checkpoint.getcont-deferred -/
theorem getContLive_deferred_discarded (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (hdeferred : self.deferredInterrupt = true)
    (hinterrupted : self.interrupted = true) :
    self.getContLive demand true =
      let next := ({ self with deferredInterrupt := false }).popLive demand true
      { next with events := .deferred self.pendingCause :: next.events } := by
  simp [getContLive, hdeferred, hinterrupted]

private def skipPop (first : FramePop ν σ β ε δ ι α) (demand : Arm) :
    FramePop ν σ β ε δ ι α :=
  match first.answer with
  | .empty => first
  | _ =>
    if first.fiber.interrupted then
      let next := first.fiber.popLive demand true
      { next with popped := first.popped ++ next.popped,
                  events := first.events ++ next.events }
    else first

private theorem skipPop_prefix (frame : Prim ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (result : FramePop ν σ β ε δ ι α) (demand : Arm) :
    skipPop (prefixPop frame events result) demand =
      prefixPop frame events (skipPop result demand) := by
  cases flag : result.fiber.interrupted <;> cases answer : result.answer <;>
    simp [skipPop, prefixPop, flag, answer, List.append_assoc]

private theorem with_same_stack (fiber : FrameFiber ν σ β ε δ ι α)
    (stack : List (Prim ν σ β ε δ ι α)) (same : fiber.stack = stack) :
    { fiber with stack := stack } = fiber := by
  cases fiber
  cases same
  rfl

private theorem popLive_stack_while_aux (demand : Arm) :
    forall (fuel : Nat) (stack : List (Prim ν σ β ε δ ι α))
      (fiber : FrameFiber ν σ β ε δ ι α),
      2 * stack.length + (if fiber.interruptible = true then 1 else 0) <= fuel ->
        popLive { fiber with stack := stack } demand true =
          skipPop (popLive { fiber with stack := stack } demand false) demand := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack fiber bound
    cases stack with
    | nil => simp [popLive, skipPop]
    | cons frame rest =>
      exact absurd bound (by simp only [List.length_cons]; omega)
  | succ fuel ih =>
    intro stack fiber bound
    cases stack with
    | nil => simp [popLive, skipPop]
    | cons frame rest =>
      have step := live_measure_lt frame { fiber with stack := rest }
      have tailBound :
          2 * (frame.ensure { fiber with stack := rest }).fst.stack.length +
            (if (frame.ensure { fiber with stack := rest }).fst.interruptible = true then 1
              else 0) <= fuel := by
        simp only [List.length_cons] at bound
        simp only at step
        omega
      conv => lhs; rw [popLive]
      conv => rhs; arg 1; rw [popLive]
      dsimp only
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceDIte, Bool.true_and]
      cases selected : frame.answerOf demand (frame.ensure { fiber with stack := rest }).snd with
      | none =>
        have tail := ih (frame.ensure { fiber with stack := rest }).fst.stack
          (frame.ensure { fiber with stack := rest }).fst tailBound
        rw [with_stack_self (frame.ensure { fiber with stack := rest }).fst] at tail
        simpa only [skipPop_prefix] using congrArg
          (prefixPop frame (frame.passEvents (frame.ensure { fiber with stack := rest }).snd))
          tail
      | some answer =>
        have nonempty := answer_nonempty frame demand
          (frame.ensure { fiber with stack := rest }).snd answer selected
        cases flag : (frame.ensure { fiber with stack := rest }).fst.interrupted <;>
          cases answer <;> simp_all [skipPop, prefixPop]

private theorem popLive_stack_while (demand : Arm)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    popLive { fiber with stack := stack } demand true =
      skipPop (popLive { fiber with stack := stack } demand false) demand :=
  popLive_stack_while_aux demand _ stack fiber (Nat.le_refl _)

private theorem popFrom_deferred (demand : Arm) (skip : Bool)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    (popFrom demand skip stack fiber).fiber.deferredInterrupt = fiber.deferredInterrupt :=
  popFrom_deferredInterrupt demand skip stack fiber

private theorem popLive_deferred (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) :
    (self.popLive demand skip).fiber.deferredInterrupt = self.deferredInterrupt := by
  rw [popLive_eq_popFrom, popFrom_deferred]

private theorem cleared_eq (self : FrameFiber ν σ β ε δ ι α)
    (hdeferred : self.deferredInterrupt = false) :
    { self with deferredInterrupt := false } = self := by
  cases self
  cases hdeferred
  rfl

private theorem getContLive_plain (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = false) :
    self.getContLive demand skip = self.popLive demand skip := by
  simp [getContLive, hdeferred, cleared_eq self hdeferred]

private theorem cleared_interrupted (self : FrameFiber ν σ β ε δ ι α) :
    ({ self with deferredInterrupt := false }).interrupted = self.interrupted := rfl

/-- One inner call followed by the source's conditional outer failure loop,
retaining all popped frames and chronological events.
census: checkpoint.exit-failcause-skip -/
theorem getContLive_while (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) :
    self.getContLive demand true =
      let first := self.getContLive demand false
      match first.answer with
      | .empty => first
      | _ =>
        if first.fiber.interrupted then
          let next := first.fiber.getContLive demand true
          { next with popped := first.popped ++ next.popped,
                      events := first.events ++ next.events }
        else first := by
  cases delayed : self.deferredInterrupt with
  | false =>
    rw [getContLive_plain self demand true delayed,
        getContLive_plain self demand false delayed]
    have next := getContLive_plain (self.popLive demand false).fiber demand true
      (by rw [popLive_deferred, delayed])
    simp only [next]
    exact popLive_stack_while demand self.stack self
  | true =>
    cases flag : self.interrupted <;>
      simp [getContLive, delayed, cleared_interrupted, flag]

end Effect4.FrameFiber
