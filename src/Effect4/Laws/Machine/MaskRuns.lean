import Effect4.Laws.Machine.MaskDiscipline

/-!
# Laws.Machine.MaskRuns — the saved mask's chain from one pop to a run

`saved_mask_pop_discipline` (`Laws/Machine/MaskDiscipline.lean`) keeps the chain `MaskChain`
through the frame machine's pop and through each region's entry. It is a local law. This module
carries the chain along a run. Its first part is the frame machine alone.

## Part A: the frames

* **A step keeps the chain** (`step_maskChain`). `FrameFiber.step` pops through its two
  resumptions, and `getCont_maskChain` keeps the chain there. A value arm pushes `whileLoop` or
  `iterator` (`armA_maskChain`), and a cause arm pushes nothing (`armE_pushes_nothing`). Each
  other equation of the step pushes the primitive that it reads, or it writes `current`. None
  pushes a restoring frame.
* **A pop that answers nothing ends at an empty stack and at the base**
  (`popFrom_unanswered_stack`, `popFrom_unanswered_flag`). The induction is that of
  `popFrom_maskChain`, with `passPushed_ensure_stack_nil` for the scratch premise. `getCont` has
  the same two statements (`getCont_unanswered_stack`, `getCont_unanswered_flag`).
* **A finished frame has an empty stack, and its flag is the base** (`step_finished_stack`,
  `step_finished_flag`). A step finishes only where its pop answers nothing: an answering frame
  declares the demanded arm (`getCont_answer_hasArm`), and that arm is defined
  (`Prim.armA_isSome`, `Prim.armE_isSome`). `Machine.frameExitState` is that pop's fiber.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. Each
  statement is a step of R11's open part "the lift of saved-mask-pop-discipline to runs";
- reach: the polymorphic `FrameFiber`, at every stack, demand, skip flag and carried cause, with
  one fixed base. The pop asks for an empty scratch stack, as `getCont` calls it;
- it does not establish a law of a run: no fiber's base in a machine, no command of the driver,
  no bracket of a region, no cleanup, no delivery and no liveness;
- consumer: the lift to runs. The fiber machine steps a frame at `evaluatePrim.stepFrame`, and
  it retains a finished frame's state at `evaluatePrim.finishFrame`
  (`Machine/Fibers.lean`).

The design is `docs/research/2026-10-06-seat-LIFT-design.md`.
-/

set_option autoImplicit false

universe u v

namespace Effect4.FrameFiber

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-! ## The base, and the sentinel -/

/-- **The base is a function of the flag and of the stack**: two chains over one flag and one
stack have one base. It is the mirror of `MaskChain.flag_eq`. A step of the lift: the clearing of
a stack keeps the chain exactly at the base, so the flag there names the base. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskChain.base_eq {base base' flag : Bool} {stack : List (Prim ν σ β ε δ ι α)}
    (h : MaskChain base flag stack) (h' : MaskChain base' flag stack) : base = base' := by
  induction stack generalizing flag with
  | nil => exact h.symm.trans h'
  | cons frame rest ih =>
    cases frame with
    | setInterruptible saved => exact ih h.2 h'.2
    | _ => exact ih h h'

/-- An answering frame never answers with the sentinel `ContAnswer.empty`: it answers with a
replacement or with itself. A step of `popFrom_unanswered_stack`, whose answering case it
refuses. -/
@[semantics "scope-lifetime-finalization"]
theorem answerOf_ne_empty (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) (answer : ContAnswer ν σ β ε δ ι α)
    (selected : frame.answerOf demand replacement = some answer) : answer ≠ ContAnswer.empty := by
  intro empty
  subst empty
  cases replacement with
  | some next =>
    rw [Prim.answerOf_replacement] at selected
    cases selected
  | none =>
    cases arm : frame.hasArm demand with
    | false =>
      rw [Prim.answerOf_missing frame demand arm] at selected
      cases selected
    | true =>
      rw [Prim.answerOf_arm frame demand arm] at selected
      cases selected

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-! ## A step keeps the chain -/

/-- **A value arm pushes no restoring frame.** `whileLoop` pushes itself at its next cursor, and
`iterator` pushes itself at its next generator. Every other value arm pushes nothing. So the
chain under the pushed frames is the chain over them. A step of `step_maskChain`. -/
@[semantics "scope-lifetime-finalization"]
theorem armA_maskChain (interp : PrimInterp ν σ β ε δ ι α) (frame : Prim ν σ β ε δ ι α)
    (value : β) (provided : Option (Exit β ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (arm : frame.armA interp value provided = some (next, pushed))
    (base flag : Bool) (rest : List (Prim ν σ β ε δ ι α)) (valid : MaskChain base flag rest) :
    MaskChain base flag (pushed ++ rest) := by
  cases frame with
  | whileLoop loop cursor =>
    cases resumed : interp.loopResume loop cursor value with
    | «continue» cursor' body =>
      simp only [Prim.armA, resumed] at arm
      cases arm
      exact valid
    | finish code =>
      simp only [Prim.armA, resumed] at arm
      cases arm
      exact valid
  | iterator generator cursor =>
    cases stepped : (interp.iterNext generator value).snd with
    | done result =>
      simp only [Prim.armA, stepped] at arm
      cases arm
      exact valid
    | halt cause =>
      simp only [Prim.armA, stepped] at arm
      cases arm
      exact valid
    | resume code continueAs =>
      simp only [Prim.armA, stepped] at arm
      cases arm
      exact valid
  | onSuccess body onValue => cases arm; exact valid
  | onSuccessConst body code => cases arm; exact valid
  | onSuccessAndFailure body onValue onCause => cases arm; exact valid
  | exitFrame body => cases arm; exact valid
  | onExit body finalizer told => cases arm; exact valid
  | _ => cases arm

/-- **A cause arm pushes nothing.** A step of `step_maskChain`. -/
@[semantics "scope-lifetime-finalization"]
theorem armE_pushes_nothing (interp : PrimInterp ν σ β ε δ ι α) (frame : Prim ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (arm : frame.armE interp cause provided = some (next, pushed)) : pushed = [] := by
  cases frame <;> cases arm <;> rfl

/-- `resumeValue` keeps the chain: its pop keeps it (`getCont_maskChain`), and the answering
frame's value arm pushes no restoring frame. A step of `step_maskChain`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeValue_maskChain (base : Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (f : FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Exit β ε δ ι α))
    (valid : MaskChain base f.interruptible f.stack) (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.resumeValue interp value provided).fst = FrameStep.running next) :
    MaskChain base next.interruptible next.stack := by
  have popped := getCont_maskChain base f Arm.contA false none valid
  unfold resumeValue at running
  split at running
  · cases running
  · cases running
    exact popped
  · cases running
    exact popped
  · split at running
    · rename_i arm
      cases running
      exact armA_maskChain interp _ value provided _ _ arm base _ _ popped
    · cases running

/-- `resumeCause` keeps the chain: its pop keeps it, and a cause arm pushes nothing. A step of
`step_maskChain`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeCause_maskChain (base : Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (f : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (valid : MaskChain base f.interruptible f.stack) (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.resumeCause interp cause provided).fst = FrameStep.running next) :
    MaskChain base next.interruptible next.stack := by
  have popped := getCont_maskChain base f Arm.contE true (some cause) valid
  unfold resumeCause at running
  dsimp only at running
  split at running
  · cases running
  · cases running
    exact popped
  · cases running
    exact popped
  · split at running
    · rename_i arm
      cases running
      rw [armE_pushes_nothing interp _ _ _ _ _ arm]
      exact popped
    · cases running

/-- **`FrameFiber.step` keeps the chain at the same base.** Where the step goes on, the next
fiber holds the chain that the fiber held. A success, a failure and a `sync` pop through their
resumption. `iterator` pushes what its value arm pushes. Each frame constructor pushes itself, and
`whileLoop` pushes itself at its first cursor. Every other equation writes `current` or nothing.
No equation pushes a restoring frame.

A step of R11's open part "the lift of saved-mask-pop-discipline to runs". Its consumer is the
fiber machine's delegation to the frame machine, `evaluatePrim.stepFrame`. It states nothing of a
finished step: `step_finished_stack` does. -/
@[semantics "scope-lifetime-finalization"]
theorem step_maskChain (base : Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (f : FrameFiber ν σ β ε δ ι α) (valid : MaskChain base f.interruptible f.stack)
    (next : FrameFiber ν σ β ε δ ι α) (running : (f.step interp).fst = FrameStep.running next) :
    MaskChain base next.interruptible next.stack := by
  cases current : f.current with
  | success value =>
    simp only [step, current] at running
    exact resumeValue_maskChain base interp f _ _ valid next running
  | failure cause =>
    simp only [step, current] at running
    exact resumeCause_maskChain base interp f _ _ valid next running
  | sync thunk =>
    simp only [step, current] at running
    exact resumeValue_maskChain base interp f _ _ valid next running
  | iterator generator cursor =>
    simp only [step, current] at running
    split at running
    · rename_i arm
      cases running
      exact armA_maskChain interp _ _ _ _ _ arm base _ _ valid
    · cases running
      exact valid
  | whileLoop loop cursor =>
    simp only [step, current] at running
    split at running <;> cases running <;> exact valid
  | _ =>
    simp only [step, current] at running
    cases running
    exact valid

/-! ## A pop that answers nothing -/

/-- **A pop that answers nothing ends at an empty stack**, from an empty scratch stack. Every
frame is passed, and one drain empties what each hook pushed (`passPushed_ensure_stack_nil`). An
answering frame never answers with the sentinel (`answerOf_ne_empty`), and a drained frame that
answers is no sentinel either.

A step of R11's open part "the lift of saved-mask-pop-discipline to runs". Its consumer is
`step_finished_stack`, through `getCont_unanswered_stack`. The scratch premise is needed: with no
frame to pop, the result's stack is the scratch stack. -/
@[semantics "scope-lifetime-finalization"]
theorem popFrom_unanswered_stack (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (scratchEmpty : f.stack = [])
    (unanswered : (popFrom demand skip frames f).answer = ContAnswer.empty) :
    (popFrom demand skip frames f).fiber.stack = [] := by
  induction frames generalizing f with
  | nil =>
    rw [popFrom_nil]
    exact scratchEmpty
  | cons head rest ih =>
    have emptied := passPushed_ensure_stack_nil demand skip head f none scratchEmpty
    have continued : (continueFrom demand skip head rest f).answer = ContAnswer.empty →
        (continueFrom demand skip head rest f).fiber.stack = [] := by
      intro silent
      unfold continueFrom at silent ⊢
      cases drained : (passPushed demand skip (head.ensure f).fst).answer with
      | empty =>
        rw [joinPushed_of_empty demand skip (head.ensure f).fst rest _ drained] at silent ⊢
        exact ih _ emptied silent
      | deferred cause =>
        rw [joinPushed_of_answer demand skip (head.ensure f).fst rest _ _
          (by intro h; cases h) drained] at silent
        cases silent
      | replacement next =>
        rw [joinPushed_of_answer demand skip (head.ensure f).fst rest _ _
          (by intro h; cases h) drained] at silent
        cases silent
      | frame answering =>
        rw [joinPushed_of_answer demand skip (head.ensure f).fst rest _ _
          (by intro h; cases h) drained] at silent
        cases silent
    cases answered : head.answerOf demand (head.ensure f).snd with
    | none =>
      rw [popFrom_continue_answer demand skip head rest f (Or.inl answered)] at unanswered
      rw [popFrom_continue_fiber demand skip head rest f (Or.inl answered)]
      exact continued unanswered
    | some answer =>
      cases skipped : (skip && (head.ensure f).fst.interrupted) with
      | true =>
        rw [popFrom_continue_answer demand skip head rest f (Or.inr skipped)] at unanswered
        rw [popFrom_continue_fiber demand skip head rest f (Or.inr skipped)]
        exact continued unanswered
      | false =>
        rw [popFrom_answer_answer demand skip head rest f answer answered skipped] at unanswered
        exact absurd unanswered (answerOf_ne_empty head demand _ answer answered)

/-- **A pop from a chain that answers nothing ends at the base.** The pop keeps the chain
(`popFrom_maskChain`), and the chain over an empty stack is the flag's equation with the base.

A step of R11's open part "the lift of saved-mask-pop-discipline to runs". Its consumer is
`step_finished_flag`, through `getCont_unanswered_flag`. -/
@[semantics "scope-lifetime-finalization"]
theorem popFrom_unanswered_flag (base : Bool) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (scratchEmpty : f.stack = []) (valid : MaskChain base f.interruptible frames)
    (unanswered : (popFrom demand skip frames f).answer = ContAnswer.empty) :
    (popFrom demand skip frames f).fiber.interruptible = base := by
  have chain := popFrom_maskChain base demand skip frames f none scratchEmpty valid
  rw [popFrom_unanswered_stack demand skip frames f scratchEmpty unanswered] at chain
  exact chain

/-- `getCont` that answers nothing ends at an empty stack, at every carried cause. Its branch of
a deferred interrupt answers, so the pop is the other branch. A step of `step_finished_stack`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_unanswered_stack (f : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (f.getCont demand skip cause).fiber.stack = [] := by
  rw [getCont_answer_cause] at unanswered
  rw [getCont_fiber_cause]
  unfold getCont at unanswered ⊢
  split at unanswered
  · cases unanswered
  · rename_i popping
    rw [if_neg popping]
    exact popFrom_unanswered_stack demand skip f.stack _ rfl unanswered

/-- `getCont` from a chain that answers nothing ends at the base. A step of
`step_finished_flag`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_unanswered_flag (base : Bool) (f : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α))
    (valid : MaskChain base f.interruptible f.stack)
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (f.getCont demand skip cause).fiber.interruptible = base := by
  have chain := getCont_maskChain base f demand skip cause valid
  rw [getCont_unanswered_stack f demand skip cause unanswered] at chain
  exact chain

/-! ## A finished step answered nothing -/

/-- A finished `resumeValue` answered nothing. Its other finishing case has an answering frame
with no value arm, and no frame is such: the answer declares the arm, and the arm is defined. A
step of `step_finished_stack`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeValue_finished (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (value : β) (provided : Option (Exit β ε δ ι α)) (exit : Exit β ε δ ι α)
    (finished : (f.resumeValue interp value provided).fst = FrameStep.finished exit) :
    (f.getCont Arm.contA false).answer = ContAnswer.empty := by
  unfold resumeValue at finished
  split at finished
  · assumption
  · cases finished
  · cases finished
  · rename_i frame answered
    split at finished
    · cases finished
    · rename_i arm
      have declared := getCont_answer_hasArm f Arm.contA false frame answered
      have defined := Prim.armA_isSome interp frame value provided
      rw [arm, declared] at defined
      cases defined

/-- A finished `resumeCause` answered nothing, in the same way. A step of
`step_finished_stack`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeCause_finished (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) (exit : Exit β ε δ ι α)
    (finished : (f.resumeCause interp cause provided).fst = FrameStep.finished exit) :
    (f.getCont Arm.contE true).answer = ContAnswer.empty := by
  rw [← getCont_answer_cause f Arm.contE true (some cause)]
  unfold resumeCause at finished
  dsimp only at finished
  split at finished
  · assumption
  · cases finished
  · cases finished
  · rename_i frame answered
    split at finished
    · cases finished
    · rename_i arm
      rw [getCont_answer_cause] at answered
      have declared := getCont_answer_hasArm f Arm.contE true frame answered
      have defined := Prim.armE_isSome interp frame
        ((f.getCont Arm.contE true (some cause)).carriedCause.getD cause)
        (provided.map (f.getCont Arm.contE true (some cause)).deliveredExit)
      rw [arm, declared] at defined
      cases defined

end Effect4.FrameFiber

namespace Effect4.Machine

open Effect4 Effect4.FrameFiber

section FinishedFrame

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- **A finished frame has an empty stack.** Where `FrameFiber.step` finishes, the state that
`frameExitState` retains has no frame. The step finishes at a success, a failure or a `sync`
whose pop answers nothing, and `frameExitState` is that pop's fiber.

A step of R11's open part "the lift of saved-mask-pop-discipline to runs". Its consumer is the
fiber machine's `evaluatePrim.finishFrame`, which retains `frameExitState` before `Cmd.finish`.
It asks for no chain. -/
@[semantics "scope-lifetime-finalization"]
theorem step_finished_stack (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (exit : Exit β ε δ ι α) (finished : (f.step interp).fst = FrameStep.finished exit) :
    (frameExitState f).stack = [] := by
  cases current : f.current with
  | success value =>
    simp only [FrameFiber.step, current] at finished
    simp only [frameExitState, current]
    exact getCont_unanswered_stack f Arm.contA false none
      (resumeValue_finished interp f _ _ exit finished)
  | failure cause =>
    simp only [FrameFiber.step, current] at finished
    simp only [frameExitState, current]
    exact getCont_unanswered_stack f Arm.contE true none
      (resumeCause_finished interp f _ _ exit finished)
  | sync thunk =>
    simp only [FrameFiber.step, current] at finished
    simp only [frameExitState, current]
    exact getCont_unanswered_stack f Arm.contA false none
      (resumeValue_finished interp f _ _ exit finished)
  | iterator generator cursor =>
    simp only [FrameFiber.step, current] at finished
    split at finished <;> cases finished
  | whileLoop loop cursor =>
    simp only [FrameFiber.step, current] at finished
    split at finished <;> cases finished
  | _ => simp only [FrameFiber.step, current, reduceCtorEq] at finished

/-- **A finished frame is at the base.** With the chain over the fiber, the state that
`frameExitState` retains has the base as its flag: the chain is kept
(`frameExitState_maskChain`), and the stack is empty.

A step of R11's open part "the lift of saved-mask-pop-discipline to runs". Its consumer is the
completed exit's statement at the fiber machine: the driver issues `Cmd.finish` at the base. -/
@[semantics "scope-lifetime-finalization"]
theorem step_finished_flag (base : Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (f : FrameFiber ν σ β ε δ ι α) (valid : MaskChain base f.interruptible f.stack)
    (exit : Exit β ε δ ι α) (finished : (f.step interp).fst = FrameStep.finished exit) :
    (frameExitState f).interruptible = base := by
  have chain := frameExitState_maskChain base f valid
  rw [step_finished_stack interp f exit finished] at chain
  exact chain

end FinishedFrame

end Effect4.Machine
