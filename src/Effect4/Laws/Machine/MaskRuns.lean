import Effect4.Laws.Machine.MaskDiscipline
import Effect4.Laws.Machine.Lift

/-!
# Laws.Machine.MaskRuns — the saved mask's chain from one pop to a run

`saved_mask_pop_discipline` (`Laws/Machine/MaskDiscipline.lean`) keeps the chain `MaskChain`
through the frame machine's pop and through each region's entry. It is a local law. This module
carries the chain along a run: **each live fiber of a reached machine holds the chain at its
start flag** (`saved_mask_chain_runs`). A fiber is live while its `exit` is `none`.

Its first part is the frame machine alone. Its second part is the fiber machine
(`Machine/Fibers.lean`), and the lift through `Machine.Lift` (`Laws/Machine/Lift.lean`).

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

Part A's reach is the polymorphic `FrameFiber`, at every stack, demand, skip flag and carried
cause, with one fixed base. The pop asks for an empty scratch stack, as `getCont` calls it. Its
consumer is part B: the fiber machine steps a frame at `evaluatePrim.stepFrame`, and it retains
a finished frame's state at `evaluatePrim.finishFrame`.

## Part B: the machine

* **Where a fiber's base is.** The machine stores no base. The base is proof data: a table of
  start flags, the world of the lift (`basesOrder`). Entry `n` is the flag that the fiber with
  id `n` started with. A spawn appends one entry (`maskRuns_make`, `spawn_maskRuns`), and no
  command changes an entry.
* **The invariant** (`MaskRuns`). Each fiber has its entry, and a live fiber holds the chain at
  its entry. An exited fiber's flag and stack are outside it: the driver steps an exited fiber
  where a second fiber evaluates the registration of a race that the first one hosts
  (`Test/Machine/MaskRuns.lean` holds the reached machine).
* **The command condition** (`ClearReady`). Two commands clear a fiber. `Cmd.exitDone` asks
  that the fiber has exited, or that its stack is empty, or that its flag is its base.
  `Cmd.finish` clears through `exitFiber.exitStore` after it publishes, so it asks for nothing.
  Each command keeps the invariant under the condition (`driveStep_maskRuns`).
* **The driver meets the condition** (`maskRuns_stepKeeps`). Each pending `Cmd.exitDone` names
  a fiber that has exited (`ClearsExited`), and no command resets an exit. `Lift.Guarded`
  carries that fact through the observers' commands and their nested work.
* **The lift** (`maskRuns_decisionLift`, `replayEval_maskRuns`). Each decision and each replay
  keeps the invariant, at a table that grows at its end. The lift asks for no admission.
* **A finished frame at the machine** (`IterKeepsMask.finished_stack`,
  `IterKeepsMask.finished_flag`). The driver issues `Cmd.finish` at an empty stack, and at the
  base where the fiber is live. It is the completed exit's statement, at its event.

The step's proof reads each fiber through one relation and each machine through a second
(`MaskLater`, `MaskAged`). Both are preorders that read projections only, so each helper of the
driver gets one statement, and a write of a field outside them is closed by reflexivity.

The command loop takes its evaluator as an instance. So the statements over a command take one
premise, `EvaluatorKeepsMask`: each evaluation keeps the machine and the fiber. The frame
evaluator `evaluatePrim` meets it (`evaluatePrim_keepsMask`), and the placed theorem is at that
evaluator. A run of a compiled program uses `Program.evaluateNative`
(`src/Effect4/Program/Compile.lean`), whose premise has no statement in this module.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. The
  proposed registry claim is `saved-mask-chain-runs`, the lift of `saved-mask-pop-discipline` to
  runs. Its pointer is `saved_mask_chain_runs`, and each other theorem is a step of it;
- reach: the fiber machine at the frame evaluator, at every interpreter, decision tape and fuel,
  with no admission of a decision and no premise on a program;
- it does not establish the bracket of a region, a flag or a stack of an exited fiber as a state
  invariant, a cleanup's multiplicity, a delivery, a budget or liveness. It says nothing of a
  host or of a printed form. An invariant is not progress;
- consumers: the bracket's law, then the waiting wrapper under a masked caller and Semaphore's
  protected permit.

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
open Effect4.Laws.Effects (WorldOrder)

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

/-- **The world of the lift: the table of start flags**, in the prefix order. Entry `n` is the flag
that the fiber with id `n` started with. A spawn appends one entry, and no command changes an
entry. The machine stores no base: `RunFiber.make` hands the flag to `FiberCore.start`, and no
field, fork record or event keeps it. So the base is proof data, as the chain is. -/
def basesOrder : WorldOrder (List Bool) :=
  ⟨fun bases bases' => bases <+: bases', List.prefix_refl, List.IsPrefix.trans⟩

/-! ## Part B: the machine

### A later fiber, and a later machine

The step's proof reads each fiber through `MaskLater` and each machine through `MaskAged`. Both
are preorders, and both read projections only. -/

section Relations

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- `g` is a later state of the fiber `f`. It has the id of `f`. It has not exited only if `f` had
not. While it has not exited, it holds each chain that `f` held, at the same base.

The relation reads the id, the exit, the flag and the stack only. So a write of another field
is closed by reflexivity: the projections reduce. -/
def MaskLater (f g : RunFiber ν σ β ε δ ι α χ) : Prop :=
  g.id = f.id ∧ (g.exit = none → f.exit = none) ∧
    (g.exit = none → ∀ base, MaskChain base f.frame.interruptible f.frame.stack →
      MaskChain base g.frame.interruptible g.frame.stack)

/-- Each fiber is a later state of itself. It closes each write of a field that the relation does
not read. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskLater.refl (f : RunFiber ν σ β ε δ ι α χ) : MaskLater f f :=
  ⟨rfl, fun live => live, fun _ _ valid => valid⟩

/-- Later states compose. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskLater.trans {f g h : RunFiber ν σ β ε δ ι α χ} (a : MaskLater f g) (b : MaskLater g h) :
    MaskLater f h :=
  ⟨b.1.trans a.1, fun live => a.2.1 (b.2.1 live),
    fun live base valid => b.2.2 live base (a.2.2 (b.2.1 live) base valid)⟩

/-- A fiber that has exited is a later state of each fiber with its id: the relation asks for a
chain only before the exit. The publication of a fiber is this case, and so is each clearing
after it. A step of `exitFiber_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskLater.of_exited {f g : RunFiber ν σ β ε δ ι α χ} (id : g.id = f.id)
    (exited : g.exit.isSome = true) : MaskLater f g := by
  refine ⟨id, ?_, ?_⟩ <;> intro live <;> rw [live] at exited <;> cases exited

/-- The machine `m'` is a later state of `m`. Its allocator has not gone back. Each of its fibers
is a later state of a fiber of `m`, or it was born since: its id was not allocated in `m`, and
while it has not exited it holds the chain at the flag that `born` gives its id.

The relation reads `nextId` and `fibers` only. So a write of the trace, of the store, of a race
or of the armed queue is closed by reflexivity. -/
def MaskAged (m m' : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  m.nextId ≤ m'.nextId ∧ ∃ born : Nat → Bool, ∀ g ∈ m'.fibers,
    (∃ f ∈ m.fibers, MaskLater f g) ∨
      (m.nextId ≤ g.id.value ∧ g.id.value < m'.nextId ∧
        (g.exit = none → MaskChain (born g.id.value) g.frame.interruptible g.frame.stack))

/-- Each machine is a later state of itself. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.refl (m : RunMachine ν σ β ε δ ι α χ St) : MaskAged m m :=
  ⟨Nat.le_refl _, fun _ => true, fun g mem => Or.inl ⟨g, mem, MaskLater.refl g⟩⟩

/-- Later machines compose: a fiber born on the way keeps its birth flag. A step of
`driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.trans {a b c : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged a b)
    (h' : MaskAged b c) : MaskAged a c := by
  obtain ⟨le, born, old⟩ := h
  obtain ⟨le', born', old'⟩ := h'
  refine ⟨Nat.le_trans le le', fun n => if n < b.nextId then born n else born' n, ?_⟩
  intro g mem
  rcases old' g mem with ⟨f, memf, later⟩ | ⟨lower, upper, chain⟩
  · rcases old f memf with ⟨e, meme, later'⟩ | ⟨lower, upper, chain⟩
    · exact Or.inl ⟨e, meme, later'.trans later⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [later.1]
        exact lower
      · rw [later.1]
        exact Nat.lt_of_lt_of_le upper le'
      · intro live
        dsimp only
        rw [later.1, if_pos upper]
        exact later.2.2 live _ (chain (later.2.1 live))
  · refine Or.inr ⟨Nat.le_trans le lower, upper, ?_⟩
    intro live
    dsimp only
    rw [if_neg (Nat.not_lt.mpr lower)]
    exact chain live

/-- A fiber that a lookup finds is in the table. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem RunMachine.mem_of_fiber? {m : RunMachine ν σ β ε δ ι α χ St} {id : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ} (found : m.fiber? id = some f) : f ∈ m.fibers :=
  List.mem_of_find?_eq_some found

/-- A fiber that a lookup finds has the lookup's id. A step of `maskRuns_stepKeeps`. -/
@[semantics "scope-lifetime-finalization"]
theorem RunMachine.id_of_fiber? {m : RunMachine ν σ β ε δ ι α χ St} {id : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ} (found : m.fiber? id = some f) : f.id = id := by
  have matched := List.find?_some found
  exact of_decide_eq_true matched

/-- An edit of one fiber keeps the allocator. A step of `maskRuns_decisionLift`. -/
@[semantics "scope-lifetime-finalization"]
theorem RunMachine.modify_nextId (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (k : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) :
    (m.modify id k).nextId = m.nextId := by
  unfold RunMachine.modify
  split <;> rfl

/-- A later state of a fiber of the later machine, written over that machine. `RunMachine.update`
replaces each fiber with the written id. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.update {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m₁.fibers) (later : MaskLater f g) :
    MaskAged m (m₁.update g) := by
  obtain ⟨le, born, old⟩ := h
  refine ⟨le, born, ?_⟩
  intro e meme
  obtain ⟨e₀, mem₀, rfl⟩ := List.mem_map.mp meme
  split
  · rcases old f mem with ⟨f₀, memf, later'⟩ | ⟨lower, upper, chain⟩
    · exact Or.inl ⟨f₀, memf, later'.trans later⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [later.1]
        exact lower
      · rw [later.1]
        exact upper
      · intro live
        rw [later.1]
        exact later.2.2 live _ (chain (later.2.1 live))
  · exact old e₀ mem₀

/-- A later state of a fiber of the first machine, written over a later machine. The loop writes
an evaluated fiber back this way (`settle`). A step of `settle_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.update_old {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (later : MaskLater f g) :
    MaskAged m (m₁.update g) := by
  obtain ⟨le, born, old⟩ := h
  refine ⟨le, born, ?_⟩
  intro e meme
  obtain ⟨e₀, mem₀, rfl⟩ := List.mem_map.mp meme
  split
  · exact Or.inl ⟨f, mem, later⟩
  · exact old e₀ mem₀

/-- An edit of the fiber at one id, where the edit gives a later state. A step of
`driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.modify {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁) (id : FiberId)
    (k : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) (later : ∀ f, MaskLater f (k f)) :
    MaskAged m (m₁.modify id k) := by
  unfold RunMachine.modify
  split
  · exact h
  · rename_i f found
    exact h.update (RunMachine.mem_of_fiber? found) (later f)

/-- An edit of every fiber, where the edit gives a later state. A park's cleanup drops observers
this way. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.mapFibers {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (later : ∀ f, MaskLater f (edit f)) :
    MaskAged m { m₁ with fibers := m₁.fibers.map edit } := by
  obtain ⟨le, born, old⟩ := h
  refine ⟨le, born, ?_⟩
  intro e meme
  obtain ⟨e₀, mem₀, rfl⟩ := List.mem_map.mp meme
  rcases old e₀ mem₀ with ⟨f₀, memf, later'⟩ | ⟨lower, upper, chain⟩
  · exact Or.inl ⟨f₀, memf, later'.trans (later e₀)⟩
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [(later e₀).1]
      exact lower
    · rw [(later e₀).1]
      exact upper
    · intro live
      rw [(later e₀).1]
      exact (later e₀).2.2 live _ (chain ((later e₀).2.1 live))

/-- A fiber appended at the next id, which holds the chain at some flag, is born at that flag. A
step of `MaskAged.make`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.born {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (child : RunFiber ν σ β ε δ ι α χ) (id : child.id = ⟨m₁.nextId⟩) (flag : Bool)
    (start : MaskChain flag child.frame.interruptible child.frame.stack)
    (m₂ : RunMachine ν σ β ε δ ι α χ St) (fibers : m₂.fibers = m₁.fibers ++ [child])
    (next : m₂.nextId = m₁.nextId + 1) : MaskAged m m₂ := by
  obtain ⟨le, born, old⟩ := h
  refine ⟨by rw [next]; exact Nat.le_succ_of_le le,
    fun n => if n = m₁.nextId then flag else born n, ?_⟩
  intro e meme
  rw [fibers] at meme
  rcases List.mem_append.mp meme with mem₁ | new
  · rcases old e mem₁ with left | ⟨lower, upper, chain⟩
    · exact Or.inl left
    · refine Or.inr ⟨lower, by rw [next]; exact Nat.lt_succ_of_lt upper, ?_⟩
      intro live
      dsimp only
      rw [if_neg (Nat.ne_of_lt upper)]
      exact chain live
  · have same : e = child := List.mem_singleton.mp new
    subst same
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [id]
      exact le
    · rw [id, next]
      exact Nat.lt_succ_self _
    · intro _
      rw [id]
      dsimp only
      rw [if_pos rfl]
      exact start

/-- A fiber that `RunFiber.make` starts at the next id is born at its start flag: `FiberCore.start`
gives it that flag over an empty stack, and the chain over an empty stack is the flag's equation
with the base. A step of `spawn_maskAged`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.make {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (program : Prim ν σ β ε δ ι α) (flag : Bool) (budget : Nat × Bool) (context : χ)
    (m₂ : RunMachine ν σ β ε δ ι α χ St)
    (fibers : m₂.fibers = m₁.fibers ++ [RunFiber.make ⟨m₁.nextId⟩ program flag budget context])
    (next : m₂.nextId = m₁.nextId + 1) : MaskAged m m₂ :=
  h.born (RunFiber.make ⟨m₁.nextId⟩ program flag budget context) rfl flag rfl m₂ fibers next

/-- A trace event changes no fiber. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.emit {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (events : List (RunEvent ν σ β ε δ ι α χ)) : MaskAged m (m₁.emit events) := h

end Relations

/-! ### The invariant -/

section Invariant

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- A fiber has its entry in the table of start flags, and it holds the chain at that entry while
it has not exited. -/
def MaskKept (bases : List Bool) (f : RunFiber ν σ β ε δ ι α χ) : Prop :=
  ∃ base, bases[f.id.value]? = some base ∧
    (f.exit = none → MaskChain base f.frame.interruptible f.frame.stack)

/-- **The invariant.** The table has one entry for each allocated fiber id. Each fiber that has not
exited holds the chain at its entry: its base is its start flag.

The invariant ranges over the fibers that have not exited. An exited fiber's flag and stack are
outside it: the driver steps an exited fiber where a second fiber evaluates the registration of
a race that the first one hosts, and `Test/Machine/MaskRuns.lean` holds that reached machine. -/
def MaskRuns (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  bases.length = m.nextId ∧ ∀ f ∈ m.fibers, MaskKept bases f

/-- Each fiber's id is allocated: it has an entry. A step of `maskRuns_stepKeeps`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskRuns.bound {bases : List Bool} {m : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) {f : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) :
    f.id.value < m.nextId := by
  obtain ⟨base, entry, -⟩ := kept.2 f mem
  rw [← kept.1]
  exact (List.getElem?_eq_some_iff.mp entry).1

/-- **A later machine holds the invariant at a longer table.** Each new entry is the flag at which
a new fiber was born. No old entry changes. A step of `driveStep_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskRuns.aged {bases : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (aged : MaskAged m m') :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' m' := by
  obtain ⟨length, fibers⟩ := kept
  obtain ⟨le, born, old⟩ := aged
  refine ⟨bases ++ (List.range (m'.nextId - m.nextId)).map (fun k => born (m.nextId + k)),
    List.prefix_append _ _, ?_, ?_⟩
  · rw [List.length_append, List.length_map, List.length_range, length]
    omega
  · intro g mem
    rcases old g mem with ⟨f, memf, later⟩ | ⟨lower, upper, chain⟩
    · obtain ⟨base, entry, valid⟩ := fibers f memf
      refine ⟨base, ?_, fun live => later.2.2 live base (valid (later.2.1 live))⟩
      rw [later.1, List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1]
      exact entry
    · refine ⟨born g.id.value, ?_, chain⟩
      have index : m.nextId + (g.id.value - bases.length) = g.id.value := by omega
      rw [List.getElem?_append_right (by omega), List.getElem?_map,
        List.getElem?_range (by omega), Option.map_some, index]

/-- A later machine with the same allocator holds the invariant at the same table. A step of
`maskRuns_decisionLift`: a decision's edits outside the command loop spawn no fiber. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskRuns.same {bases : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (aged : MaskAged m m') (next : m'.nextId = m.nextId) :
    MaskRuns bases m' := by
  obtain ⟨length, fibers⟩ := kept
  obtain ⟨-, born, old⟩ := aged
  refine ⟨length.trans next.symm, ?_⟩
  intro g mem
  rcases old g mem with ⟨f, memf, later⟩ | ⟨lower, upper, -⟩
  · obtain ⟨base, entry, valid⟩ := fibers f memf
    refine ⟨base, ?_, fun live => later.2.2 live base (valid (later.2.1 live))⟩
    rw [later.1]
    exact entry
  · rw [next] at upper
    exact absurd upper (Nat.not_lt.mpr lower)

/-- The empty machine holds the invariant at the empty table. It is the field `empty` of
`saved_mask_chain_runs`. -/
@[semantics "scope-lifetime-finalization"]
theorem maskRuns_empty (state : St) :
    MaskRuns [] (RunMachine.empty state : RunMachine ν σ β ε δ ι α χ St) :=
  ⟨rfl, fun _ mem => nomatch mem⟩

/-- **A fiber's base is its start flag.** A fiber that `RunFiber.make` starts at the next id extends
the table by the flag that `FiberCore.start` gives it. A root is this case. It is the field
`start` of `saved_mask_chain_runs`. -/
@[semantics "scope-lifetime-finalization"]
theorem maskRuns_make (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (kept : MaskRuns bases m) (program : Prim ν σ β ε δ ι α) (flag : Bool) (budget : Nat × Bool)
    (context : χ) :
    MaskRuns (bases ++ [flag])
      { m with
        fibers := m.fibers ++ [RunFiber.make ⟨m.nextId⟩ program flag budget context]
        nextId := m.nextId + 1 } := by
  refine ⟨?_, ?_⟩
  · rw [List.length_append, kept.1]
    rfl
  · intro g mem
    rcases List.mem_append.mp mem with old | new
    · obtain ⟨base, entry, valid⟩ := kept.2 g old
      refine ⟨base, ?_, valid⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1]
      exact entry
    · have same := List.mem_singleton.mp new
      subst same
      refine ⟨flag, ?_, fun _ => rfl⟩
      show (bases ++ [flag])[m.nextId]? = some flag
      rw [← kept.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl

/-- A spawn extends the table by the flag that its mask mode gives the child: true, false, or the
parent's flag. It is `maskRuns_make` at the machine that `spawn` builds. Its consumer is the
bracket's law, which reads a child's base. -/
@[semantics "scope-lifetime-finalization"]
theorem spawn_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (kept : MaskRuns bases m)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    MaskRuns
      (bases ++ [match options.maskMode with
        | Supervision.MaskMode.interruptible => true
        | Supervision.MaskMode.uninterruptible => false
        | Supervision.MaskMode.inherit => parent.frame.interruptible])
      (spawn interp m parent program options site).1 :=
  maskRuns_make bases m kept program _ (interp.budgetOf parent.context) parent.context

end Invariant


/-! ### The command condition, and the pending condition -/

section Pending

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- Each fiber with this id has exited, and the id is allocated. So no later spawn takes the id. -/
def Exited (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Prop :=
  id.value < m.nextId ∧ ∀ f ∈ m.fibers, f.id = id → f.exit.isSome = true

/-- No command resets an exit: a later machine keeps `Exited`. A step of `maskRuns_stepKeeps`: a
pending `Cmd.exitDone` stays safe through the observers' commands and their nested work. -/
@[semantics "scope-lifetime-finalization"]
theorem Exited.aged {m m' : RunMachine ν σ β ε δ ι α χ St} {id : FiberId} (h : Exited m id)
    (aged : MaskAged m m') : Exited m' id := by
  obtain ⟨bound, exited⟩ := h
  obtain ⟨le, born, old⟩ := aged
  refine ⟨Nat.lt_of_lt_of_le bound le, ?_⟩
  intro g mem same
  rcases old g mem with ⟨f, memf, later⟩ | ⟨lower, -, -⟩
  · have before := exited f memf (later.1.symm.trans same)
    cases live : g.exit with
    | none =>
      rw [later.2.1 live] at before
      cases before
    | some exit => rfl
  · rw [same] at lower
    exact absurd bound (Nat.not_lt.mpr lower)

/-- **The pending condition.** Each pending `Cmd.exitDone` names a fiber that has exited.
`Lift.Guarded` carries it as its fact on the pending commands. The driver meets it:
`exitFiber.exitStore` issues `Cmd.exitDone` for the fiber that it has published. -/
def ClearsExited (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) : Prop :=
  ∀ id, Cmd.exitDone id ∈ cmds → Exited m id

/-- No command of the list is a `Cmd.exitDone`. -/
def noClear (cmds : List (Cmd ν σ β ε δ ι α)) : Bool :=
  cmds.all fun c => match c with
    | Cmd.exitDone _ => false
    | _ => true

/-- A list clears nothing exactly when its two parts clear nothing. A step of
`driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem noClear_append (a b : List (Cmd ν σ β ε δ ι α)) :
    noClear (a ++ b) = (noClear a && noClear b) := List.all_append

/-- Two lists that clear nothing, joined. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem noClear_append_of {a b : List (Cmd ν σ β ε δ ι α)} (ha : noClear a = true)
    (hb : noClear b = true) : noClear (a ++ b) = true := by
  rw [noClear_append, ha, hb]
  rfl

/-- A list of commands of one shape that clears nothing. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem noClear_map {τ : Type} (g : τ → Cmd ν σ β ε δ ι α) (single : ∀ x, noClear [g x] = true)
    (xs : List τ) : noClear (xs.map g) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih => exact noClear_append_of (a := [g x]) (single x) ih

/-- A choice between two lists that clear nothing. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem noClear_ite (c : Prop) [Decidable c] {a b : List (Cmd ν σ β ε δ ι α)}
    (ha : noClear a = true) (hb : noClear b = true) : noClear (if c then a else b) = true := by
  split
  · exact ha
  · exact hb

/-- A list that clears nothing holds no `Cmd.exitDone`. A step of `CmdKeepsMask.of_prefix`. -/
@[semantics "scope-lifetime-finalization"]
theorem not_mem_of_noClear {cmds : List (Cmd ν σ β ε δ ι α)} (clear : noClear cmds = true)
    (id : FiberId) : Cmd.exitDone id ∉ cmds := by
  intro mem
  have := List.all_eq_true.mp clear _ mem
  cases this

/-- What one command leaves: the machine has aged, and each `Cmd.exitDone` that it leaves was
pending before, or it names a fiber that has exited now. -/
def CmdKeepsMask (m : RunMachine ν σ β ε δ ι α χ St) (rest : List (Cmd ν σ β ε δ ι α))
    (out : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) : Prop :=
  MaskAged m out.1 ∧ ∀ id, Cmd.exitDone id ∈ out.2 → Cmd.exitDone id ∈ rest ∨ Exited out.1 id

/-- New commands that clear nothing, in front of the pending ones. Every command but `Cmd.finish`
leaves its commands this way. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem CmdKeepsMask.of_prefix {m m' : RunMachine ν σ β ε δ ι α χ St}
    {rest : List (Cmd ν σ β ε δ ι α)} (aged : MaskAged m m') (pre : List (Cmd ν σ β ε δ ι α))
    (clear : noClear pre = true) : CmdKeepsMask m rest (m', pre ++ rest) := by
  refine ⟨aged, ?_⟩
  intro id mem
  rcases List.mem_append.mp mem with new | old
  · exact absurd new (not_mem_of_noClear clear id)
  · exact Or.inl old

/-- A list that clears nothing meets the pending condition. Each list that a decision starts a loop
with is such a list. A step of `maskRuns_decisionLift`. -/
@[semantics "scope-lifetime-finalization"]
theorem clearsExited_of_noClear {m : RunMachine ν σ β ε δ ι α χ St}
    {cmds : List (Cmd ν σ β ε δ ι α)} (clear : noClear cmds = true) : ClearsExited m cmds :=
  fun id mem => absurd mem (not_mem_of_noClear clear id)

/-- A dispatcher task's commands clear nothing. A step of `maskRuns_decisionLift`. -/
@[semantics "scope-lifetime-finalization"]
theorem taskCmds_noClear (task : Task ν σ β ε δ ι α) : noClear (taskCmds task) = true := by
  cases task <;> rfl

/-- **The command condition.** Just before `Cmd.exitDone` clears a fiber, the fiber has exited, or
its stack is empty, or its flag is its base. The condition reads the machine before the
clearing: `RunFiber.cleared` empties the stack and keeps the flag, so emptiness after it protects
nothing.

`Cmd.finish` also clears, through `exitFiber.exitStore`. It publishes the fiber first, in the
same step, so it asks for nothing. Every other command clears no stack. -/
def ClearReady (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) :
    Cmd ν σ β ε δ ι α → Prop
  | Cmd.exitDone id => ∀ f, m.fiber? id = some f →
      f.exit.isSome = true ∨ f.frame.stack = [] ∨ bases[id.value]? = some f.frame.interruptible
  | _ => True

/-- **Clearing a stack keeps the chain exactly where the flag is the base.** `RunFiber.cleared`
empties the stack and keeps the flag, and the chain over an empty stack is the flag's equation
with the base. It is Codex's connector, as written: `lift/candidate.lean.txt` under
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/dogfood-review-1406/`.
A step of `driveStep_maskRuns`: the case of `Cmd.exitDone` on a fiber that has not exited. -/
@[semantics "scope-lifetime-finalization"]
theorem cleared_maskChain_iff (base : Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) :
    MaskChain base (f.cleared interp).frame.interruptible (f.cleared interp).frame.stack ↔
      f.frame.interruptible = base :=
  Iff.rfl

end Pending


/-! ### The driver's helpers -/

section Helpers

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- A posted task writes its owner's dispatcher, or it halts. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.postTask {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α) :
    MaskAged m (m₁.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact h
  · rename_i o found
    exact h.update (RunMachine.mem_of_fiber? found) (MaskLater.refl o)

/-- The drain of owed resumes posts tasks. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.drainOwed {m : RunMachine ν σ β ε δ ι α χ St}
    (owed : List (Owed (Prim ν σ β ε δ ι α))) :
    ∀ {m₁ : RunMachine ν σ β ε δ ι α χ St}, MaskAged m m₁ → MaskAged m (drainOwed m₁ owed).1 := by
  induction owed with
  | nil =>
    intro m₁ h
    exact h
  | cons entry rest ih =>
    intro m₁ h
    unfold Machine.drainOwed
    split
    · exact ih h
    · exact ih (h.postTask _ _ _)

/-- The drain of owed resumes issues resumes only. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem drainOwed_noClear (owed : List (Owed (Prim ν σ β ε δ ι α))) :
    ∀ (m₁ : RunMachine ν σ β ε δ ι α χ St), noClear (drainOwed m₁ owed).2 = true := by
  induction owed with
  | nil =>
    intro m₁
    rfl
  | cons entry rest ih =>
    intro m₁
    unfold Machine.drainOwed
    split
    · exact ih m₁
    · exact ih _

/-- A spawn appends one fiber, born at its start flag. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem spawn_maskAged {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (interp : RunInterp ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat) :
    MaskAged m (spawn interp m₁ parent program options site).1 :=
  h.make _ _ _ _ _ rfl rfl

/-- A child's start is an evaluation command, or a task on the parent's dispatcher. It changes no
fiber of the table. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem start_keepsMask {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (parent : RunFiber ν σ β ε δ ι α χ) (child : FiberId) (immediately : Bool) :
    MaskAged m (start m₁ parent child immediately).1 ∧
      MaskLater parent (start m₁ parent child immediately).2.1 ∧
      noClear (start m₁ parent child immediately).2.2 = true := by
  unfold start
  split
  · exact ⟨h, MaskLater.refl _, rfl⟩
  · exact ⟨h, MaskLater.refl _, rfl⟩

/-- A race's entrant is a spawn. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem launchEntrant_maskAged {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat) (host : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (site : List Nat) :
    MaskAged m (launchEntrant interp raceId m₁ host program site).1 :=
  spawn_maskAged h interp host program ⟨true, true, Supervision.MaskMode.interruptible⟩ site

/-- The parallel close's daemons are spawns. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem forkFinalizers_maskAged (interp : RunInterp ν σ β ε δ ι α χ St)
    (host : RunFiber ν σ β ε δ ι α χ) (programs : List (Prim ν σ β ε δ ι α)) :
    ∀ {m m₁ : RunMachine ν σ β ε δ ι α χ St}, MaskAged m m₁ →
      MaskAged m (forkFinalizers interp m₁ host programs).1 := by
  induction programs with
  | nil =>
    intro m m₁ h
    exact h
  | cons program rest ih =>
    intro m m₁ h
    exact ih (spawn_maskAged h interp host program ⟨true, true, Supervision.MaskMode.inherit⟩ [])

/-- A fork: the child is born, and its start is an evaluation or a task on the parent. A step of
`evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem fork_keepsMask {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (interp : RunInterp ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat)
    (immediately : Bool) :
    MaskAged m (start (spawn interp m₁ parent program options site).1
        (spawn interp m₁ parent program options site).2.1
        (spawn interp m₁ parent program options site).2.2 immediately).1 ∧
      MaskLater parent (start (spawn interp m₁ parent program options site).1
        (spawn interp m₁ parent program options site).2.1
        (spawn interp m₁ parent program options site).2.2 immediately).2.1 ∧
      noClear (start (spawn interp m₁ parent program options site).1
        (spawn interp m₁ parent program options site).2.1
        (spawn interp m₁ parent program options site).2.2 immediately).2.2 = true :=
  start_keepsMask (spawn_maskAged h interp parent program options site) _ _ immediately

/-- `forkChild` sets the middleware latch before its spawn, and a daemon fork does not. Neither
changes a fiber. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem middleware_maskAged {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (daemon : Bool) :
    MaskAged m (if daemon = true then m₁ else { m₁ with middlewareInstalled := true }) := by
  cases daemon
  · exact h
  · exact h

/-- A countdown park adds an observer to its first live target, and it pushes its cleanup as an
`asyncFinalizer` frame, which is neutral. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem countdownPark_keepsMask {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (interp : RunInterp ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (targets : List FiberId) (resumeWith : Resume ν) (failFast : Bool) :
    MaskAged m (countdownPark interp m₁ f targets resumeWith failFast).1 ∧
      MaskLater f (countdownPark interp m₁ f targets resumeWith failFast).2.1 := by
  unfold countdownPark
  dsimp only
  split
  · exact ⟨h, MaskLater.refl _⟩
  · refine ⟨MaskAged.emit (MaskAged.modify ?_ _ _ ?_) _, MaskLater.refl _⟩
    · exact h
    · exact fun g => MaskLater.refl g

end Helpers


/-! ### One evaluation's facts, the exit path and the loop's write -/

section Exit

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- A halt changes no fiber. A step of `settle_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskAged.halt {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁) (why : Stuck) :
    MaskAged m (m₁.halt why) := h

/-- What one evaluation leaves. The machine has aged, and the fiber is a later state. No nested
command clears a fiber. A finished outcome has an empty stack. -/
def IterKeepsMask (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (it : Iter ν σ β ε δ ι α χ St) : Prop :=
  MaskAged m it.machine ∧ MaskLater f it.fiber ∧ noClear it.nested = true ∧
    ∀ exit, it.outcome = Outcome.finished exit → it.fiber.frame.stack = []

/-- An evaluation that starts from a later machine and a later fiber. A step of
`iteration_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem IterKeepsMask.rebase {m m₁ : RunMachine ν σ β ε δ ι α χ St}
    {f f₁ : RunFiber ν σ β ε δ ι α χ} {it : Iter ν σ β ε δ ι α χ St} (aged : MaskAged m m₁)
    (later : MaskLater f f₁) (h : IterKeepsMask m₁ f₁ it) : IterKeepsMask m f it :=
  ⟨aged.trans h.1, later.trans h.2.1, h.2.2.1, h.2.2.2⟩

/-- **The driver issues `Cmd.finish` at an empty stack.** `settle` issues `Cmd.finish` at a finished
outcome alone, and it writes this fiber back. It is the completed exit's statement at its event,
and no state invariant of an exited fiber. Its consumer is the bracket's law. -/
@[semantics "scope-lifetime-finalization"]
theorem IterKeepsMask.finished_stack {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {it : Iter ν σ β ε δ ι α χ St} (kept : IterKeepsMask m f it)
    {exit : Exit β ε δ ι α} (finished : it.outcome = Outcome.finished exit) :
    it.fiber.frame.stack = [] :=
  kept.2.2.2 exit finished

/-- **The driver issues `Cmd.finish` at the base.** With the chain over the evaluated fiber, a
finished fiber that has not exited has the base as its flag: the chain is kept, and the stack is
empty. So a fiber's first publication is at its start flag. -/
@[semantics "scope-lifetime-finalization"]
theorem IterKeepsMask.finished_flag {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {it : Iter ν σ β ε δ ι α χ St} (kept : IterKeepsMask m f it)
    {base : Bool} (valid : MaskChain base f.frame.interruptible f.frame.stack)
    (live : it.fiber.exit = none) {exit : Exit β ε δ ι α}
    (finished : it.outcome = Outcome.finished exit) : it.fiber.frame.interruptible = base := by
  have chain := kept.2.1.2.2 live base valid
  rw [kept.finished_stack finished] at chain
  exact chain

/-- The top of a loop iteration writes the code and the deferred flag, and the op counter counts.
A step of `iteration_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem runloopTop_maskLater (f : RunFiber ν σ β ε δ ι α χ) :
    MaskLater f (countOp (runloopTop f)) := by
  unfold runloopTop
  split
  · exact MaskLater.refl f
  · exact MaskLater.refl f

/-- A yield's injection writes the code and a trace event. A step of `iteration_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem injectYield_keepsMask {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {y : Bool} {it : Iter ν σ β ε δ ι α χ St} (injected : injectYield m f y = some it) :
    MaskAged m it.machine ∧ MaskLater f it.fiber := by
  unfold injectYield at injected
  split at injected
  · cases injected
    exact ⟨MaskAged.refl m, MaskLater.refl f⟩
  · cases injected

/-- A race's entry allocates its bookkeeping and writes the code. A step of
`evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem beginRace_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (entrants : List (Prim ν σ β ε δ ι α)) (site : Option (List Nat)) :
    IterKeepsMask m f (beginRace interp m f y entrants site) :=
  ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩

/-- A race's registration marks the race, and its two commands clear nothing. A step of
`evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem registerRace_keepsMask (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (y : Bool) (raceId : Nat) : IterKeepsMask m f (registerRace m f y raceId) := by
  unfold registerRace
  split
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩

/-- **The exit path publishes a fiber before it clears it.** So each clearing of the exit path is of
a fiber that has exited, and the `Cmd.exitDone` that it issues names the published fiber. Its
re-entry for the children writes the code only. A step of `driveStep_keepsMask`: the case of
`Cmd.finish`. -/
@[semantics "scope-lifetime-finalization"]
theorem exitFiber_keepsMask {m : RunMachine ν σ β ε δ ι α χ St}
    (interp : RunInterp ν σ β ε δ ι α χ St) {f₀ f : RunFiber ν σ β ε δ ι α χ}
    (exit : Exit β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) (mem : f₀ ∈ m.fibers)
    (later : MaskLater f₀ f) (bound : f.id.value < m.nextId) :
    CmdKeepsMask m rest ((exitFiber interp m f exit).1, (exitFiber interp m f exit).2 ++ rest) := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    dsimp only
    refine CmdKeepsMask.of_prefix
      (MaskAged.emit (MaskAged.update_old (MaskAged.refl m) mem ?_) _) _ rfl
    exact later
  · unfold exitFiber.exitStore
    dsimp only
    split
    · refine CmdKeepsMask.of_prefix
        (MaskAged.update_old (MaskAged.emit (MaskAged.update_old (MaskAged.refl m) mem ?_) _)
          mem ?_) _ rfl
      · exact MaskLater.of_exited later.1 rfl
      · exact MaskLater.of_exited later.1 rfl
    · refine ⟨MaskAged.emit (MaskAged.update_old (MaskAged.refl m) mem ?_) _, ?_⟩
      · exact MaskLater.of_exited later.1 rfl
      · intro id pending
        rcases List.mem_append.mp pending with issued | old
        · refine Or.inr ?_
          rcases List.mem_append.mp issued with observed | cleared
          · obtain ⟨observer, -, impossible⟩ := List.mem_map.mp observed
            cases impossible
          · rcases List.mem_cons.mp cleared with same | other
            · cases same
              refine ⟨bound, ?_⟩
              intro g memg sameId
              obtain ⟨g₀, -, rfl⟩ := List.mem_map.mp memg
              by_cases matched : g₀.id = (f.publish exit).id
              · rw [if_pos matched]
                rfl
              · rw [if_neg matched] at sameId
                exact absurd sameId matched
            · rcases List.mem_cons.mp other with drain | none
              · cases drain
              · cases none
        · exact Or.inl old

/-- What the loop does with an evaluation: it writes the fiber back, and it issues the continuing
command, which clears nothing. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem settle_keepsMask {m : RunMachine ν σ β ε δ ι α χ St} {f₀ : RunFiber ν σ β ε δ ι α χ}
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (it : Iter ν σ β ε δ ι α χ St)
    (mem : f₀ ∈ m.fibers) (aged : MaskAged m it.machine) (later : MaskLater f₀ it.fiber)
    (nested : noClear it.nested = true) :
    CmdKeepsMask m rest (settle id rest it) := by
  unfold settle
  split
  · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ ?_
    · exact later
    · rw [noClear_append, nested]
      rfl
  · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ ?_
    · exact later
    · rw [noClear_append, nested]
      rfl
  · split
    · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ ?_
      · exact later
      · rw [noClear_append, nested]
        rfl
    · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ nested
      exact later
  · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ nested
    exact later
  · refine CmdKeepsMask.of_prefix (MaskAged.update_old aged mem ?_) _ ?_
    · exact later
    · rw [noClear_append, nested]
      rfl
  · refine ⟨MaskAged.halt (MaskAged.update_old aged mem ?_) _, fun _ pending => nomatch pending⟩
    exact later

/-- No outcome that a `withFiber` action reads off the machine is a finished one. A step of
`withFiber_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem outcomeOf_unfinished (stuck : Option Stuck) (parked : Bool) (exit : Exit β ε δ ι α)
    (finished : (match stuck with
      | some why => (Outcome.stuck why : Outcome ν σ β ε δ ι α)
      | none => if parked = true then Outcome.parked else Outcome.continue_) =
        Outcome.finished exit) : False := by
  split at finished
  · cases finished
  · split at finished <;> cases finished

end Exit


/-! ### Interrupts, links and observers -/

section Interrupts

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- An interrupt's record writes the cause, the deferred flag, the code and the park. It keeps the
flag and the stack. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptRecord_maskLater (interp : RunInterp ν σ β ε δ ι α χ St) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    MaskLater f (interruptRecord interp who extra f).1 := by
  unfold interruptRecord
  dsimp only
  (repeat' split) <;> exact MaskLater.refl f

/-- Interrupts in list order: each is a record and at most one evaluation command. A step of
`fireObserver_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptEach_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α) (targets : List FiberId) :
    ∀ {m : RunMachine ν σ β ε δ ι α χ St}
      (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)),
      MaskAged m acc.1 → noClear acc.2 = true →
        MaskAged m (interruptEach interp who extra targets acc).1 ∧
          noClear (interruptEach interp who extra targets acc).2 = true := by
  induction targets with
  | nil =>
    intro m acc h clear
    exact ⟨h, clear⟩
  | cons t rest ih =>
    intro m acc h clear
    rw [interruptEach_cons]
    cases found : acc.1.fiber? t with
    | none => exact ih acc h clear
    | some g =>
      refine ih _ (MaskAged.emit (h.update (RunMachine.mem_of_fiber? found) ?_) _) ?_
      · exact interruptRecord_maskLater interp (some who) extra g
      · dsimp only
        rw [noClear_append, clear]
        cases (interruptRecord interp (some who) extra g).2 <;> rfl

/-- The fail-fast interrupts of a countdown, which run only at its first failure. A step of
`fireObserver_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptEach_if_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α) (targets : List FiberId)
    {m : RunMachine ν σ β ε δ ι α χ St}
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) (first : Bool)
    (h : MaskAged m acc.1) (clear : noClear acc.2 = true) :
    MaskAged m (if first = true then interruptEach interp who extra targets acc else acc).1 ∧
      noClear (if first = true then interruptEach interp who extra targets acc else acc).2 =
        true := by
  cases first
  · exact ⟨h, clear⟩
  · exact interruptEach_keepsMask interp who extra targets acc h clear

/-- A scope's link records an interrupt, or it adds an observer. A step of `driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem linkScope_keepsMask {m m₁ : RunMachine ν σ β ε δ ι α χ St} (h : MaskAged m m₁)
    (interp : RunInterp ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α) :
    MaskAged m (linkScope interp m₁ mode scope target interruptor extra).1 ∧
      noClear (linkScope interp m₁ mode scope target interruptor extra).2 = true := by
  unfold linkScope
  split
  · exact ⟨h, rfl⟩
  · split
    · exact ⟨h, rfl⟩
    · rename_i t found
      split
      rename_i recorded applyNow record
      have later := interruptRecord_maskLater interp interruptor extra t
      rw [record] at later
      refine ⟨MaskAged.emit (h.update (RunMachine.mem_of_fiber? found) later) _, ?_⟩
      cases applyNow <;> rfl
  · split
    · exact ⟨h, rfl⟩
    · rename_i t found
      split
      · exact ⟨h, rfl⟩
      · split
        · exact ⟨h, rfl⟩
        · refine ⟨MaskAged.emit (MaskAged.modify ?_ _ _ ?_) _, rfl⟩
          · exact h
          · exact fun g => MaskLater.refl g

/-- An observer's firing keeps the machine, and it issues no clearing. It writes children, pending
parks, observers and races, and it records the fail-fast interrupts. A step of
`driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem fireObserver_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) (observer : Observer) :
    MaskAged acc.1 (fireObserver interp id exit acc observer).1 ∧
      (noClear acc.2 = true → noClear (fireObserver interp id exit acc observer).2 = true) := by
  unfold fireObserver
  dsimp only
  split
  · exact ⟨MaskAged.refl _, fun clear => noClear_append_of clear rfl⟩
  · refine ⟨MaskAged.modify ?_ _ _ ?_, fun clear => clear⟩
    · exact MaskAged.refl _
    · exact fun g => MaskLater.refl g
  · split
    · exact ⟨MaskAged.refl _, fun clear => clear⟩
    · exact ⟨MaskAged.refl _, fun clear => clear⟩
  · rename_i waiter token
    split
    · exact ⟨MaskAged.refl _, fun clear => clear⟩
    · rename_i w found
      split
      · exact ⟨MaskAged.refl _, fun clear => clear⟩
      · rename_i p pending
        have step := interruptEach_if_keepsMask interp waiter (interp.stackAnnotations waiter)
          p.remaining (m := acc.1)
          (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], [])
          (p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess) (MaskAged.refl _) rfl
        split
        · refine ⟨MaskAged.update_old ?_ (RunMachine.mem_of_fiber? found) ?_, fun clear => ?_⟩
          · exact step.1
          · exact MaskLater.refl w
          · exact noClear_append_of (noClear_append_of clear step.2) rfl
        · refine ⟨MaskAged.update_old (MaskAged.modify ?_ _ _ ?_)
            (RunMachine.mem_of_fiber? found) ?_, fun clear => ?_⟩
          · exact step.1
          · exact fun g => MaskLater.refl g
          · exact MaskLater.refl w
          · exact noClear_append_of clear step.2
  · split
    · exact ⟨MaskAged.refl _, fun clear => clear⟩
    · rename_i race found
      split
      · refine ⟨MaskAged.refl _, fun clear => ?_⟩
        rw [noClear_append, clear]
        cases registering : race.registering <;> rfl
      · exact ⟨MaskAged.refl _, fun clear => clear⟩
  · exact ⟨MaskAged.refl _, fun clear => clear⟩

/-- The edit of an `interruptFrom` decision is a record. It keeps the allocator. A step of
`maskRuns_decisionLift`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptEdit_maskAged (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (who : Option FiberId) (extra : ReasonAnnotations α)
    (target : FiberId) (t : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? target = some t) :
    MaskAged m (Lift.interruptEdit interp m who extra target t) ∧
      (Lift.interruptEdit interp m who extra target t).nextId = m.nextId := by
  unfold Lift.interruptEdit
  dsimp only
  split
  · exact ⟨(MaskAged.refl m).update (RunMachine.mem_of_fiber? found)
      (interruptRecord_maskLater interp who extra t), rfl⟩
  · exact ⟨(MaskAged.refl m).update (RunMachine.mem_of_fiber? found)
      (interruptRecord_maskLater interp who extra t), rfl⟩

end Interrupts


/-! ### One evaluation of the frame evaluator -/

section Evaluate

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The fiber machine's read of a frame step. A step that goes on gives the next frame, and a
finished step retains `frameExitState`. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem finishFrame_keepsMask (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (y : Bool) (next : FrameStep ν σ β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α))
    (nested : List (Cmd ν σ β ε δ ι α))
    (chain : ∀ frame, next = FrameStep.running frame → ∀ base,
      MaskChain base f.frame.interruptible f.frame.stack →
        MaskChain base frame.interruptible frame.stack)
    (empty : ∀ exit, next = FrameStep.finished exit → (frameExitState f.frame).stack = [])
    (clear : noClear nested = true) :
    IterKeepsMask m f (evaluatePrim.finishFrame m f y next events nested) := by
  unfold evaluatePrim.finishFrame
  dsimp only
  split
  · rename_i frame
    exact ⟨MaskAged.refl m, ⟨rfl, fun live => live, fun _ base valid => chain frame rfl base valid⟩,
      clear, fun _ h => nomatch h⟩
  · rename_i exit
    exact ⟨MaskAged.refl m,
      ⟨rfl, fun live => live, fun _ base valid => frameExitState_maskChain base f.frame valid⟩,
      clear, fun _ _ => empty exit rfl⟩

/-- The delegation to the frame machine: `step_maskChain` for a step that goes on, and
`step_finished_stack` for a finished one. A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem stepFrame_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) :
    IterKeepsMask m f (evaluatePrim.stepFrame interp m f y) :=
  finishFrame_keepsMask m f y (f.frame.step interp.toPrimInterp).1
    (f.frame.step interp.toPrimInterp).2 []
    (fun frame running base valid =>
      step_maskChain base interp.toPrimInterp f.frame valid frame running)
    (fun exit finished => step_finished_stack interp.toPrimInterp f.frame exit finished) rfl

/-- An exit that meets an `onExit` frame whose finalizer is a program: the pop keeps the chain
(`getCont_maskChain`). Every other exit is the frame machine's step. A step of
`evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem finalizerOr_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (exit : Exit β ε δ ι α) : IterKeepsMask m f (evaluatePrim.finalizerOr interp m f y exit) := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact ⟨MaskAged.refl m,
        ⟨rfl, fun live => live, fun _ base valid => getCont_maskChain base f.frame _ _ _ valid⟩,
        rfl, fun _ h => nomatch h⟩
    · exact stepFrame_keepsMask interp m f y
  · exact stepFrame_keepsMask interp m f y

/-- `fiberInterruptAs` records one interrupt, and its commands clear nothing. A step of
`evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptAs_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (target who : FiberId) :
    IterKeepsMask m f (evaluatePrim.interruptAs interp m f y target who) := by
  unfold evaluatePrim.interruptAs
  split
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · rename_i t found
    split
    rename_i recorded applyNow record
    have later := interruptRecord_maskLater interp (some who) (interp.stackAnnotations f.id) t
    rw [record] at later
    refine ⟨MaskAged.emit ((MaskAged.refl m).update (RunMachine.mem_of_fiber? found) later) _,
      MaskLater.refl f, ?_, fun _ h => nomatch h⟩
    cases applyNow <;> rfl

/-- Each `withFiber` action keeps the machine and the fiber. The two regions' entries keep the chain
(`uninterruptible_maskChain`, `interruptibleRegion_maskChain`), and so does the mask's getter.
A fork is a birth. Every other action writes no flag and no stack, or it pushes a neutral frame.
A step of `evaluatePrim_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (action : WithFiberAction ν σ β ε δ ι α χ) :
    IterKeepsMask m f (evaluatePrim.withFiber interp m f y action) := by
  unfold evaluatePrim.withFiber
  dsimp only
  split
  · rename_i program options site
    have facts := fork_keepsMask (middleware_maskAged (MaskAged.refl m) options.daemon) interp f
      program options site options.startImmediately
    exact ⟨facts.1, facts.2.1, noClear_append_of facts.2.2 (noClear_ite _ rfl rfl),
      fun _ h => nomatch h⟩
  · rename_i program options scope site
    have facts := fork_keepsMask (MaskAged.refl m) interp f program
      { options with daemon := true } site options.startImmediately
    exact ⟨facts.1, facts.2.1, noClear_append_of facts.2.2 rfl, fun _ h => nomatch h⟩
  · rename_i program options site
    split
    · have facts := fork_keepsMask (MaskAged.refl m) interp f program
        { options with daemon := true } site options.startImmediately
      exact ⟨facts.1, facts.2.1, noClear_append_of facts.2.2 rfl, fun _ h => nomatch h⟩
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · rename_i target scope
    have facts := linkScope_keepsMask (MaskAged.refl m) interp Supervision.ScopeMode.fiberRunIn
      scope target (some target) ReasonAnnotations.empty
    exact ⟨facts.1, MaskLater.refl f, facts.2,
      fun exit finished => (outcomeOf_unfinished _ _ exit finished).elim⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact interruptAs_keepsMask interp m f y _ _
  · split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f,
      noClear_append_of (noClear_map _ (fun _ => rfl) _) rfl, fun _ h => nomatch h⟩
  · rename_i targets
    have facts := countdownPark_keepsMask (MaskAged.refl m) interp f targets Resume.exitsValue false
    exact ⟨facts.1, facts.2, rfl,
      fun exit finished => (outcomeOf_unfinished _ _ exit finished).elim⟩
  · rename_i targets
    have facts := countdownPark_keepsMask (MaskAged.refl m) interp f targets Resume.exitsValue true
    exact ⟨facts.1, facts.2, rfl,
      fun exit finished => (outcomeOf_unfinished _ _ exit finished).elim⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · rename_i snapshot
    have facts := countdownPark_keepsMask (MaskAged.refl m) interp f
      (f.children.filter fun c => !(snapshot.contains c)) Resume.void false
    exact ⟨facts.1, facts.2, rfl,
      fun exit finished => (outcomeOf_unfinished _ _ exit finished).elim⟩
  · exact beginRace_keepsMask interp m f y _ _
  · exact ⟨MaskAged.refl m,
      ⟨rfl, fun live => live, fun _ base valid => uninterruptible_maskChain base f.frame valid⟩,
      rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m,
      ⟨rfl, fun live => live,
        fun _ base valid => interruptibleRegion_maskChain base f.frame valid⟩,
      rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨forkFinalizers_maskAged interp f _ (MaskAged.refl m), MaskLater.refl f,
      noClear_append_of (noClear_map _ (fun _ => rfl) _) rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · refine ⟨MaskAged.mapFibers (MaskAged.refl m) _ ?_, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    exact fun g => MaskLater.refl g
  · split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · exact ⟨MaskAged.refl m,
      ⟨rfl, fun live => live, fun _ base valid => uninterruptible_maskChain base f.frame valid⟩,
      rfl, fun _ h => nomatch h⟩

/-- **One evaluation of the frame evaluator keeps the machine and the fiber.** The parks push the
neutral `asyncFinalizer` frame. The actions are `withFiber_keepsMask`. Every other primitive is
the frame machine's step. A step of `saved_mask_chain_runs`, through `EvaluatorKeepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem evaluatePrim_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) :
    IterKeepsMask m f (evaluatePrim interp m f y) := by
  unfold evaluatePrim
  split
  · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · dsimp only
    split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · split
      · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
      · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
  · split
    · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact registerRace_keepsMask m f y _
    · rename_i targets _
      have facts :=
        countdownPark_keepsMask (MaskAged.refl m) interp f targets Resume.exitsValue false
      split
      rename_i m' f' parked park
      rw [park] at facts
      cases parked
      · exact ⟨facts.1, facts.2, rfl, fun _ h => nomatch h⟩
      · exact ⟨facts.1, facts.2, rfl, fun _ h => nomatch h⟩
    · split
      · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
      · rename_i t found
        split
        · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
        · refine ⟨MaskAged.emit (MaskAged.update_old ?_ (RunMachine.mem_of_fiber? found) ?_) _,
            MaskLater.refl f, rfl, fun _ h => nomatch h⟩
          · exact MaskAged.refl m
          · exact MaskLater.refl t
    · split
      · split
        · exact withFiber_keepsMask interp m f y _
        · exact stepFrame_keepsMask interp m f y
      · split
        · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
        · exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
      · exact finalizerOr_keepsMask interp m f y _
      · exact finalizerOr_keepsMask interp m f y _
      · exact stepFrame_keepsMask interp m f y

end Evaluate


/-! ### One command, and the lift through `Machine.Lift` -/

section Step

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
  (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)]

/-- **The evaluator's premise.** Each evaluation keeps the machine and the fiber. The command loop
takes its evaluator as an instance, so the lift takes this one premise. The frame evaluator
meets it (`evaluatePrim_evaluatorKeepsMask`). A run of a compiled program uses another
evaluator, `Program.evaluateNative` (`src/Effect4/Program/Compile.lean`). -/
def EvaluatorKeepsMask (interp : RunInterp ν σ β ε δ ι α χ St) : Prop :=
  ∀ (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool),
    IterKeepsMask m f (evaluator.evaluate interp m f y)

/-- One loop iteration: the loop's top, the counter, the injection, then the evaluator. A step of
`driveStep_keepsMask`. -/
@[semantics "scope-lifetime-finalization"]
theorem iteration_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) : IterKeepsMask m f (iteration interp m f y) := by
  unfold iteration
  dsimp only
  split
  · rename_i it injected
    obtain ⟨aged, later⟩ := injectYield_keepsMask injected
    exact (evaluates it.machine it.fiber it.yielding).rebase aged
      ((runloopTop_maskLater f).trans later)
  · exact (evaluates m (countOp (runloopTop f)) y).rebase (MaskAged.refl m) (runloopTop_maskLater f)

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- **Each command keeps the machine**, where a `Cmd.exitDone` names a fiber that has exited. Each
`Cmd.exitDone` that the command leaves was pending, or it names the fiber that `Cmd.finish` has
published. A step of `maskRuns_stepKeeps` and of `driveStep_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem driveStep_keepsMask (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp)
    (m : RunMachine ν σ β ε δ ι α χ St) (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (bound : ∀ f ∈ m.fibers, f.id.value < m.nextId)
    (exited : ∀ id, c = Cmd.exitDone id → ∀ f, m.fiber? id = some f → f.exit.isSome = true) :
    CmdKeepsMask m rest (driveStep interp m c rest) := by
  cases c with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      split
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
      · refine CmdKeepsMask.of_prefix (MaskAged.emit
          (MaskAged.update_old (MaskAged.refl m) (RunMachine.mem_of_fiber? found) ?_) _) [_] rfl
        exact MaskLater.refl f
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      have kept := iteration_keepsMask interp evaluates m f yielding
      exact settle_keepsMask id rest _ (RunMachine.mem_of_fiber? found) kept.1 kept.2.1 kept.2.2.1
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      have kept := evaluates m f yielding
      exact settle_keepsMask id rest _ (RunMachine.mem_of_fiber? found) kept.1 kept.2.1 kept.2.2.1
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i t found
      split
      · split
        · refine CmdKeepsMask.of_prefix (MaskAged.emit
            (MaskAged.update_old (MaskAged.refl m) (RunMachine.mem_of_fiber? found) ?_) _) [_] rfl
          exact MaskLater.refl t
        · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
  | launch raceId =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i race _
      split
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
      · rename_i program more _
        split
        · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
        · split
          · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
          · rename_i host _
            have aged := launchEntrant_maskAged (MaskAged.refl m) interp raceId host program
              (race.nextSite.getD [])
            refine CmdKeepsMask.of_prefix ?_ [_, _, _] rfl
            exact aged
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · rename_i race c _ _
      split
      · rename_i exit _
        have fired := fireObserver_keepsMask interp child exit
          (m.updateRace
            { race with state := { race.state with live := race.state.live ++ [child] } }, [])
          (Observer.raceCallback raceId)
        refine CmdKeepsMask.of_prefix ?_ _ (fired.2 rfl)
        exact fired.1
      · refine CmdKeepsMask.of_prefix (MaskAged.modify ?_ _ _ ?_) [] rfl
        · exact MaskAged.refl m
        · exact fun g => MaskLater.refl g
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i race _
      split
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
      · rename_i f found
        split
        · exact settle_keepsMask _ rest _ (RunMachine.mem_of_fiber? found) (MaskAged.refl m)
            (MaskLater.refl f) rfl
        · exact settle_keepsMask _ rest _ (RunMachine.mem_of_fiber? found) (MaskAged.refl m)
            (MaskLater.refl f) rfl
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i g found
      have later := interruptRecord_maskLater interp who extra g
      refine CmdKeepsMask.of_prefix ?_ _ ?_
      · exact MaskAged.emit ((MaskAged.refl m).update (RunMachine.mem_of_fiber? found) later) _
      · exact noClear_ite _ rfl rfl
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      exact settle_keepsMask _ rest _ (RunMachine.mem_of_fiber? found) (MaskAged.refl m)
        (MaskLater.refl f) rfl
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [_] rfl
    · split
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [_] rfl
      · split
        · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [_, _] rfl
        · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [_] rfl
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · split
      · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
      · refine CmdKeepsMask.of_prefix (MaskAged.modify (MaskAged.modify ?_ _ _ ?_) _ _ ?_) [] rfl
        · exact MaskAged.refl m
        · exact fun g => MaskLater.refl g
        · exact fun g => MaskLater.refl g
  | observe id exit observer =>
    simp only [driveStep]
    have fired := fireObserver_keepsMask interp id exit (m, []) observer
    refine CmdKeepsMask.of_prefix ?_ _ (fired.2 rfl)
    exact fired.1
  | exitDone id =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      refine CmdKeepsMask.of_prefix
        ((MaskAged.refl m).update (RunMachine.mem_of_fiber? found) ?_) [] rfl
      exact MaskLater.of_exited rfl (exited id rfl f found)
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      exact settle_keepsMask _ rest _ (RunMachine.mem_of_fiber? found) (MaskAged.refl m)
        (MaskLater.refl f) rfl
  | link mode scope target interruptor extra =>
    simp only [driveStep]
    have linked := linkScope_keepsMask (MaskAged.refl m) interp mode scope target interruptor extra
    refine CmdKeepsMask.of_prefix ?_ _ linked.2
    exact linked.1
  | finish id exit =>
    simp only [driveStep]
    split
    · exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl
    · rename_i f found
      exact exitFiber_keepsMask interp exit rest (RunMachine.mem_of_fiber? found) (MaskLater.refl f)
        (bound f (RunMachine.mem_of_fiber? found))
  | drainDue =>
    simp only [driveStep]
    refine CmdKeepsMask.of_prefix ?_ _ (drainOwed_noClear _ _)
    exact MaskAged.drainOwed _ (MaskAged.refl m)
  | wake list phase =>
    simp only [driveStep]
    exact CmdKeepsMask.of_prefix (MaskAged.refl m) [] rfl

/-! ## The invariant through a command, a decision and a replay -/

/-- **Each command keeps the invariant under the command condition.** `Cmd.exitDone` reads the
condition's three alternatives. Every other command moves each fiber to a later state, or it
bears a fiber at its start flag. It is the field `command` of `saved_mask_chain_runs`.

It does not say that a pending `Cmd.exitDone` will meet the condition: `maskRuns_stepKeeps`
does, for the driver's own commands. -/
@[semantics "scope-lifetime-finalization"]
theorem driveStep_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (kept : MaskRuns bases m) (ready : ClearReady bases m c) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep interp m c rest).1 := by
  cases c with
  | exitDone id =>
    refine ⟨bases, List.prefix_refl _, ?_⟩
    simp only [driveStep]
    split
    · exact kept
    · rename_i f found
      refine ⟨kept.1, ?_⟩
      intro g mem
      obtain ⟨g₀, mem₀, rfl⟩ := List.mem_map.mp mem
      by_cases matched : g₀.id = (f.cleared interp).id
      · rw [if_pos matched]
        obtain ⟨base, entry, valid⟩ := kept.2 f (RunMachine.mem_of_fiber? found)
        refine ⟨base, entry, fun live => (cleared_maskChain_iff base interp f).mpr ?_⟩
        have live' : f.exit = none := live
        rcases ready f found with exited | empty | atBase
        · rw [live'] at exited
          cases exited
        · have chain := valid live'
          rw [empty] at chain
          exact chain
        · rw [RunMachine.id_of_fiber? found, atBase] at entry
          exact Option.some.inj entry
      · rw [if_neg matched]
        exact kept.2 g₀ mem₀
  | _ =>
    exact kept.aged (driveStep_keepsMask interp evaluates m _ rest (fun f mem => kept.bound mem)
      (fun id same => by cases same)).1

/-- **The driver's own commands keep the invariant and the pending condition.** It is the command
premise of `Machine.Lift`, with the invariant as the machine fact and `ClearsExited` as the fact
on the pending commands. It is the field `guarded` of `saved_mask_chain_runs`. -/
@[semantics "scope-lifetime-finalization"]
theorem maskRuns_stepKeeps (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (ts : List (Machine.Task ν σ β ε δ ι α)) :
    Lift.StepKeeps basesOrder interp
      (Lift.Guarded (fun bases m => MaskRuns bases m) (fun _ m cmds => ClearsExited m cmds)
        (fun _ _ _ => True) ts) := by
  intro bases m c rest running guarded
  obtain ⟨kept, pending⟩ := guarded
  have cleared := (pending running).1
  have step := driveStep_keepsMask interp evaluates m c rest (fun f mem => kept.bound mem)
    (fun id same f found =>
      (cleared id (by rw [same]; exact List.mem_cons_self ..)).2 f (RunMachine.mem_of_fiber? found)
        (RunMachine.id_of_fiber? found))
  obtain ⟨bases', le, kept'⟩ := kept.aged step.1
  refine ⟨bases', le, kept', fun _ => ⟨?_, trivial⟩⟩
  intro id mem
  rcases step.2 id mem with old | new
  · exact (cleared id (List.mem_cons_of_mem _ old)).aged step.1
  · exact new

/-- **Each decision's edits keep the invariant**: the premises of `Machine.Lift`'s decision lift.
The lift asks for no admission of a decision. A step of `stepDecisionState_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem maskRuns_decisionLift (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) :
    Lift.DecisionLift basesOrder interp (fun bases m => MaskRuns bases m)
      (fun _ m cmds => ClearsExited m cmds) (fun _ _ _ => True) (fun _ _ _ => True) where
  step := maskRuns_stepKeeps interp evaluates
  nil := fun _ _ => trivial
  evaluate := fun _ _ _ _ _ => clearsExited_of_noClear rfl
  drain := fun bases m owner f kept found => by
    refine ⟨kept.same ?_ rfl, trivial⟩
    refine MaskAged.update (MaskAged.refl m) (RunMachine.mem_of_fiber? found) ?_
    exact MaskLater.refl f
  ran := fun _ _ _ _ kept => kept
  task := fun _ _ _ t _ _ _ _ => ⟨clearsExited_of_noClear (taskCmds_noClear t), trivial⟩
  skip := fun _ _ _ _ _ => trivial
  yield := fun bases m id v kept => by
    refine kept.same (MaskAged.modify (MaskAged.refl m) _ _ ?_) (RunMachine.modify_nextId m id _)
    exact fun g => MaskLater.refl g
  interrupt := fun bases m who extra target t kept found =>
    kept.same (interruptEdit_maskAged interp m who extra target t found).1
      (interruptEdit_maskAged interp m who extra target t found).2
  middleware := fun _ _ kept => kept
  clockNone := fun bases _ _ _ kept _ _ => ⟨bases, List.prefix_refl _, kept⟩
  clockSome := fun bases m millis owed st kept _ _ => by
    obtain ⟨bases', le, kept'⟩ :=
      kept.aged (MaskAged.drainOwed [owed] (m₁ := { m with state := st }) (MaskAged.refl m))
    exact ⟨bases', le, kept',
      fun _ => clearsExited_of_noClear (noClear_append_of (drainOwed_noClear _ _) rfl)⟩
  answer := fun bases m id token answer kept running _ =>
    maskRuns_stepKeeps interp evaluates [] bases _ _ _ running
      ⟨kept, fun _ => ⟨clearsExited_of_noClear rfl, trivial⟩⟩

/-- The command loop keeps the invariant at every fuel, from commands that meet the pending
condition. Its consumer is a run entry such as `runFork`, which starts a loop outside a decision. -/
@[semantics "scope-lifetime-finalization"]
theorem driveState_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (fuel : Nat) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (kept : MaskRuns bases m) (pending : ClearsExited m cmds) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveState interp fuel m cmds).1 := by
  obtain ⟨bases', le, guarded⟩ := Lift.driveState_lift basesOrder interp _
    (maskRuns_stepKeeps interp evaluates []) fuel bases m cmds
    ⟨kept, fun _ => ⟨pending, trivial⟩⟩
  exact ⟨bases', le, guarded.1⟩

/-- Each decision keeps the invariant. It is the field `decision` of `saved_mask_chain_runs`. -/
@[semantics "scope-lifetime-finalization"]
theorem stepDecisionState_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (fuel : Nat) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (d : RunDecision ν σ β ε δ ι α)
    (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (stepDecisionState interp fuel m d).1 :=
  Lift.stepDecisionState_lift (maskRuns_decisionLift interp evaluates) fuel bases m d kept trivial

/-- With no admission to ask, every tape is admitted. A step of `replayEval_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem admittedReplay_true (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St),
      Lift.AdmittedReplay (fun bases m => MaskRuns bases m) (fun _ _ _ => True) interp fuel m tape
  | [], _ => trivial
  | _ :: tape, _ => fun _ => ⟨fun _ _ => trivial, fun _ => admittedReplay_true interp fuel tape _⟩

/-- **Each fiber of a reached machine that has not exited holds the chain at its start flag.** A
replay of any decision tape keeps the invariant, at a table that the first one is a prefix of.
It is the field `replay` of `saved_mask_chain_runs`, by `Lift.stepDecisionState_lift` and
`Lift.replayEval_lift`. -/
@[semantics "scope-lifetime-finalization"]
theorem replayEval_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (fuel : Nat) (tape : List (RunDecision ν σ β ε δ ι α))
    (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayEval interp fuel tape m).machine :=
  Lift.replayEval_lift basesOrder (fun bases m => MaskRuns bases m) (fun _ _ _ => True) interp fuel
    (fun bases m d _ kept _ => stepDecisionState_maskRuns interp evaluates fuel bases m d kept)
    tape bases m kept (admittedReplay_true interp fuel tape m)

end Step


/-! ### The frame evaluator, and the placed theorem -/

section Frames

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The frame evaluator meets the evaluator's premise. A step of `saved_mask_chain_runs`. -/
@[semantics "scope-lifetime-finalization"]
theorem evaluatePrim_evaluatorKeepsMask (interp : RunInterp ν σ β ε δ ι α χ St) :
    EvaluatorKeepsMask interp :=
  evaluatePrim_keepsMask interp

/-- The statements of the proposed registry claim `saved-mask-chain-runs`, at the frame evaluator.
Each field holds the invariant `MaskRuns` at a table of start flags. -/
structure MaskChainRuns (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v))
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] : Prop where
  /-- The empty machine holds the invariant at the empty table. -/
  empty : ∀ (state : St), MaskRuns [] (RunMachine.empty state : RunMachine ν σ β ε δ ι α χ St)
  /-- **A fiber's base is its start flag.** A fiber that `RunFiber.make` starts at the next id
  extends the table by its flag. -/
  start : ∀ (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (program : Prim ν σ β ε δ ι α) (flag : Bool) (budget : Nat × Bool) (context : χ),
    MaskRuns bases m →
      MaskRuns (bases ++ [flag])
        { m with
          fibers := m.fibers ++ [RunFiber.make ⟨m.nextId⟩ program flag budget context]
          nextId := m.nextId + 1 }
  /-- **Each command keeps the invariant under the command condition** `ClearReady`. -/
  command : ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)),
    MaskRuns bases m → ClearReady bases m c →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep interp m c rest).1
  /-- **The driver's own commands keep the invariant and the pending condition**: the command
  premise of `Machine.Lift`, through `Lift.Guarded`. -/
  guarded : ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (ts : List (Machine.Task ν σ β ε δ ι α)),
    Lift.StepKeeps basesOrder interp
      (Lift.Guarded (fun bases m => MaskRuns bases m) (fun _ m cmds => ClearsExited m cmds)
        (fun _ _ _ => True) ts)
  /-- **Each decision keeps the invariant**, with no admission. -/
  decision : ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (d : RunDecision ν σ β ε δ ι α), MaskRuns bases m →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (stepDecisionState interp fuel m d).1
  /-- **Each reached machine holds the invariant**, at a table that the first one is a prefix of. -/
  replay : ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St), MaskRuns bases m →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayEval interp fuel tape m).machine
  /-- **The driver issues `Cmd.finish` at an empty stack**: a finished evaluation has no frame. -/
  finished : ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) (exit : Exit β ε δ ι α),
    (evaluatePrim interp m f y).outcome = Outcome.finished exit →
      (evaluatePrim interp m f y).fiber.frame.stack = []

/-- **Each live fiber of a reached run holds the saved mask's chain at its start flag** (the
proposed registry claim `saved-mask-chain-runs`; concept `scope-lifetime-finalization`,
requirement R11). It is the lift of `saved_mask_pop_discipline` to runs. Each field cites one
theorem of this module, so its status is derived from theirs (`#plan_status`).

Reach: the fiber machine at the frame evaluator `evaluatePrim`, at every interpreter, decision
tape and fuel. It asks for no admission of a decision and no premise on a program. A fiber is
live while its `exit` is `none`. The statements over another evaluator take one premise,
`EvaluatorKeepsMask`.

It does not establish the bracket of a region, a flag or a stack of an exited fiber as a state
invariant, a cleanup's multiplicity, a delivery, a budget or liveness. It says nothing of a host
or of a printed form. The native evaluator's premise has no statement here. An invariant is not
progress.

Its consumers are the bracket's law, then the waiting wrapper under a masked caller and
Semaphore's protected permit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_mask_chain_runs (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u)
    (St : Type (max u v)) [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    MaskChainRuns ν σ β ε δ ι α χ St where
  empty := maskRuns_empty
  start := fun bases m program flag budget context kept =>
    maskRuns_make bases m kept program flag budget context
  command := fun interp => driveStep_maskRuns interp (evaluatePrim_evaluatorKeepsMask interp)
  guarded := fun interp => maskRuns_stepKeeps interp (evaluatePrim_evaluatorKeepsMask interp)
  decision := fun interp =>
    stepDecisionState_maskRuns interp (evaluatePrim_evaluatorKeepsMask interp)
  replay := fun interp => replayEval_maskRuns interp (evaluatePrim_evaluatorKeepsMask interp)
  finished := fun interp m f y _ finished =>
    (evaluatePrim_keepsMask interp m f y).finished_stack finished

end Frames

end Effect4.Machine
