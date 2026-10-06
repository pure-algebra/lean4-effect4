import Effect4.Laws.Machine.MaskRuns
import ProofGraph.Plan

/-!
# Test.Machine.MaskRuns — the saved mask's chain from one pop to a run: finite controls

`src/Effect4/Laws/Machine/MaskRuns.lean` carries the chain `FrameFiber.MaskChain` from the frame
machine's pop along a run. This battery evaluates its statements on real fibers, at the
alphabets `Nat`.

## Part A: the frames

- One sweep: every stack of at most three frames over eight frames, both flags, both bases, a
  pending cause or none, a deferred interrupt or none, and twenty primitives as `current`. Each
  state that holds the chain keeps it through `FrameFiber.step`. Each finished step and each
  pop that answers nothing ends at an empty stack and at the base.
- Four red controls, each red at its own property: a step that pushes a restoring frame and
  keeps the flag; the unanswered pop without the scratch premise; the flag's statement without
  the chain; the finished frame's statement without a finished step.

Placement. Each guard is a finite instance of a step of R11's open part "the lift of
saved-mask-pop-discipline to runs" (concept `scope-lifetime-finalization`). A fiber outside the
sweep is not checked here: the theorems are the general statements. Part A states no law of a
run.
-/

set_option autoImplicit false

namespace Test.Machine.MaskRuns

open Effect4 Effect4.FrameFiber Effect4.Machine

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

private def cause : C := ⟨[.interrupt (some 53) .empty]⟩

private def value : P := .onSuccess (.success 2) 3
private def handler : P := .onFailure (.success 4) 5

/-- A frame interpreter with both kinds of value arm that push: loop 1 goes on at its next
cursor, and generator 2 yields under itself. Loop 0 and the generators 0 and 1 stop. -/
private def frames : PrimInterp Nat Nat Nat Nat Nat Nat Nat where
  contA := fun name value => if name = 3 then .success (value + 1) else .sync name
  contE := fun _ cause => .failure cause
  syncValue := fun thunk => thunk
  suspendBody := fun thunk => .success thunk
  finalizerExit := fun _ _ => .success ()
  reifyExit := fun _ => 0
  iterNext := fun generator value =>
    ([], if generator = 0 then .done value else if generator = 1 then .halt cause
      else .resume (.success value) (generator - 1))
  loopEnter := fun loop cursor =>
    if loop = 0 then .finish (.success cursor) else .continue (cursor + 1) (.success cursor)
  loopResume := fun loop cursor value =>
    if loop = 0 then .finish (.success value) else .continue (cursor + 1) (.success value)
  notImplemented := 0
  cancelThenFail := fun _ cause => .failure cause

/-- The chain over a fiber's flag and its stack, decided by the law module's instance. -/
private def holds (base : Bool) (f : F) : Bool := decide (MaskChain base f.interruptible f.stack)

private def bools : List Bool := [true, false]

/-! ## The sweep -/

private def alphabet : List P :=
  [.setInterruptible true, .setInterruptible false, .onExit (.success 1) 9 false,
    .asyncFinalizer 7, value, handler, .whileLoop 1 0, .iterator 2 0]

/-- One primitive of each constructor as `current`, and a second one where an interpreter's
answer splits the step. -/
private def currents : List P :=
  [.success 0, .failure cause, .sync 1, .suspend 1, .withFiber 1, .yieldableError 1,
    .iterator 0 0, .iterator 2 0, value, .onSuccessConst (.success 1) (.success 2), handler,
    .onSuccessAndFailure (.success 1) 3 5, .exitFrame (.success 1), .onExit (.success 1) 9 false,
    .setInterruptible true, .whileLoop 0 0, .whileLoop 1 0, .yieldNowWith 0, .async 1 false none,
    .asyncFinalizer 7]

private def stacksUpTo : Nat → List (List P)
  | 0 => [[]]
  | n + 1 => [] :: (stacksUpTo n).flatMap fun stack => alphabet.map (· :: stack)

/-- The states of the sweep that hold the chain, each with its base. -/
private def states (depth : Nat) : List (Bool × F) :=
  (stacksUpTo depth).flatMap fun stack => bools.flatMap fun flag => bools.flatMap fun base =>
    [none, some cause].flatMap fun pendingCause => bools.flatMap fun deferred =>
      currents.filterMap fun current =>
        let f : F := ⟨current, stack, flag, pendingCause, deferred⟩
        if holds base f then some (base, f) else none

/-- A step that goes on keeps the chain, and a finished step retains an empty stack at the
base. -/
private def stepKeeps (base : Bool) (f : F) : Bool :=
  match (f.step frames).fst with
  | .running next => holds base next
  | .finished _ => (frameExitState f).stack.isEmpty && (frameExitState f).interruptible == base

private def finishes (f : F) : Bool :=
  match (f.step frames).fst with
  | .running _ => false
  | .finished _ => true

/-- A pop that answers nothing ends at an empty stack and at the base. -/
private def unansweredKeeps (base : Bool) (pop : FramePop Nat Nat Nat Nat Nat Nat Nat) : Bool :=
  pop.answer != .empty || (pop.fiber.stack.isEmpty && pop.fiber.interruptible == base)

#guard (stacksUpTo 3).length == 585
#guard (states 3).length == 64000

-- `FrameFiber.step` keeps the chain where it goes on, and it finishes at the base.
#guard (states 3).all fun (base, f) => stepKeeps base f
-- Both outcomes are in the sweep.
#guard ((states 3).countP fun (_, f) => finishes f) == 1040

-- Each pop that answers nothing ends at an empty stack and at the base: each demand, each skip
-- flag, a carried cause or none.
#guard (states 3).all fun (base, f) => Arm.all.all fun d => bools.all fun s =>
  unansweredKeeps base (f.getCont d s) && unansweredKeeps base (f.getCont d s (some cause))
-- The same for the pop itself, from an empty scratch stack.
#guard (states 3).all fun (base, f) => Arm.all.all fun d => bools.all fun s =>
  unansweredKeeps base (popFrom d s f.stack { f with stack := [] })
-- The sweep holds pops that answer nothing: the two checks above are not empty.
#guard ((states 3).foldl (fun n (_, f) => n + Arm.all.foldl (fun k d =>
  k + bools.countP fun s => (f.getCont d s).answer == .empty) 0) 0) == 61760

/-! ## The red controls -/

/-! ### 1. A step that pushes a restoring frame and keeps the flag -/

/-- A wrong entry of a region: it pushes the frame that returns the flag, and it keeps the
flag. A real entry pushes that frame only where it changes the flag. -/
private def pushNoMask (f : F) : F := { f with stack := .setInterruptible f.interruptible :: f.stack }

-- It breaks the chain at every state of the sweep. The real entries keep it.
#guard (states 3).all fun (base, f) => !holds base (pushNoMask f)
#guard (states 3).all fun (base, f) => holds base f.uninterruptible

/-! ### 2. The unanswered pop without the scratch premise -/

/-- With no frame to pop, the pop answers nothing and its stack is the scratch stack. So the
statement needs the empty scratch stack. -/
theorem unanswered_needs_empty_scratch :
    ¬ ∀ (demand : Arm) (skip : Bool) (frames : List P) (f : F),
      (popFrom demand skip frames f).answer = ContAnswer.empty →
        (popFrom demand skip frames f).fiber.stack = [] := by
  intro h
  exact absurd (h .contA false [] ⟨.success 0, [value], true, none, false⟩ rfl) (by decide)

/-! ### 3. The flag's statement without the chain -/

/-- An empty stack answers nothing at either flag. So the flag is the base only under the
chain. -/
theorem unanswered_flag_needs_chain :
    ¬ ∀ (base : Bool) (f : F) (demand : Arm) (skip : Bool) (carried : Option C),
      (f.getCont demand skip carried).answer = ContAnswer.empty →
        (f.getCont demand skip carried).fiber.interruptible = base := by
  intro h
  exact absurd (h true ⟨.success 0, [], false, none, false⟩ .contA false none rfl) (by decide)

/-- One flag and one stack give one base: with two flags, two empty stacks have each its own
base. -/
theorem base_needs_flag :
    ¬ ∀ (base base' flag flag' : Bool) (stack : List P),
      MaskChain base flag stack → MaskChain base' flag' stack → base = base' :=
  fun h => Bool.noConfusion (h true false true false [] rfl rfl)

/-! ### 4. The finished frame's statement without a finished step -/

/-- A step that goes on: the value frame answers, and the cause frame under it stays. -/
private def answered : F := ⟨.success 0, [value, handler], true, none, false⟩

-- `frameExitState` alone gives no empty stack: the premise of a finished step is needed.
#guard !finishes answered
#guard (frameExitState answered).stack == [handler]
#guard holds true (frameExitState answered)

/-! ## The statements, pinned

The brief's two statements of part A as they stand, by their types at the alphabets `Nat`. -/

example : ∀ (base : Bool) (interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat) (f : F),
    MaskChain base f.interruptible f.stack → ∀ (next : F),
      (f.step interp).fst = FrameStep.running next → MaskChain base next.interruptible next.stack :=
  step_maskChain

example : ∀ (demand : Arm) (skip : Bool) (frames : List P) (f : F), f.stack = [] →
    (popFrom demand skip frames f).answer = ContAnswer.empty →
      (popFrom demand skip frames f).fiber.stack = [] :=
  popFrom_unanswered_stack

example : ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List P) (f : F), f.stack = [] →
    MaskChain base f.interruptible frames →
      (popFrom demand skip frames f).answer = ContAnswer.empty →
        (popFrom demand skip frames f).fiber.interruptible = base :=
  popFrom_unanswered_flag

example : ∀ (base : Bool) (interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat) (f : F),
    MaskChain base f.interruptible f.stack → ∀ (exit : Exit Nat Nat Nat Nat Nat),
      (f.step interp).fst = FrameStep.finished exit →
        (frameExitState f).stack = [] ∧ (frameExitState f).interruptible = base :=
  fun base interp f valid exit finished =>
    ⟨step_finished_stack interp f exit finished, step_finished_flag base interp f valid exit finished⟩

/-- A statement in use: a step of a fiber of the sweep keeps the chain. -/
example : ∀ next : F, (answered.step frames).fst = FrameStep.running next →
    MaskChain true next.interruptible next.stack :=
  step_maskChain true frames answered (by decide)

/-! ## The pinned outputs -/

/-- info: 'Effect4.FrameFiber.step_maskChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_maskChain

/-- info: 'Effect4.FrameFiber.popFrom_unanswered_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms popFrom_unanswered_stack

/-- info: 'Effect4.FrameFiber.popFrom_unanswered_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms popFrom_unanswered_flag

/-- info: 'Effect4.Machine.step_finished_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_finished_stack

/-- info: 'Effect4.Machine.step_finished_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_finished_flag

end Test.Machine.MaskRuns
