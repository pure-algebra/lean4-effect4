import Test.Dogfood.Proofs.HostTimeoutNative
import Effect4.Laws.Program.Simulation.Deliver

/-!
# Ordered timeout values through actual frame pops

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: native evaluation and the command assertion.
The relation follows the actual answering frame and remaining stack.
Failure skips may discard value continuations; value pops retain the incoming class.
Scratch frames are the administrative masks that `Prim.ensure` installs.
These local transfer laws establish no reached-machine assertion or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutFrames
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutFlow HostTimeoutNative

abbrev NativeFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NativePop := FramePop EffName EffThunk Val Err Defect FiberId Ann

/-- Frame hooks keep only identity masks in their scratch stack. -/
inductive Masks : List NCode → Prop
  | nil : Masks []
  | cons (flag : Bool) {rest : List NCode} (tail : Masks rest) :
      Masks (.setInterruptible flag :: rest)

/-- Administrative masks have the same input and output value class. -/
theorem masks_stack {B : List Val} (kind : Kind) {frames : List NCode}
    (owned : Masks frames) : StackAt B kind kind frames := by
  induction owned with
  | nil => exact .nil kind
  | cons flag tail ih => exact .cons (.mask kind flag) ih

/-- Appending ordered continuations joins exactly the shared middle class. -/
theorem stack_append {B : List Val} {input middle output : Kind} {first second : List NCode}
    (left : StackAt B input middle first) (right : StackAt B middle output second) :
    StackAt B input output (first ++ second) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head (ih right)

/-- Every actual frame hook retains the administrative scratch assertion. -/
theorem ensure_masks {B : List Val} {input output : Kind} {frame : NCode}
    (owned : SavedAt B input output frame) (fiber : NativeFrame)
    (scratch : Masks fiber.stack) : Masks (frame.ensure fiber).1.stack := by
  cases owned
  all_goals simp only [Prim.ensure]
  all_goals repeat' split
  all_goals aesop (add safe constructors [Masks])

/-- A hook replacement is a failure, so it introduces no successful value. -/
theorem ensure_failure (frame : NCode) (fiber : NativeFrame) (next : NCode)
    (found : (frame.ensure fiber).2 = some next) : ∃ cause, next = .failure cause := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (add norm simp [Prim.ensure])

/-- A saved frame skipped by a value pop has identical input and output classes. -/
theorem value_pass {B : List Val} {input output : Kind} {frame : NCode}
    (owned : SavedAt B input output frame) (missing : frame.hasArm .contA = false) :
    input = output := by
  cases owned
  all_goals aesop (add norm simp [Prim.hasArm, Prim.arms, List.contains_cons, List.contains_nil])

/-- The pop answer relates its chosen frame to the remaining ordered continuation chain. -/
def PopAt (B : List Val) (demand : Effect4.Arm) (input output : Kind) (pop : NativePop) : Prop :=
  match pop.answer with
  | .empty => (demand = .contA → input = output) ∧
      (∃ middle, StackAt B middle output pop.fiber.stack) ∧ Masks pop.fiber.stack
  | .frame frame => ∃ incoming middle,
      SavedAt B incoming middle frame ∧ StackAt B middle output pop.fiber.stack ∧
        (demand = .contA → incoming = input)
  | .replacement next => ∃ middle,
      CodeAt B middle next ∧ StackAt B middle output pop.fiber.stack
  | .deferred _ => ∃ middle, StackAt B middle output pop.fiber.stack

/-- Changing a skipped cause frame's input leaves the returned continuation chain intact. -/
theorem pop_input {B : List Val} {demand : Effect4.Arm} {input next output : Kind} {pop : NativePop}
    (equal : demand = .contA → input = next) (owned : PopAt B demand next output pop) :
    PopAt B demand input output pop := by
  cases answer : pop.answer
  all_goals simp only [PopAt, answer] at owned ⊢
  case empty => exact ⟨fun h => (equal h).trans (owned.1 h), owned.2⟩
  case frame frame =>
    obtain ⟨incoming, middle, saved, rest, same⟩ := owned
    exact ⟨incoming, middle, saved, rest, fun h => (same h).trans (equal h).symm⟩
  case replacement next => exact owned
  case deferred cause => exact owned

/-- Passing a frame changes only the trace, not the typed pop answer or remaining stack. -/
theorem pass_on {B : List Val} {demand : Effect4.Arm} {input output : Kind} {pop : NativePop}
    (frame : NCode) (replacement : Option NCode) (owned : PopAt B demand input output pop) :
    PopAt B demand input output (FrameFiber.passOn frame replacement pop) := by
  exact owned

/-- Draining a scratch mask retains masks and either returns no answer or a failed replacement. -/
theorem pushed_masks (demand : Effect4.Arm) (normal : demand = .contA ∨ demand = .contE) (skip : Bool) (fiber : NativeFrame) (cause : Option CauseV)
    (owned : Masks fiber.stack) :
    Masks (FrameFiber.passPushed demand skip fiber cause).fiber.stack ∧
      ((FrameFiber.passPushed demand skip fiber cause).answer = .empty ∨
        ∃ error, (FrameFiber.passPushed demand skip fiber cause).answer = .replacement (.failure error)) := by
  generalize hs : fiber.stack = frames at owned
  cases owned with
  | nil =>
    simp only [FrameFiber.passPushed, hs]
    exact ⟨.nil, .inl trivial⟩
  | cons flag tail =>
    simp only [FrameFiber.passPushed, hs, Prim.ensure, Prim.answerOf]
    repeat' split
    all_goals rcases normal with rfl | rfl
    all_goals aesop (add norm simp [Prim.hasArm, Prim.arms, List.contains_cons, List.contains_nil])

/-- A hook's scratch drain joins either its failure or the recursively selected continuation. -/
theorem join_pushed {B : List Val} (demand : Effect4.Arm) (normal : demand = .contA ∨ demand = .contE) (skip : Bool) (fiber : NativeFrame)
    (frames : List NCode) (tail : NativePop) (cause : Option CauseV)
    (middle output : Kind) (scratch : Masks fiber.stack)
    (rest : StackAt B middle output frames) (owned : PopAt B demand middle output tail) :
    PopAt B demand middle output (FrameFiber.joinPushed demand skip fiber frames tail cause) := by
  obtain ⟨masks, empty | ⟨error, failed⟩⟩ := pushed_masks demand normal skip fiber cause scratch
  · simp only [FrameFiber.joinPushed, empty, PopAt]
    exact owned
  · simp only [FrameFiber.joinPushed, failed, PopAt]
    exact ⟨middle, .head (.failure middle error), stack_append (masks_stack middle masks) rest⟩

/-- The answer selected by the actual hook and arm test has the exact remaining value chain. -/
theorem selected_answer {B : List Val} {input middle output : Kind} {frame : NCode}
    (demand : Effect4.Arm) (fiber : NativeFrame) (frames : List NCode)
    (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (saved : SavedAt B input middle frame) (rest : StackAt B middle output frames)
    (scratch : Masks fiber.stack)
    (found : frame.answerOf demand (frame.ensure fiber).2 = some answer) :
    PopAt B demand input output
      ⟨answer, [], [], {(frame.ensure fiber).1 with stack := (frame.ensure fiber).1.stack ++ frames}, none⟩ := by
  have masks := ensure_masks saved fiber scratch
  unfold Prim.answerOf at found
  cases hook : (frame.ensure fiber).2 with
  | none =>
    rw [hook] at found
    cases arm : frame.hasArm demand with
    | false => rw [arm] at found; cases found
    | true =>
      rw [arm] at found
      cases found
      exact ⟨input, middle, saved, stack_append (masks_stack middle masks) rest, fun _ => rfl⟩
  | some replacement =>
    rw [hook] at found
    cases found
    obtain ⟨cause, rfl⟩ := ensure_failure frame fiber replacement hook
    exact ⟨middle, .head (.failure middle cause), stack_append (masks_stack middle masks) rest⟩

/-- No answer at a value pop means the saved frame has no value arm. -/
theorem answer_missing (frame : NCode) (demand : Effect4.Arm) (replacement : Option NCode)
    (missing : frame.answerOf demand replacement = none) : frame.hasArm demand = false := by
  unfold Prim.answerOf at missing
  cases replacement with
  | some _ => cases missing
  | none =>
    cases arm : frame.hasArm demand with
    | false => rfl
    | true => rw [arm] at missing; cases missing

/-- The actual fused pop retains the ordered continuation through every hook and skip. -/
theorem pop_from {B : List Val} (demand : Effect4.Arm) (normal : demand = .contA ∨ demand = .contE) (skip : Bool)
    (safe : demand = .contA → skip = false)
    {input output : Kind} {frames : List NCode} (fiber : NativeFrame) (cause : Option CauseV)
    (owned : StackAt B input output frames) (scratch : Masks fiber.stack) :
    PopAt B demand input output (FrameFiber.popFrom demand skip frames fiber cause) := by
  induction owned generalizing fiber cause with
  | nil kind => exact ⟨fun _ => rfl, ⟨kind, masks_stack kind scratch⟩, scratch⟩
  | @cons input middle output frame frames saved rest ih =>
    have ensured := ensure_masks saved fiber scratch
    have joined (nextCause : Option CauseV) :
        PopAt B demand middle output
          (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 frames
            (FrameFiber.popFrom demand skip frames
              (FrameFiber.passPushed demand skip (frame.ensure fiber).1 nextCause).fiber
              (FrameFiber.passPushed demand skip (frame.ensure fiber).1 nextCause).carriedCause)
            nextCause) := by
      exact join_pushed demand normal skip (frame.ensure fiber).1 frames _ nextCause middle output ensured rest
        (ih _ _ (pushed_masks demand normal skip (frame.ensure fiber).1 nextCause ensured).1)
    unfold FrameFiber.popFrom
    dsimp only
    split
    · rename_i answer found
      split
      · rename_i skipped
        refine pop_input (next := middle) ?_ (pass_on frame _ (joined _))
        intro demanded
        have stopped := safe demanded
        simp only [stopped, Bool.false_and, Bool.false_eq_true] at skipped
      · exact selected_answer demand fiber frames answer saved rest scratch found
    · rename_i missing
      refine pop_input (next := middle) ?_ (pass_on frame _ (joined cause))
      intro demanded
      subst demand
      exact value_pass saved (answer_missing frame .contA _ missing)

/-- The actual continuation pop retains its typed answer and saved suffix. -/
theorem get_cont {B : List Val} {input output : Kind} (fiber : NativeFrame)
    (demand : Effect4.Arm) (normal : demand = .contA ∨ demand = .contE) (skip : Bool) (cause : Option CauseV)
    (safe : demand = .contA → skip = false) (owned : StackAt B input output fiber.stack) :
    PopAt B demand input output (fiber.getCont demand skip cause) := by
  unfold FrameFiber.getCont
  split
  · exact ⟨input, owned⟩
  · exact pop_from demand normal skip safe _ cause owned .nil

/-- An empty actual pop leaves only identity masks in its stored frame. -/
theorem get_cont_empty_masks {B : List Val} {input output : Kind} (fiber : NativeFrame)
    (demand : Effect4.Arm) (normal : demand = .contA ∨ demand = .contE) (skip : Bool)
    (safe : demand = .contA → skip = false) (owned : StackAt B input output fiber.stack)
    (empty : (fiber.getCont demand skip).answer = .empty) :
    Masks (fiber.getCont demand skip).fiber.stack := by
  have assertion := get_cont fiber demand normal skip none safe owned
  unfold PopAt at assertion
  rw [show (fiber.getCont demand skip none).answer = .empty from empty] at assertion
  exact assertion.2.2

/-- Popping saved continuations keeps the code whose terminal exit is stored. -/
theorem get_cont_current (fiber : NativeFrame) (demand : Effect4.Arm) (skip : Bool) :
    (fiber.getCont demand skip).fiber.current = fiber.current := by
  unfold FrameFiber.getCont
  split
  · rfl
  · rw [Sched.popFrom_current]

/-- Restoring a finalizer's outcome never substitutes a new successful body. -/
theorem restored_exit {B : List Val} {kind : Kind} {original : ExitV}
    (good : ExitAt B kind original) (cleanup : Exit Unit Err Defect FiberId Ann) :
    ExitAt B kind (Exit.restoreAfterFinalizer original cleanup) := by
  cases original <;> cases cleanup
  all_goals aesop (add norm simp [ExitAt, Exit.restoreAfterFinalizer, Exit.mergeFinalizer])

/-- An asserted exit's actual primitive retains its successful value class. -/
theorem exit_code {B : List Val} {kind : Kind} {exit : ExitV} (good : ExitAt B kind exit) :
    CodeAt B kind (Prim.ofExit exit) := by
  cases exit with
  | success value => exact .head (.success good)
  | failure cause => exact .head (.failure kind cause)

/-- Every selected value arm returns code and pushed frames at its saved output class. -/
theorem value_arm {B : List Val} {input output : Kind} {frame : NCode}
    (view : View) (value : Val) (provided : Option ExitV)
    (saved : SavedAt B input output frame) (selected : frame.hasArm .contA = true)
    (good : ValueAt B input value) (exit : ExitAt B input (provided.getD (.success value))) :
    ∃ next pushed, frame.armA (interpreter view).toPrimInterp value provided = some (next, pushed) ∧
      CodeAt B output next ∧ StackAt B output output pushed := by
  cases saved with
  | success input output body name callback =>
    exact ⟨_, [], rfl, callback view value good, .nil output⟩
  | constant output body next callback => exact ⟨next, [], rfl, callback, .nil output⟩
  | failure kind body name callback => cases selected
  | exit kind body name flag callback =>
    exact ⟨_, [], rfl, exit_code (restored_exit exit _), .nil input⟩
  | mask kind flag => cases selected
  | cancel kind name callback => cases selected
  | loop name cursor cursorGood callback =>
    have answer := callback view cursor value cursorGood good
    cases operation : (interpreter view).loopResume name cursor value with
    | «continue» next body =>
      rw [operation] at answer
      cases answer with
      | enter cursor body cursorGood bodyGood =>
        exact ⟨body, [.whileLoop name next], by simp only [Prim.armA, operation], bodyGood,
          .cons (.loop name next cursorGood callback) (.nil .result)⟩
    | finish code =>
      rw [operation] at answer
      cases answer with
      | finish code codeGood =>
        exact ⟨code, [], by simp only [Prim.armA, operation], codeGood, .nil .result⟩

/-- A selected cause arm either handles the failure or restores its saved failed exit. -/
theorem cause_arm {B : List Val} {input output : Kind} {frame : NCode}
    (view : View) (cause : CauseV) (provided : Option ExitV)
    (saved : SavedAt B input output frame) (selected : frame.hasArm .contE = true)
    (exit : ExitAt B input (provided.getD (.failure cause))) :
    ∃ next pushed, frame.armE (interpreter view).toPrimInterp cause provided = some (next, pushed) ∧
      CodeAt B output next ∧ StackAt B output output pushed := by
  cases saved with
  | success input output body name callback => cases selected
  | constant output body next callback => cases selected
  | failure kind body name callback =>
    exact ⟨_, [], rfl, callback view cause, .nil input⟩
  | exit kind body name flag callback =>
    exact ⟨_, [], rfl, exit_code (restored_exit exit _), .nil input⟩
  | mask kind flag => cases selected
  | loop name cursor cursorGood callback => cases selected
  | cancel kind name callback =>
    cases interrupted : cause.hasInterrupts with
    | false => exact ⟨_, [], by simp only [Prim.armE, interrupted, Bool.false_eq_true, ite_false],
        .head (.failure input cause), .nil input⟩
    | true => exact ⟨_, [], by simp only [Prim.armE, interrupted, ite_true],
        callback view cause, .nil input⟩

/-- A running frame's code and saved chain finish in the stated value class. -/
def FrameKind (B : List Val) (output : Kind) (frame : NativeFrame) : Prop :=
  ∃ input, CodeAt B input frame.current ∧ StackAt B input output frame.stack

def StepKind (B : List Val) (output : Kind) : FrameStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .running frame => FrameKind B output frame
  | .finished exit => ExitAt B output exit

/-- The value resume consumes the actual selected frame and exact remaining ordered stack. -/
theorem resume_value {B : List Val} {input output : Kind} (view : View) (fiber : NativeFrame)
    (value : Val) (provided : Option ExitV) (good : ValueAt B input value)
    (exit : ExitAt B input (provided.getD (.success value)))
    (stack : StackAt B input output fiber.stack) :
    StepKind B output (fiber.resumeValue (interpreter view).toPrimInterp value provided).1 := by
  have owned := get_cont fiber .contA (.inl rfl) false none (fun _ => rfl) stack
  unfold PopAt at owned
  unfold FrameFiber.resumeValue
  cases found : (fiber.getCont .contA false).answer with
  | empty =>
    rw [found] at owned
    have same := owned.1 rfl
    exact same ▸ exit
  | deferred cause =>
    rw [found] at owned
    obtain ⟨middle, rest⟩ := owned
    exact ⟨middle, .head (.failure middle cause), rest⟩
  | replacement next =>
    rw [found] at owned
    exact owned
  | frame chosen =>
    rw [found] at owned
    obtain ⟨incoming, middle, saved, rest, same⟩ := owned
    have equal := same rfl
    subst incoming
    obtain ⟨next, pushed, arm, codeGood, pushedGood⟩ := value_arm view value provided saved
      (FrameFiber.getCont_answer_hasArm fiber .contA false chosen found) good exit
    dsimp only
    rw [arm]
    exact ⟨middle, codeGood, stack_append pushedGood rest⟩

/-- Failure delivery keeps failures at every value class, including preempted catches. -/
theorem delivered_failure {B : List Val} (kind : Kind) (pop : NativePop) (cause : CauseV) :
    ExitAt B kind (pop.deliveredExit (.failure cause)) := by trivial

/-- A cause resume may skip value frames but retains its actual chosen output chain. -/
theorem resume_cause {B : List Val} {input output : Kind} (view : View) (fiber : NativeFrame)
    (cause : CauseV) (provided : Option CauseV) (stack : StackAt B input output fiber.stack) :
    StepKind B output (fiber.resumeCause (interpreter view).toPrimInterp cause
      (provided.map Exit.failure)).1 := by
  have owned := get_cont fiber .contE (.inr rfl) true (some cause) (fun h => by cases h) stack
  unfold PopAt at owned
  unfold FrameFiber.resumeCause
  dsimp only
  cases found : (fiber.getCont .contE true (some cause)).answer with
  | empty =>
    cases provided with
    | none => trivial
    | some original => trivial
  | deferred interrupted =>
    rw [found] at owned
    obtain ⟨middle, rest⟩ := owned
    exact ⟨middle, .head (.failure middle interrupted), rest⟩
  | replacement next =>
    rw [found] at owned
    exact owned
  | frame chosen =>
    rw [found] at owned
    obtain ⟨incoming, middle, saved, rest, _⟩ := owned
    have selected : chosen.hasArm .contE = true := by
      apply FrameFiber.getCont_answer_hasArm fiber .contE true chosen
      rw [← FrameFiber.getCont_answer_cause fiber .contE true (some cause)]
      exact found
    have exit : ExitAt B incoming
        (((provided.map Exit.failure).map (fiber.getCont .contE true (some cause)).deliveredExit).getD
          (.failure ((fiber.getCont .contE true (some cause)).carriedCause.getD cause))) := by
      cases provided <;> trivial
    obtain ⟨next, pushed, arm, codeGood, pushedGood⟩ := cause_arm view
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) _ saved selected exit
    dsimp only
    rw [arm]
    exact ⟨middle, codeGood, stack_append pushedGood rest⟩

/-- A terminal value step has consumed every value continuation. -/
theorem value_finished_empty {B : List Val} {input output : Kind} (view : View)
    (fiber : NativeFrame) (value : Val) (provided : Option ExitV) (answer : ExitV)
    (good : ValueAt B input value) (exit : ExitAt B input (provided.getD (.success value)))
    (stack : StackAt B input output fiber.stack)
    (finished : (fiber.resumeValue (interpreter view).toPrimInterp value provided).1 = .finished answer) :
    (fiber.getCont .contA false).answer = .empty := by
  unfold FrameFiber.resumeValue at finished
  cases found : (fiber.getCont .contA false).answer with
  | empty => rfl
  | deferred cause => rw [found] at finished; cases finished
  | replacement next => rw [found] at finished; cases finished
  | frame chosen =>
    have owned := get_cont fiber .contA (.inl rfl) false none (fun _ => rfl) stack
    unfold PopAt at owned
    rw [found] at owned finished
    obtain ⟨incoming, middle, saved, rest, same⟩ := owned
    have equal := same rfl
    subst incoming
    obtain ⟨next, pushed, arm, _, _⟩ := value_arm view value provided saved
      (FrameFiber.getCont_answer_hasArm fiber .contA false chosen found) good exit
    dsimp only at finished
    rw [arm] at finished
    cases finished

/-- A terminal failure step has consumed every cause continuation. -/
theorem cause_finished_empty {B : List Val} {input output : Kind} (view : View)
    (fiber : NativeFrame) (cause : CauseV) (answer : ExitV)
    (stack : StackAt B input output fiber.stack)
    (finished : (fiber.resumeCause (interpreter view).toPrimInterp cause
      (some (.failure cause))).1 = .finished answer) :
    (fiber.getCont .contE true (some cause)).answer = .empty := by
  unfold FrameFiber.resumeCause at finished
  dsimp only at finished
  cases found : (fiber.getCont .contE true (some cause)).answer with
  | empty => rfl
  | deferred cause => rw [found] at finished; cases finished
  | replacement next => rw [found] at finished; cases finished
  | frame chosen =>
    have owned := get_cont fiber .contE (.inr rfl) true (some cause) (fun h => by cases h) stack
    unfold PopAt at owned
    rw [found] at owned finished
    obtain ⟨incoming, middle, saved, rest, _⟩ := owned
    have selected : chosen.hasArm .contE = true := by
      apply FrameFiber.getCont_answer_hasArm fiber .contE true chosen
      rw [← FrameFiber.getCont_answer_cause fiber .contE true (some cause)]
      exact found
    obtain ⟨next, pushed, arm, _, _⟩ := cause_arm view
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
      (some ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause))) saved selected
      (delivered_failure incoming (fiber.getCont .contE true (some cause)) cause)
    dsimp only at finished
    simp only [Option.map_some] at finished
    rw [arm] at finished
    cases finished

/-- A code assertion exposes its actual primitive head through the complete source proof. -/
theorem code_head {B : List Val} {kind : Kind} {code : NCode} (good : CodeAt B kind code) :
    HeadAt B kind code := by
  cases good with
  | source point slots => exact source_head point slots
  | head good => exact good

/-- The actual frame step consumes only primitives the native dispatcher delegates to it. -/
theorem step_head {B : List Val} {input output : Kind} (view : View) (fiber : NativeFrame)
    (head : HeadAt B input fiber.current) (stack : StackAt B input output fiber.stack)
    (regular : (interpreter view).parkOf fiber.current = none)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (interpreter view).withFiberOf thunk = none) :
    StepKind B output (fiber.step (interpreter view).toPrimInterp).1 := by
  generalize current : fiber.current = code at head
  cases head with
  | success good =>
    simp only [FrameFiber.step, current]
    exact resume_value view fiber _ (some (.success _)) good good stack
  | failure kind cause =>
    simp only [FrameFiber.step, current]
    exact resume_cause view fiber cause (some cause) stack
  | sync kind thunk answer fallback operation =>
    simp only [FrameFiber.step, current]
    exact resume_value view fiber _ none (fallback view) (fallback view) stack
  | suspend kind point body =>
    simp only [FrameFiber.step, current]
    exact ⟨_, body view, stack⟩
  | action kind thunk operation action good =>
    have absent := ordinary thunk current
    rw [action view] at absent
    cases absent
  | onSuccess incoming middle body name first next =>
    simp only [FrameFiber.step, current]
    exact ⟨incoming, first, .cons (.success incoming _ body name next) stack⟩
  | constant middle body next first saved =>
    simp only [FrameFiber.step, current]
    exact ⟨.unit, first, .cons (.constant _ body next saved) stack⟩
  | onFailure kind body name first caught =>
    simp only [FrameFiber.step, current]
    exact ⟨_, first, .cons (.failure _ body name caught) stack⟩
  | onExit kind body name flag first cleanup =>
    simp only [FrameFiber.step, current]
    exact ⟨_, first, .cons (.exit _ body name flag cleanup) stack⟩
  | loop name cursor cursorGood enter resume =>
    simp only [FrameFiber.step, current]
    have entered := enter view cursor cursorGood
    cases operation : (interpreter view).loopEnter name cursor with
    | «continue» next body =>
      rw [operation] at entered
      cases entered with
      | enter cursor body cursorGood bodyGood =>
        exact ⟨.result, bodyGood, .cons (.loop name next cursorGood resume) stack⟩
    | finish code =>
      rw [operation] at entered
      cases entered with
      | finish code codeGood => exact ⟨.result, codeGood, stack⟩
  | yieldNow priority =>
    simp only [FrameFiber.step, current]
    exact ⟨.unit, by rw [current]; exact .head (.yieldNow priority), stack⟩
  | external op request path =>
    simp only [FrameFiber.step, current]
    exact ⟨.body, by rw [current]; exact .head (.external op request path), stack⟩
  | sleep millis =>
    simp only [FrameFiber.step, current]
    exact ⟨.unit, by rw [current]; exact .head (.sleep millis), stack⟩
  | racePark race => rw [current] at regular; cases regular
  | awaitPark targets => rw [current] at regular; cases regular

/-- A completed primitive keeps a well-classified stored frame after its actual exit pop. -/
theorem finished_head {B : List Val} {input output : Kind} (view : View) (fiber : NativeFrame)
    (head : HeadAt B input fiber.current) (stack : StackAt B input output fiber.stack)
    (regular : (interpreter view).parkOf fiber.current = none)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (interpreter view).withFiberOf thunk = none) (exit : ExitV)
    (finished : (fiber.step (interpreter view).toPrimInterp).1 = .finished exit) :
    CodeAt B output (frameExitState fiber).current ∧ Masks (frameExitState fiber).stack := by
  generalize current : fiber.current = code at head
  cases head with
  | success good =>
    have empty := value_finished_empty view fiber _ (some (.success _)) exit good good stack
      (by simpa only [FrameFiber.step, current] using finished)
    have assertion := get_cont fiber .contA (.inl rfl) false none (fun _ => rfl) stack
    unfold PopAt at assertion
    rw [empty] at assertion
    have same := assertion.1 rfl
    rw [frameExitState, current]
    refine ⟨?_, assertion.2.2⟩
    rw [get_cont_current, current]
    exact .head (.success (same ▸ good))
  | failure kind cause =>
    have empty := cause_finished_empty view fiber cause exit stack
      (by simpa only [FrameFiber.step, current] using finished)
    have plain : (fiber.getCont .contE true).answer = .empty := by
      rw [← FrameFiber.getCont_answer_cause fiber .contE true (some cause)]
      exact empty
    rw [frameExitState, current]
    refine ⟨?_, get_cont_empty_masks fiber .contE (.inr rfl) true (fun h => by cases h) stack plain⟩
    rw [get_cont_current, current]
    exact .head (.failure output cause)
  | sync kind thunk answer fallback operation =>
    have empty := value_finished_empty view fiber _ none exit (fallback view) (fallback view) stack
      (by simpa only [FrameFiber.step, current] using finished)
    have assertion := get_cont fiber .contA (.inl rfl) false none (fun _ => rfl) stack
    unfold PopAt at assertion
    rw [empty] at assertion
    have same := assertion.1 rfl
    rw [frameExitState, current]
    refine ⟨?_, assertion.2.2⟩
    rw [get_cont_current, current]
    exact same ▸ CodeAt.head (.sync input thunk answer fallback operation)
  | action kind thunk operation action good =>
    have absent := ordinary thunk current
    rw [action view] at absent
    cases absent
  | loop name cursor cursorGood enter resume =>
    simp only [FrameFiber.step, current] at finished
    split at finished <;> cases finished
  | racePark race => rw [current] at regular; cases regular
  | awaitPark targets => rw [current] at regular; cases regular
  | suspend kind point body =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | onSuccess incoming middle body name first next =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | constant middle body next first saved =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | onFailure kind body name first caught =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | onExit kind body name flag first cleanup =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | yieldNow priority =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | external op request path =>
    simp only [FrameFiber.step, current] at finished
    cases finished
  | sleep millis =>
    simp only [FrameFiber.step, current] at finished
    cases finished

/-- Installing a finished frame retains the same ordered body assertion as a running frame. -/
theorem finished_frame {B : List Val} {output : Kind} (view : View) (fiber : NativeFrame)
    (owned : FrameKind B output fiber) (regular : (interpreter view).parkOf fiber.current = none)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (interpreter view).withFiberOf thunk = none) (exit : ExitV)
    (finished : (fiber.step (interpreter view).toPrimInterp).1 = .finished exit) :
    CodeAt B output (frameExitState fiber).current ∧ Masks (frameExitState fiber).stack := by
  obtain ⟨input, code, stack⟩ := owned
  exact finished_head view fiber (code_head code) stack regular ordinary exit finished

/-- Native frame delegation retains its expected successful result, including every saved callback. -/
theorem step_frame {B : List Val} {output : Kind} (view : View) (fiber : NativeFrame)
    (owned : FrameKind B output fiber) (regular : (interpreter view).parkOf fiber.current = none)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (interpreter view).withFiberOf thunk = none) :
    StepKind B output (fiber.step (interpreter view).toPrimInterp).1 := by
  obtain ⟨input, code, stack⟩ := owned
  exact step_head view fiber (code_head code) stack regular ordinary

end Test.Dogfood.Proofs.HostTimeoutFrames
