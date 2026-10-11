import Effect4.Laws.Program.NativeInterpScope

/-!
# Source scope through the actual frame machine

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The predicates inspect existing primitive frames and their existing saved names.
The pop proof retains the actual answering frame and every remaining stack slot.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- Every saved primitive frame retains its source-bearing slots. -/
def StackAt (root : NativeEff) (frames : List NCode) : Prop := ∀ code ∈ frames, CodeAt root code

/-- A frame-machine fiber retains its current primitive and saved frames. -/
def FrameAt (root : NativeEff) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  CodeAt root fiber.current ∧ StackAt root fiber.stack

/-- The pop answer retains its actual answering primitive. -/
def AnswerAt (root : NativeEff) : ContAnswer EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .frame code | .replacement code => CodeAt root code
  | _ => True

/-- A frame hook pushes only administrative masks, retaining prior source slots. -/
theorem ensure_stack_at (root : NativeEff) (frame : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : StackAt root fiber.stack) : StackAt root (frame.ensure fiber).1.stack := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (add norm simp [StackAt, List.mem_cons, CodeAt])

/-- A frame hook's replacement is an exit and carries no source writer. -/
theorem ensure_replacement_at (root : NativeEff) (frame : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    ∀ code ∈ (frame.ensure fiber).2, CodeAt root code := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (add norm simp [Option.mem_def, CodeAt])

/-- Choosing the pop answer retains the frame or hook replacement it reads. -/
theorem answerOf_at (root : NativeEff) (frame : NCode) (demand : Effect4.Arm)
    (replacement : Option NCode) (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (owned : CodeAt root frame) (hook : ∀ code ∈ replacement, CodeAt root code)
    (found : Prim.answerOf frame demand replacement = some answer) : AnswerAt root answer := by
  unfold Prim.answerOf at found
  repeat' split at found
  all_goals aesop (add norm simp [AnswerAt, Option.mem_def])

/-- The non-recursive hook pop retains the answering source and remaining frames. -/
theorem passPushed_at (root : NativeEff) (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV)
    (owned : StackAt root fiber.stack) :
    StackAt root (FrameFiber.passPushed demand skip fiber cause).fiber.stack ∧
      AnswerAt root (FrameFiber.passPushed demand skip fiber cause).answer := by
  unfold FrameFiber.passPushed
  cases h : fiber.stack with
  | nil => exact ⟨owned, trivial⟩
  | cons frame rest =>
    simp only []
    have head : CodeAt root frame := owned frame (by rw [h]; exact .head _)
    have tail : StackAt root rest := fun code member => owned code (by rw [h]; exact .tail _ member)
    have stack := ensure_stack_at root frame {fiber with stack := rest} tail
    have hook := ensure_replacement_at root frame {fiber with stack := rest}
    refine ⟨stack, ?_⟩
    split
    · split
      · trivial
      · exact answerOf_at root frame demand _ _ head hook (by assumption)
    · trivial

/-- Appending the saved suffix retains every primitive frame. -/
theorem stack_append_at (root : NativeEff) (first second : List NCode)
    (a : StackAt root first) (b : StackAt root second) : StackAt root (first ++ second) := by
  intro code member
  rcases List.mem_append.mp member with left | right
  · exact a code left
  · exact b code right

/-- The fused pop retains source slots through its hook drain and tail recursion. -/
theorem popFrom_at (root : NativeEff) (demand : Effect4.Arm) (skip : Bool) (frames : List NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV)
    (owned : StackAt root frames) (scratch : StackAt root fiber.stack) :
    StackAt root (FrameFiber.popFrom demand skip frames fiber cause).fiber.stack ∧
      AnswerAt root (FrameFiber.popFrom demand skip frames fiber cause).answer := by
  induction frames generalizing fiber cause with
  | nil => exact ⟨scratch, trivial⟩
  | cons frame rest ih =>
    have head : CodeAt root frame := owned frame (.head _)
    have tail : StackAt root rest := fun code member => owned code (.tail _ member)
    have ensured := ensure_stack_at root frame fiber scratch
    have hook := ensure_replacement_at root frame fiber
    have pushed := passPushed_at root demand skip (frame.ensure fiber).1 none ensured
    have recursive := ih (FrameFiber.passPushed demand skip (frame.ensure fiber).1 none).fiber
      none tail pushed.1
    have answering (answer : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
        (h : Prim.answerOf frame demand (frame.ensure fiber).2 = some answer) : AnswerAt root answer :=
      answerOf_at root frame demand _ answer head hook h
    unfold FrameFiber.popFrom
    dsimp only
    repeat' split
    all_goals aesop (add norm simp [FrameFiber.passOn, FrameFiber.joinPushed, FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause, FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]) (add safe apply [answering, stack_append_at])

/-- The actual continuation pop retains its answer and every remaining saved frame. -/
theorem getCont_at (root : NativeEff)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV)
    (owned : StackAt root fiber.stack) :
    StackAt root (fiber.getCont demand skip cause).fiber.stack ∧
      AnswerAt root (fiber.getCont demand skip cause).answer := by
  unfold FrameFiber.getCont
  split
  · exact ⟨owned, trivial⟩
  · exact popFrom_at root demand skip fiber.stack _ cause owned (by intro code member; cases member)

/-- An exit contains no source-bearing residual slot. -/
theorem ofExit_at (root : NativeEff) (exit : ExitV) : CodeAt root (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Invoking a source-owned value frame retains its next primitive and pushed frames. -/
theorem armA_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root frame)
    (found : frame.armA (interpAt root completed table).toPrimInterp value provided = some (next, pushed)) :
    CodeAt root next ∧ StackAt root pushed := by
  fun_cases Prim.armA (interpAt root completed table).toPrimInterp frame value provided
  all_goals aesop (add norm simp [CodeAt, StackAt, Prim.armA, LoopAt, IterAt]) (add safe apply [ofExit_at, (interp_contA_at root fragment)]) (add safe forward [(interp_loopResume_at root fragment), interp_iter_at])

/-- Invoking a source-owned cause frame retains its next primitive and pushed frames. -/
theorem armE_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root frame)
    (found : frame.armE (interpAt root completed table).toPrimInterp cause provided = some (next, pushed)) :
    CodeAt root next ∧ StackAt root pushed := by
  fun_cases Prim.armE (interpAt root completed table).toPrimInterp frame cause provided
  all_goals aesop (add norm simp [CodeAt, StackAt, Prim.armE]) (add safe apply [ofExit_at, (interp_contE_at root fragment), interp_cancel_at])

/-- A frame step retains every source slot of its running fiber. -/
def FrameStepAt (root : NativeEff) : FrameStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .running fiber => FrameAt root fiber
  | .finished _ => True

/-- Resuming a value uses the actual owned pop answer and source value arm. -/
theorem resumeValue_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    FrameStepAt root ((fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1) := by
  have popped := getCont_at root fiber .contA false none owned.2
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  all_goals aesop (add norm simp [FrameStepAt, FrameAt, AnswerAt, CodeAt, FrameFiber.getCont_fiber_cause, FrameFiber.getCont_answer_cause]) (add safe apply [stack_append_at]) (add safe forward [(armA_at root fragment completed table)])

/-- Resuming a cause uses the actual owned pop answer and source cause arm. -/
theorem resumeCause_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    FrameStepAt root ((fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1) := by
  have remaining := (getCont_at root fiber .contE true none owned.2).1
  have answering (frame : NCode) (found : (fiber.getCont .contE true).answer = .frame frame) : CodeAt root frame := by
    have answer := (getCont_at root fiber .contE true none owned.2).2
    rw [found] at answer
    exact answer
  have replacing (next : NCode) (found : (fiber.getCont .contE true).answer = .replacement next) : CodeAt root next := by
    have answer := (getCont_at root fiber .contE true none owned.2).2
    rw [found] at answer
    exact answer
  unfold FrameFiber.resumeCause
  dsimp only
  repeat' split
  all_goals aesop (add norm simp [FrameStepAt, FrameAt, AnswerAt, CodeAt, FrameFiber.getCont_fiber_cause, FrameFiber.getCont_answer_cause]) (add safe apply [stack_append_at]) (add safe forward [answering, replacing, (armE_at root fragment completed table)])

/-- One actual frame step retains the source addresses of its running residual. -/
theorem frame_step_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    FrameStepAt root ((fiber.step (interpAt root completed table).toPrimInterp).1) := by
  have current := owned.1
  have stack := owned.2
  unfold FrameFiber.step
  cases h : fiber.current
  all_goals rw [h] at current
  all_goals dsimp only
  case success value => exact resumeValue_at root fragment completed table fiber value _ owned
  case failure cause => exact resumeCause_at root fragment completed table fiber cause _ owned
  case sync thunk => exact resumeValue_at root fragment completed table fiber _ none owned
  case iterator name cursor =>
    cases ha : Prim.armA (interpAt root completed table).toPrimInterp (.iterator name cursor) cursor none with
    | none => exact owned
    | some result =>
      rcases result with ⟨next, pushed⟩
      have slots := armA_at root fragment completed table (.iterator name cursor) cursor none next pushed current ha
      exact ⟨slots.1, stack_append_at root _ _ slots.2 stack⟩
  case whileLoop name cursor =>
    have slots := interp_loopEnter_at root fragment completed table name cursor current
    cases hl : (interpAt root completed table).loopEnter name cursor with
    | «continue» next body =>
      rw [hl] at slots
      exact ⟨slots, fun code member => by
        rcases List.mem_cons.mp member with eq | tail
        · rw [eq]; exact current
        · exact stack code tail⟩
    | finish body =>
      rw [hl] at slots
      exact ⟨slots, stack⟩
  all_goals aesop (add norm simp [FrameStepAt, FrameAt, CodeAt, StackAt, List.mem_cons]) (add safe apply [(resumeValue_at root fragment), (resumeCause_at root fragment), (interp_suspend_at root fragment)])

/-- Frame hooks retain the current primitive while pushing administrative masks. -/
theorem ensure_current (frame : NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    (frame.ensure fiber).1.current = fiber.current := by
  fun_cases Prim.ensure frame fiber
  all_goals rfl

/-- The single pushed hook retains the current primitive. -/
theorem pushed_current (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    (FrameFiber.passPushed demand skip fiber cause).fiber.current = fiber.current := by
  unfold FrameFiber.passPushed
  cases h : fiber.stack with
  | nil => rfl
  | cons frame rest => exact ensure_current frame _

/-- The fused pop retains the current primitive throughout hook and tail processing. -/
theorem pop_current (demand : Effect4.Arm) (skip : Bool) (frames : List NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    (FrameFiber.popFrom demand skip frames fiber cause).fiber.current = fiber.current := by
  induction frames generalizing fiber cause with
  | nil => rfl
  | cons frame rest ih =>
    unfold FrameFiber.popFrom
    dsimp only
    repeat' split
    all_goals simp only [FrameFiber.passOn, FrameFiber.joinPushed]
    all_goals repeat' split
    all_goals simp only [ih, pushed_current, ensure_current]

/-- The actual pop retains both the current primitive and saved source scopes. -/
theorem getCont_frame_at (root : NativeEff)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) (owned : FrameAt root fiber) :
    FrameAt root (fiber.getCont demand skip cause).fiber := by
  refine ⟨?_, (getCont_at root fiber demand skip cause owned.2).1⟩
  have same : (fiber.getCont demand skip cause).fiber.current = fiber.current := by
    unfold FrameFiber.getCont
    split
    · rfl
    · exact pop_current demand skip fiber.stack _ cause
  rw [same]
  exact owned.1

/-- A finished frame run retains the drained frame's source scopes. -/
theorem frame_exit_at (root : NativeEff)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    FrameAt root (frameExitState fiber) := by
  unfold frameExitState
  split <;> exact getCont_frame_at root fiber _ _ none owned

end Effect4.Program.SourceScope
