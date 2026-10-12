import Effect4.Laws.Program.NativeInterpScope
import Effect4.Laws.Machine.AnswerFlowFamilyPop

/-!
# Source scope through the actual frame machine

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The predicates inspect existing primitive frames and their existing saved names.
The pop proof retains the actual answering frame and every remaining stack slot.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- Every saved primitive frame retains its source-bearing slots. -/
def StackAt (root : NativeEff) (frames : List NCode) : Prop := ∀ code ∈ frames, CodeAt root code

/-- The existing lexical saved predicate is the Unit instance of the shared ordered path. -/
theorem stack_path_at (root : NativeEff) (frames : List NCode) (owned : StackAt root frames) :
    Effect4.Contracts.Path (fun (_ _ : Unit) code => CodeAt root code) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons head rest ih =>
    exact .cons (owned head (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Reading the shared path retains every existing lexical saved primitive. -/
theorem path_stack_at (root : NativeEff) {input output : Unit} {frames : List NCode}
    (path : Effect4.Contracts.Path (fun (_ _ : Unit) code => CodeAt root code) input output frames) : StackAt root frames := by
  induction path with
  | nil => intro code member; cases member
  | cons head tail ih =>
    intro code member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; exact head
    · exact ih code later

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
  have family : PopTrace.Family demand skip
      (fun (_ _ : Unit) code => CodeAt root code) (fun fiber => StackAt root fiber.stack)
      (fun _ _ _ pop => StackAt root pop.fiber.stack ∧ AnswerAt root pop.answer) := by
    constructor
    · intro kind fiber cause owned; exact ⟨owned, trivial⟩
    · intro input middle output head tail fiber cause answer owned path scratch chosen kept
      exact ⟨stack_append_at root _ _ (ensure_stack_at root head fiber scratch) (path_stack_at root path),
        answerOf_at root head demand _ answer owned (ensure_replacement_at root head fiber) chosen⟩
    · intro input middle head fiber after owned scratch
      exact (passPushed_at root demand skip (head.ensure fiber).1 after
        (ensure_stack_at root head fiber scratch)).1
    · intro input middle output head tail fiber before after tailPop owned path scratch passed drained next
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained]
      exact next
    · intro input middle output head tail fiber before after tailPop owned path scratch passed answered
      have pushed := passPushed_at root demand skip (head.ensure fiber).1 after
        (ensure_stack_at root head fiber scratch)
      unfold FrameFiber.passOn FrameFiber.joinPushed
      split
      · rename_i drained; exact False.elim (answered drained)
      · exact ⟨stack_append_at root _ _ pushed.1 (path_stack_at root path), pushed.2⟩
  exact family.popFrom () () frames fiber cause (stack_path_at root frames owned) scratch

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

/-- The lexical frame instance keeps its existing source predicate and admits every answer. -/
def lexicalModel (root : NativeEff) :
    AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err)
      (δ := Defect) (ι := FiberId) (α := Ann) Unit Unit where
  future := fun _ _ => True
  future_refl := fun _ => trivial
  future_trans := fun _ _ _ _ _ => trivial
  value := fun _ _ _ => True
  cause := fun _ _ _ => True
  code := fun _ _ => CodeAt root
  finalizer := fun _ _ _ => none
  success := fun _ _ _ _ => trivial
  failure := fun _ _ _ _ => trivial

/-- Every existing lexical saved primitive is an external edge, including recursive loop callbacks. -/
def lexicalEdge (root : NativeEff) (_ : Unit) (_ _ : Unit) :
    Prim EffName EffThunk Val Err Defect FiberId Ann → Prop := CodeAt root

/-- The lexical callback equations instantiate all six obligations without finite loop unrolling. -/
theorem lexical_family (root : NativeEff) (fragment : Fragment root)
    (completed : List (FiberId × Exit Val Err Defect FiberId Ann)) (table : RowTable) :
    AnswerFlow.SavedFamily (lexicalModel root) (interpAt root completed table).toPrimInterp
      (lexicalEdge root) := by
  constructor
  · intro world input output frame held nextWorld future value good absent; trivial
  · intro world input output frame held nextWorld future cause good absent; trivial
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent arm
    obtain ⟨code, stack⟩ := armA_at root fragment completed table frame value provided next pushed held arm
    exact ⟨(), code, stack_path_at root pushed stack⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent arm
    obtain ⟨code, stack⟩ := armE_at root fragment completed table frame cause provided next pushed held arm
    exact ⟨(), code, stack_path_at root pushed stack⟩
  · intro world input output frame held nextWorld future exit next good installed
    have absent := AnswerFlow.programOf_none (lexicalModel root) nextWorld frame exit (fun _ => rfl)
    rw [absent] at installed
    cases installed
  · intro world input output frame held nextWorld future fiber cause delivered good arm interrupted skipped; trivial

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
  have callback (frame : NCode) (next : NCode) (pushed : List NCode)
      (held : CodeAt root frame)
      (found : frame.armA (interpAt root completed table).toPrimInterp value provided = some (next, pushed)) :
      CodeAt root next ∧ StackAt root pushed := by
    obtain ⟨input, code, path⟩ := (lexical_family root fragment completed table).answer () () () frame held
      () trivial value provided next pushed trivial (by intro exit member; cases exit <;> trivial)
      (AnswerFlow.programOf_none (lexicalModel root) () frame _ (fun _ => rfl)) found
    exact ⟨code, path_stack_at root path⟩
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  all_goals aesop (add norm simp [FrameStepAt, FrameAt, AnswerAt, CodeAt, FrameFiber.getCont_fiber_cause, FrameFiber.getCont_answer_cause]) (add safe apply [stack_append_at]) (add safe forward [callback])

/-- Resuming a cause uses the actual owned pop answer and source cause arm. -/
theorem resumeCause_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    FrameStepAt root ((fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1) := by
  let interp := (interpAt root completed table).toPrimInterp
  let pop := fiber.getCont .contE true (some cause)
  have retained := getCont_at root fiber .contE true (some cause) owned.2
  change FrameStepAt root ((fiber.resumeCause interp cause provided).1)
  cases selected : pop.answer with
  | empty =>
    rw [FrameFiber.resumeCause_empty interp fiber cause provided selected]
    trivial
  | deferred delivered =>
    rw [FrameFiber.resumeCause_deferred interp fiber cause delivered provided selected]
    exact ⟨trivial, retained.1⟩
  | replacement next =>
    rw [FrameFiber.resumeCause_replacement interp fiber cause provided next selected]
    have source := retained.2
    rw [selected] at source
    exact ⟨source, retained.1⟩
  | frame frame =>
    cases evaluated : frame.armE interp (pop.carriedCause.getD cause)
        (provided.map pop.deliveredExit) with
    | none =>
      change (fiber.getCont .contE true (some cause)).answer = .frame frame at selected
      change frame.armE interp ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
        (provided.map (fiber.getCont .contE true (some cause)).deliveredExit) = none at evaluated
      simp only [FrameFiber.resumeCause, selected, evaluated, FrameStepAt]
    | some result =>
      obtain ⟨next, pushed⟩ := result
      obtain ⟨events, actual, input, code, suffix⟩ :=
        AnswerFlow.External.resumeCause_provided_selected (lexicalModel root) interp
          (lexicalEdge root) (lexical_family root fragment completed table)
          (fun _ _ => trivial) () () () fiber cause provided frame next pushed trivial
          (stack_path_at root fiber.stack owned.2) selected
          (by intro incoming delivered carried good exit member; cases exit <;> trivial)
          (by intro delivered carried
              exact AnswerFlow.programOf_none (lexicalModel root) () frame _ (fun _ => rfl))
          evaluated
      rw [actual]
      exact ⟨code, path_stack_at root suffix⟩

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
  case onSuccess body name =>
    obtain ⟨after, events, ran, code, suffix⟩ := AnswerFlow.push_success_path (lexicalModel root)
      (interpAt root completed table).toPrimInterp () () () () (lexicalEdge root) fiber body name h
      current.1 current (stack_path_at root fiber.stack stack)
    have actual := congrArg (FrameStepAt root) (congrArg Prod.fst ran)
    have result := actual.mpr (show FrameStepAt root (.running after) from ⟨code, path_stack_at root suffix⟩)
    simpa only [FrameFiber.step, h] using result
  case onFailure body name =>
    obtain ⟨after, events, ran, code, suffix⟩ := AnswerFlow.push_failure_path (lexicalModel root)
      (interpAt root completed table).toPrimInterp () () () () (lexicalEdge root) fiber body name h
      current.1 current (stack_path_at root fiber.stack stack)
    have actual := congrArg (FrameStepAt root) (congrArg Prod.fst ran)
    have result := actual.mpr (show FrameStepAt root (.running after) from ⟨code, path_stack_at root suffix⟩)
    simpa only [FrameFiber.step, h] using result
  case whileLoop name cursor =>
    have slots := interp_loopEnter_at root fragment completed table name cursor current
    have produced : match (interpAt root completed table).loopEnter name cursor with
        | .continue next body => AnswerFlow.FamilyResult (lexicalModel root) (lexicalEdge root) () () body [.whileLoop name next]
        | .finish body => AnswerFlow.FamilyResult (lexicalModel root) (lexicalEdge root) () () body [] := by
      cases actual : (interpAt root completed table).loopEnter name cursor with
      | «continue» next body =>
        rw [actual] at slots
        exact ⟨(), slots, .cons current (.nil ())⟩
      | finish body =>
        rw [actual] at slots
        exact ⟨(), slots, .nil ()⟩
    obtain ⟨after, ran, input, code, suffix⟩ := AnswerFlow.loop_step (lexicalModel root)
      (interpAt root completed table).toPrimInterp (lexicalEdge root) () () () fiber name cursor h
      (stack_path_at root fiber.stack stack)
      (by intro next body found; rw [found] at produced; exact produced)
      (by intro body found; rw [found] at produced; exact produced)
    have actual := congrArg (FrameStepAt root) ran
    have result := actual.mpr (show FrameStepAt root (.running after) from ⟨code, path_stack_at root suffix⟩)
    simpa only [FrameFiber.step, h] using result
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
