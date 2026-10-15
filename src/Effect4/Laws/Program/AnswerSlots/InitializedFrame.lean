import Effect4.Laws.Program.AnswerSlots.InitializedSync
import Effect4.Laws.Machine.AnswerFlowResume
import Effect4.Laws.Program.NativeFrameScope
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the initialized graph follows actual current-frame transitions and native sync answers.
Reach: the existing ordered saved family and actual source interpreter.
Limit: native finalizer interception, action results and command closure remain separate.
Consumer: the initialized primitive evaluator and crew log-history producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- Saved callbacks remain valid when the actual native stores grow. -/
theorem edge_future (spec : Spec) (completed : List (FiberId × ExitV)) (first last : World)
    (future : Future first last) (input output : Kind) (frame : NCode)
    (held : Edge spec completed first input output frame) : Edge spec completed last input output frame := by
  apply AnswerFlow.FamilyEmbedding.edge_future_over (embedding spec completed)
    (Semantic spec) (Typed.Edge spec.toSpec completed) ?_ ?_ first last future input output frame held
  · intro before after later incoming outgoing code owned
    exact AnswerFlow.ViewSavedAt.future (fun view => model spec view)
      (fun view => (interpAt spec.root view spec.table).toPrimInterp) (fun _ => later) owned
  · intro before after later incoming outgoing code owned
    cases before
    cases after
    exact owned

/-- The same ordered saved suffix remains valid after native store growth. -/
theorem path_future (spec : Spec) (completed : List (FiberId × ExitV)) (first last : World)
    (future : Future first last) (input output : Kind) (frames : List NCode)
    (held : Effect4.Contracts.Path (Edge spec completed first) input output frames) :
    Effect4.Contracts.Path (Edge spec completed last) input output frames :=
  held.map (edge_future spec completed first last future)

/-- Either restoring mask is an identity saved edge at every initialized answer class. -/
theorem mask_edge_flag (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (flag : Bool) : Edge spec completed world kind kind (.setInterruptible flag) :=
  .saved ⟨(fun view => AnswerFlow.saved_mask (model spec view)
    (interpAt spec.root view spec.table).toPrimInterp world kind flag),
    (by intro loop cursor same; cases same), (by intro generator cursor same; cases same)⟩

/-- The native exit restoration uses the true-mask instance. -/
theorem mask_edge (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) : Edge spec completed world kind kind (.setInterruptible true) :=
  mask_edge_flag spec completed world kind true

/-- Every nonterminal pure step consumes the existing head theorem without another primitive walk. -/
theorem nonterminal_step (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : CodeAt spec world input fiber.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.stack)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk) :
    AnswerFlow.FamilyStep (model spec completed) (Edge spec completed) world output
      (fiber.step (interpAt spec.root completed spec.table).toPrimInterp).1 := by
  apply AnswerFlow.frame_step (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
    (Edge spec completed) world input output fiber
    (head spec fragment completed world input fiber.current owned noSync) saved
  · intro value provided actual good
    rcases actual with ⟨current, supplied⟩ | ⟨thunk, current, valueEq, supplied⟩
    · exact (noSuccess value current).elim
    · exact (noSync thunk current).elim
  · intro cause current good
    exact (noFailure cause current).elim

/-- A real synchronous native answer updates the class and retains its actual saved suffix. -/
theorem sync_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (thunk : EffThunk) (state : Stores) (value : Val)
    (current : fiber.current = .sync thunk) (owned : CodeAt spec world input fiber.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.stack)
    (ran : (interpAt spec.root completed spec.table).syncState thunk world.state = some (state, value)) :
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) ⟨world.owner, state⟩ output
      (.success value) fiber.stack := by
  have code : CodeAt spec world input (.sync thunk) := current ▸ owned
  exact ⟨input, .success (sync_value spec completed world input thunk state value code ran),
    path_future spec completed world ⟨world.owner, state⟩ (sync_future spec completed world thunk state value ran)
      input output fiber.stack saved⟩

/-- A missing native synchronous operation uses the existing checked fallback value class. -/
theorem fallback_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (thunk : EffThunk)
    (current : fiber.current = .sync thunk) (owned : CodeAt spec world input fiber.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.stack)
    (missing : (interpAt spec.root completed spec.table).syncState thunk world.state = none) :
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world output
      (.success ((interpAt spec.root completed spec.table).syncValue thunk)) fiber.stack := by
  exact ⟨input, .success (sync_fallback spec completed world input thunk (current ▸ owned) missing), saved⟩

/-- The actual fused pop retains its existing current primitive. -/
theorem getCont_current (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    (fiber.getCont demand skip cause).fiber.current = fiber.current := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact SourceScope.pop_current demand skip fiber.stack _ cause

/-- A finished exit retains a valid current class in its actual drained frame.
The output class is existential because this invariant protects writers, not the root result. -/
theorem finished_exit_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (exit finished : ExitV) (_current : fiber.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.current)
    (_saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.stack)
    (stopped : (fiber.step (interpAt spec.root completed spec.table).toPrimInterp).1 = .finished finished) :
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      (frameExitState fiber).current (frameExitState fiber).stack := by
  have empty := Effect4.Machine.step_finished_stack
    (interpAt spec.root completed spec.table).toPrimInterp fiber finished stopped
  have same : (frameExitState fiber).current = fiber.current := by
    unfold frameExitState
    split <;> exact getCont_current fiber _ _ none
  refine ⟨input, input, ?_, ?_⟩
  · rw [same]
    exact owned
  · rw [empty]
    exact .nil input
end Effect4.Program.AnswerSlots.Initialized
