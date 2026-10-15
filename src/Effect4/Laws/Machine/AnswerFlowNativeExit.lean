import Effect4.Laws.Machine.AnswerFlowResume
import Effect4.Laws.Program.NativeFrameScope
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native terminal dispatch consumes the existing saved-family return certificates.
Reach: the actual native frame, selected finalizer and retained ordered suffix at one world.
Consumer: bare initializer and crew native terminal producers.
Cause permissions and actual finalizer representation remain explicit premises.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow.External.Native
open Effect4 Effect4.Machine Effect4.Program
universe w
variable {World Kind : Type w}
variable (model : Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
  (ι := FiberId) (α := Ann) World Kind)
variable (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
variable (Edge : World → Kind → Kind → NCode → Prop)
variable (family : SavedFamily model interp.toPrimInterp Edge)
variable (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))

/-- A native result retains either its actual completed exit or its live current and saved path. -/
def ResultAt (world : World) (output : Kind) (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  match result.outcome with
  | .finished exit => ExitAt model world output exit
  | _ => FamilyResult model Edge world output result.fiber.frame.current result.fiber.frame.stack

/-- The actual native frame dispatcher retains the exit permission of a completed frame. -/
theorem step_frame_result (world : World) (output : Kind) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (typed : FamilyStep model Edge world output (fiber.frame.step interp.toPrimInterp).1) :
    ResultAt model Edge world output (evaluatePrim.stepFrame interp machine fiber yielding) := by
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step interp.toPrimInterp with
  | mk step events =>
    rw [actual] at typed
    cases step with
    | running frame => exact typed
    | finished exit => exact typed

/-- The actual fused continuation pop retains the current primitive. -/
theorem getCont_current (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    (fiber.getCont demand skip cause).fiber.current = fiber.current := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact SourceScope.pop_current demand skip fiber.stack _ cause

/-- Native completion retains its actual current permission and drained saved suffix. -/
theorem finished_frame (world : World) (input _output : Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (finished : ExitV)
    (owned : model.code world input fiber.current)
    (stopped : (fiber.step interp.toPrimInterp).1 = .finished finished) :
    ∃ result, FamilyResult model Edge world result (frameExitState fiber).current (frameExitState fiber).stack := by
  have empty := Effect4.Machine.step_finished_stack interp.toPrimInterp fiber finished stopped
  have same : (frameExitState fiber).current = fiber.current := by
    unfold frameExitState
    split <;> exact getCont_current fiber _ _ none
  refine ⟨input, input, ?_, ?_⟩
  · rw [same]
    exact owned
  · rw [empty]
    exact .nil input

/-- Frame completion joins a running saved-family result with the actual finished frame. -/
theorem finish_exit (world : World) (input output : Kind) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (owned : model.code world input fiber.frame.current)
    (running : RunningStep model Edge world output (fiber.frame.step interp.toPrimInterp).1) :
    let next := evaluatePrim.stepFrame interp machine fiber yielding
    ∃ result, FamilyResult model Edge world result next.fiber.frame.current next.fiber.frame.stack := by
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step interp.toPrimInterp with
  | mk step events =>
    rw [actual] at running
    cases step with
    | running frame => exact ⟨output, running⟩
    | finished finished => exact finished_frame model interp Edge world input output fiber.frame finished owned (congrArg Prod.fst actual)

include family mask in
/-- A native terminal fallback consumes only actual absent finalizer programs. -/
theorem pure_exit_step (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : model.code world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge world) input output fiber.frame.stack)
    (good : ExitAt model world input exit)
    (causes : ∀ kind cause, model.cause world kind cause)
    (pure : ∀ selected,
      (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer = .frame selected →
      AnswerFlow.programOf model world selected
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = none) :
    let next := evaluatePrim.stepFrame interp machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult model Edge world result
      next.fiber.frame.current next.fiber.frame.stack := by
  apply finish_exit model interp Edge world input output machine fiber yielding owned
  cases exit with
  | success value =>
    change fiber.frame.current = .success value at current
    simp only [FrameFiber.step, current]
    apply AnswerFlow.External.resume_value model Edge
      mask interp.toPrimInterp
      family world input output fiber.frame value (some (.success value)) good saved
    · intro kind cause; exact causes kind cause
    · intro next selected kind
      obtain ⟨cause, rfl⟩ := AnswerFlow.External.getCont_replacement_failure Edge world input output fiber.frame .contA false none saved next selected
      exact model.failure world kind _ (causes kind _)
    · intro incoming allowed provided member
      cases member
      exact allowed
    · intro selected chosen
      exact pure selected chosen
  | failure cause =>
    change fiber.frame.current = .failure cause at current
    simp only [FrameFiber.step, current]
    apply AnswerFlow.External.resume_cause model Edge
      mask interp.toPrimInterp
      family world input output fiber.frame cause (some (.failure cause)) good saved
    · intro interrupt member kind old allowed; exact causes kind _
    · intro kind cause; exact causes kind cause
    · intro next selected kind
      obtain ⟨reason, rfl⟩ := AnswerFlow.External.getCont_replacement_failure Edge world input output fiber.frame .contE true (some cause) saved next selected
      exact model.failure world kind _ (causes kind _)
    · intro incoming delivered carried allowed provided member
      cases member
      change AnswerFlow.ExitAt model world incoming
        ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause))
      simp only [FramePop.deliveredExit, carried]
      exact causes incoming _
    · intro selected chosen delivered carried
      simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected chosen


/-- The actual finalizer dispatcher reuses contextual local return and installation producers. -/
theorem finalizer_dispatch (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (Post : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores → Prop)
    (ordinary :
      (∀ body name flag program,
        (fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).answer =
            .frame (.onExit body name flag) →
        interp.finalizerProgram name
          ((fiber.frame.getCont
            (match exit with | .success _ => .contA | .failure _ => .contE)
            (match exit with | .success _ => false | .failure _ => true)
            (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) ≠ some program) →
      Post (evaluatePrim.stepFrame interp machine fiber yielding))
    (installation : ∀ body name flag program,
      (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer =
          .frame (.onExit body name flag) →
      interp.finalizerProgram name
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program →
      Post (evaluatePrim.finalizerOr interp machine fiber yielding exit)) :
    Post (evaluatePrim.finalizerOr interp machine fiber yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body name flag chosen
      split
      · rename_i program installed
        have result := installation body name flag program chosen installed
        unfold evaluatePrim.finalizerOr at result
        dsimp only at result
        rw [chosen] at result
        dsimp only at result
        rw [installed] at result
        exact result
      · rename_i missing
        apply ordinary
        intro other otherName otherFlag program selected
        have equal := chosen.symm.trans selected
        cases equal
        rw [missing]
        intro impossible
        cases impossible
    · rename_i absent
      apply ordinary
      intro body name flag program selected
      exact (absent body name flag selected).elim

include family mask in
/-- The actual finalizer dispatcher either installs its certified wrapper or uses the checked pure return. -/
theorem finalizer_frame (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : model.code world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge world) input output fiber.frame.stack)
    (good : ExitAt model world input exit)
    (causes : ∀ kind cause, model.cause world kind cause)
    (finalizer : ∀ name exit, model.finalizer world name exit =
      (interp.finalizerProgram name exit).map (finalizerCode interp exit)) :
    let next := evaluatePrim.finalizerOr interp machine fiber yielding exit
    ∃ result, AnswerFlow.FamilyResult model Edge world result
      next.fiber.frame.current next.fiber.frame.stack := by
  have installation (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
      (chosen : (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer = .frame (.onExit body name flag))
      (installed : interp.finalizerProgram name
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program) :
      let result := evaluatePrim.finalizerOr interp machine fiber yielding exit
      AnswerFlow.FamilyResult model Edge world output
        result.fiber.frame.current result.fiber.frame.stack := by
    cases exit with
    | success value =>
      change (fiber.frame.getCont .contA false).answer = .frame (.onExit body name flag) at chosen
      change interp.finalizerProgram name (.success value) = some program at installed
      unfold evaluatePrim.finalizerOr
      dsimp only
      rw [chosen]
      dsimp only
      simp only [FramePop.deliveredExit]
      rw [installed]
      dsimp only
      exact AnswerFlow.External.getCont_value_finalizer model
        interp.toPrimInterp Edge
        family mask world input output
        fiber.frame value (.onExit body name flag) _ good saved chosen (by
          change model.finalizer world name _ = _
          rw [finalizer, installed]; rfl)
    | failure cause =>
      change (fiber.frame.getCont .contE true (some cause)).answer = .frame (.onExit body name flag) at chosen
      change interp.finalizerProgram name
        ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some program at installed
      unfold evaluatePrim.finalizerOr
      dsimp only
      rw [chosen]
      dsimp only
      rw [installed]
      dsimp only
      exact AnswerFlow.External.getCont_cause_finalizer model
        interp.toPrimInterp Edge
        family mask world input output
        fiber.frame cause (.onExit body name flag) _ good
        (by intro interrupt member kind old allowed; exact causes kind _) saved chosen (by
          change model.finalizer world name _ = _
          rw [finalizer, installed]; rfl)

  cases exit
  all_goals
    apply finalizer_dispatch interp machine fiber yielding _
      (fun next => ∃ result, FamilyResult model Edge world result next.fiber.frame.current next.fiber.frame.stack)
    · intro absent
      apply pure_exit_step model interp Edge family mask world input output machine fiber yielding _ current owned saved good causes
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change model.finalizer world name _ = none
        rw [finalizer]
        cases actual : interp.finalizerProgram name _ with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
    · intro body name flag program chosen installed
      exact ⟨output, installation body name flag program chosen installed⟩

end Effect4.Machine.AnswerFlow.External.Native
