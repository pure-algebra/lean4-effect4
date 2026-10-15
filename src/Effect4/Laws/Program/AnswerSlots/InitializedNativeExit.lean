import Effect4.Laws.Program.AnswerSlots.InitializedFrame

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual terminal primitive evaluation retains the initialized writer-safe frame graph.
Reach: native finishFrame, actual retained exit code and ordered saved suffixes.
Limit: nonterminal action, park and command closure remain separate producers.
Consumer: the initialized native primitive producer and crew log-history invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Actual frame completion retains a writer-safe frame even before the finish command settles. -/
theorem finish_exit (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack)
    (running : AnswerFlow.External.RunningStep (model spec completed) (Edge spec completed) world output
      (fiber.frame.step (interpAt spec.root completed spec.table).toPrimInterp).1) :
    let next := evaluatePrim.stepFrame (interpAt spec.root completed spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step (interpAt spec.root completed spec.table).toPrimInterp with
  | mk step events =>
    rw [actual] at running
    cases step with
    | running frame => exact ⟨output, running⟩
    | finished finished =>
      exact finished_exit_frame spec completed world input output fiber.frame exit finished current owned saved
        (congrArg Prod.fst actual)

/-- The current successful primitive supplies its actual answer class through the existing head law. -/
theorem success_value (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input : Kind) (value : Val)
    (owned : CodeAt spec world input (.success value)) : ValueAt spec world input value := by
  have typed := head spec fragment completed world input (.success value) owned (by intro thunk wrong; cases wrong)
  cases typed with
  | success value good => exact good

/-- Actual native exit classes admit their own delivered failure and success. -/
theorem current_exit (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input : Kind) (exit : ExitV)
    (owned : CodeAt spec world input (Prim.ofExit exit)) :
    AnswerFlow.ExitAt (model spec completed) world input exit := by
  cases exit with
  | success value => exact success_value spec fragment completed world input value owned
  | failure cause => exact code_phase spec world input _ owned

/-- A native terminal fallback consumes only actual absent finalizer programs. -/
theorem pure_exit_step (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack)
    (pure : ∀ selected,
      (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer = .frame selected →
      AnswerFlow.programOf (model spec completed) world selected
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = none) :
    let next := evaluatePrim.stepFrame (interpAt spec.root completed spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  apply finish_exit spec completed world input output machine fiber yielding exit current owned saved
  have phase := code_phase spec world input _ owned
  have good := current_exit spec fragment completed world input exit (current ▸ owned)
  cases exit with
  | success value =>
    change fiber.frame.current = .success value at current
    simp only [FrameFiber.step, current]
    apply AnswerFlow.External.resume_value (model spec completed) (Edge spec completed)
      (mask_edge spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (family spec fragment completed) world input output fiber.frame value (some (.success value)) good saved
    · intro kind cause; exact phase
    · intro next selected kind
      obtain ⟨cause, rfl⟩ := AnswerFlow.External.getCont_replacement_failure (Edge spec completed) world input output fiber.frame .contA false none saved next selected
      exact .failure phase
    · intro incoming allowed provided member
      cases member
      exact allowed
    · intro selected chosen
      exact pure selected chosen
  | failure cause =>
    change fiber.frame.current = .failure cause at current
    simp only [FrameFiber.step, current]
    apply AnswerFlow.External.resume_cause (model spec completed) (Edge spec completed)
      (mask_edge spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (family spec fragment completed) world input output fiber.frame cause (some (.failure cause)) good saved
    · intro interrupt member kind old allowed; exact phase
    · intro kind cause; exact phase
    · intro next selected kind
      obtain ⟨reason, rfl⟩ := AnswerFlow.External.getCont_replacement_failure (Edge spec completed) world input output fiber.frame .contE true (some cause) saved next selected
      exact .failure phase
    · intro incoming delivered carried allowed provided member
      cases member
      change AnswerFlow.ExitAt (model spec completed) world incoming
        ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause))
      simp only [FramePop.deliveredExit, carried]
      exact phase
    · intro selected chosen delivered carried
      simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected chosen

/-- The actual finalizer dispatcher either installs its certified wrapper or uses the checked pure return. -/
theorem finalizer_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack) :
    let next := evaluatePrim.finalizerOr (interpAt spec.root completed spec.table) machine fiber yielding exit
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  have phase := code_phase spec world input _ owned
  have good := current_exit spec fragment completed world input exit (current ▸ owned)
  have installation (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
      (chosen : (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer = .frame (.onExit body name flag))
      (installed : (interpAt spec.root completed spec.table).finalizerProgram name
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program) :
      let result := evaluatePrim.finalizerOr (interpAt spec.root completed spec.table) machine fiber yielding exit
      AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world output
        result.fiber.frame.current result.fiber.frame.stack := by
    cases exit with
    | success value =>
      change (fiber.frame.getCont .contA false).answer = .frame (.onExit body name flag) at chosen
      change (interpAt spec.root completed spec.table).finalizerProgram name (.success value) = some program at installed
      unfold evaluatePrim.finalizerOr
      dsimp only
      rw [chosen]
      dsimp only
      simp only [FramePop.deliveredExit]
      rw [installed]
      dsimp only
      exact AnswerFlow.External.getCont_value_finalizer (model spec completed)
        (interpAt spec.root completed spec.table).toPrimInterp (Edge spec completed)
        (family spec fragment completed) (mask_edge spec completed) world input output
        fiber.frame value (.onExit body name flag) _ good saved chosen (by
          change ((interpAt spec.root completed spec.table).finalizerProgram name _).map _ = _
          rw [installed]; rfl)
    | failure cause =>
      change (fiber.frame.getCont .contE true (some cause)).answer = .frame (.onExit body name flag) at chosen
      change (interpAt spec.root completed spec.table).finalizerProgram name
        ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some program at installed
      unfold evaluatePrim.finalizerOr
      dsimp only
      rw [chosen]
      dsimp only
      rw [installed]
      dsimp only
      exact AnswerFlow.External.getCont_cause_finalizer (model spec completed)
        (interpAt spec.root completed spec.table).toPrimInterp (Edge spec completed)
        (family spec fragment completed) (mask_edge spec completed) world input output
        fiber.frame cause (.onExit body name flag) _ good
        (by intro interrupt member kind old allowed; exact phase) saved chosen (by
          change ((interpAt spec.root completed spec.table).finalizerProgram name _).map _ = _
          rw [installed]; rfl)

  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body name flag chosen
      split
      · rename_i program installed
        exact ⟨output, by
          have result := installation body name flag program chosen installed
          unfold evaluatePrim.finalizerOr at result
          dsimp only at result
          rw [chosen] at result
          dsimp only at result
          rw [installed] at result
          exact result⟩
      · rename_i missing
        apply pure_exit_step spec fragment completed world input output machine fiber yielding _ current owned saved
        intro selected answer
        have same := chosen.symm.trans answer
        cases same
        change ((interpAt spec.root completed spec.table).finalizerProgram name _).map _ = none
        rw [missing]
        rfl
    · rename_i absent
      apply pure_exit_step spec fragment completed world input output machine fiber yielding _ current owned saved
      intro selected answer
      cases selected
      case onExit body name flag => exact (absent body name flag answer).elim
      all_goals rfl
end Effect4.Program.AnswerSlots.Initialized
