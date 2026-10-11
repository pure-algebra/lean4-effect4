import Effect4.Laws.Machine.AnswerFlowFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: lexical source and numeric callback permissions share actual native value pop transport.
Reach: external saved edges, exact incoming value, actual mask hooks, and the ordered suffix.
Consumers: AnswerFlowPop's unchanged semantic headers and NativeFrameScope's lexical adapters.
Pending causes, supplied exits, source history, and progress remain explicit obligations.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow.External
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Actual hook insertion adds only an identity edge to the existing saved path. -/
theorem ensure_path
    (_model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))
    (world : World) (input output : Kind) (code : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (stack : Path (Edge world) input output fiber.stack) :
    Path (Edge world) input output (code.ensure fiber).1.stack := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [kept]; exact stack
  · rw [pushed]; exact .cons (mask world input) stack

variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
variable (family : SavedFamily model interp Edge)
variable (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))

include interp family mask in
/-- The actual value pop carries its incoming value into the selected saved callback.
It retains the suffix after that callback's actual mask hook. -/
theorem popFrom_value_selected (world : World) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (value : β) (selected : Prim ν σ β ε δ ι α)
    (empty : fiber.stack = [])
    (good : model.value world input value)
    (stack : Path (Edge world) input output frames)
    (found : (FrameFiber.popFrom .contA false frames fiber).answer = .frame selected) :
    ∃ incoming middle, model.value world incoming value ∧
      Edge world incoming middle selected ∧
      Path (Edge world) middle output (FrameFiber.popFrom .contA false frames fiber).fiber.stack := by
  have popFamily : PopTrace.Family .contA false (Edge world)
      (fun fiber => fiber.stack = [])
      (fun input output _ pop => model.value world input value → pop.answer = .frame selected →
        ∃ incoming middle, model.value world incoming value ∧ Edge world incoming middle selected ∧
          Path (Edge world) middle output pop.fiber.stack) := by
    constructor
    · intro kind fiber cause scratch good found
      cases found
    · intro input middle output head tail fiber cause answer callback path empty chosen kept good found
      have shape := Prim.answerOf_frame_eq head selected .contA _
        (chosen.trans (congrArg some found))
      rw [shape.1]
      have scratch : Path (Edge world) middle middle fiber.stack := by
        rw [empty]; exact .nil middle
      exact ⟨input, middle, good, callback,
        Path.append (ensure_path model Edge mask world middle middle head fiber scratch) path⟩
    · intro input middle head fiber after callback empty
      rw [FrameFiber.passPushed_fiber_cause]; exact PopTrace.drain_empty .contA false head fiber empty
    · intro input middle output head tail fiber before after tailPop callback path empty passed drained next good found
      have missing : head.hasArm .contA = false := by
        rcases passed with ⟨chosen, _⟩ | ⟨answer, _, skipped, _⟩
        · exact PopTrace.answer_missing head .contA _ chosen
        · cases skipped
      have nextGood : model.value world middle value :=
        family.skip world input middle head callback world (model.future_refl world) value good missing
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      exact next nextGood found
    · intro input middle output head tail fiber before after tailPop callback path empty passed answered good found
      unfold FrameFiber.passOn FrameFiber.joinPushed at found
      split at found
      · rename_i drained; exact False.elim (answered drained)
      · rw [FrameFiber.passPushed_answer_cause] at found
        exact False.elim (PopTrace.drain_not_frame .contA false rfl head selected fiber empty found)
  exact popFamily.popFrom input output frames fiber none (stack) empty good found

include interp family mask in
/-- Actual getCont retains the selected callback and its ordered suffix.
Deferred and replacement answers cannot inhabit this selected-frame branch. -/
theorem getCont_value_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (selected : Prim ν σ β ε δ ι α)
    (good : model.value world input value)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected) :
    ∃ incoming middle, model.value world incoming value ∧
      Edge world incoming middle selected ∧
      Path (Edge world) middle output (fiber.getCont .contA false).fiber.stack := by
  unfold FrameFiber.getCont at found ⊢
  split
  · rename_i deferred
    rw [if_pos deferred] at found
    cases found
  · rename_i normal
    rw [if_neg normal] at found
    exact popFrom_value_selected model interp Edge family mask world input output fiber.stack _ value selected rfl good stack found


/-- The fused failure pop discards a restoring mask's replacement and retains its carried cause.
Consumer: the structural induction proceeds through the original saved list. -/
theorem drain_cause (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (empty : fiber.stack = []) :
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).answer = .empty ∧
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).carriedCause = some cause := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · simp only [FrameFiber.passPushed, kept.trans empty]
    exact ⟨True.intro, True.intro⟩
  · have shape : (code.ensure fiber).1.stack = [.setInterruptible true] := by rw [pushed, empty]
    simp only [FrameFiber.passPushed, shape]
    cases pending : (code.ensure fiber).1.interruptedCause with
    | none => simp only [Prim.ensure]; exact ⟨rfl, rfl⟩
    | some interrupted => simp only [Prim.ensure]; exact ⟨rfl, rfl⟩

include interp family in
/-- Passing an interrupted saved frame uses its exact discard or missing-arm clause. -/
theorem saved_discard_cause (world : World) (input middle : Kind)
    (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α)
    (saved : Edge world input middle code)
    (good : model.cause world input cause)
    (interrupted : (code.ensure fiber).1.interrupted = true) :
    ∃ delivered, FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered ∧
      model.cause world middle delivered := by
  cases arm : code.hasArm .contE with
  | false =>
    have unchanged : FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some cause := by
      simp only [FrameFiber.skippedCause, arm, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨cause, unchanged, family.skipCause world input middle code saved world
      (model.future_refl world) cause good arm⟩
  | true =>
    have produced : ∃ delivered,
        FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered := by
      cases pending : (code.ensure fiber).1.interruptedCause with
      | none => exact ⟨cause, by simp only [FrameFiber.skippedCause, arm, pending]; rfl⟩
      | some other => exact ⟨Cause.sanitize cause other, by simp only [FrameFiber.skippedCause, arm, pending]; rfl⟩
    rcases produced with ⟨delivered, equation⟩
    exact ⟨delivered, equation, family.discard world input middle code saved world
      (model.future_refl world) fiber cause delivered good arm interrupted equation⟩

include interp family mask in
/-- The selected failure callback retains the cause actually carried past earlier discarded handlers. -/
theorem popFrom_cause_selected (world : World) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (selected : Prim ν σ β ε δ ι α)
    (empty : fiber.stack = [])
    (good : model.cause world input cause)
    (stack : Path (Edge world) input output frames)
    (found : (FrameFiber.popFrom .contE true frames fiber (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (FrameFiber.popFrom .contE true frames fiber (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ Edge world incoming middle selected ∧
      Path (Edge world) middle output
        (FrameFiber.popFrom .contE true frames fiber (some cause)).fiber.stack := by
  have popFamily : PopTrace.Family .contE true (Edge world)
      (fun fiber => fiber.stack = [])
      (fun input output carried pop => ∀ cause, carried = some cause → model.cause world input cause →
        pop.answer = .frame selected → ∃ incoming middle delivered,
          pop.carriedCause = some delivered ∧ model.cause world incoming delivered ∧
          Edge world incoming middle selected ∧ Path (Edge world) middle output pop.fiber.stack) := by
    constructor
    · intro kind fiber before scratch cause incoming good found
      cases found
    · intro input middle output head tail fiber before answer callback path empty chosen kept cause incoming good found
      have shape := Prim.answerOf_frame_eq head selected .contE _
        (chosen.trans (congrArg some found))
      rw [shape.1]
      have scratch : Path (Edge world) middle middle fiber.stack := by
        rw [empty]; exact .nil middle
      exact ⟨input, middle, cause, incoming, good, callback,
        Path.append (ensure_path model Edge mask world middle middle head fiber scratch) path⟩
    · intro input middle head fiber after callback empty
      rw [FrameFiber.passPushed_fiber_cause]; exact PopTrace.drain_empty .contE true head fiber empty
    · intro input middle output head tail fiber before after tailPop callback path empty passed drained next cause incoming good found
      have advanced : ∃ delivered, after = some delivered ∧ model.cause world middle delivered := by
        rcases passed with ⟨chosen, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · have missing := PopTrace.answer_missing head .contE _ chosen
          exact ⟨cause, unchanged.trans incoming,
            family.skipCause world input middle head callback world (model.future_refl world) cause good missing⟩
        · rcases saved_discard_cause model interp Edge family world input middle head fiber cause callback good
            (by simpa only [Bool.true_and] using skipped) with ⟨delivered, equation, nextGood⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation), nextGood⟩
      rcases advanced with ⟨delivered, changed, nextGood⟩
      have causeKept := (drain_cause head fiber delivered empty).2
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      exact next delivered (by rw [changed]; exact causeKept) nextGood found
    · intro input middle output head tail fiber before after tailPop callback path empty passed answered cause incoming good found
      have produced : ∃ delivered, after = some delivered := by
        rcases passed with ⟨_, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · exact ⟨cause, unchanged.trans incoming⟩
        · rcases saved_discard_cause model interp Edge family world input middle head fiber cause callback good
            (by simpa only [Bool.true_and] using skipped) with ⟨delivered, equation, _⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation)⟩
      rcases produced with ⟨delivered, changed⟩
      rw [changed, (drain_cause head fiber delivered empty).1] at answered
      exact False.elim (answered rfl)
  exact popFamily.popFrom input output frames fiber (some cause) stack empty cause rfl good found

include interp family mask in
/-- Actual getCont selects a failure callback at the class of its delivered cause. -/
theorem getCont_cause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected : Prim ν σ β ε δ ι α)
    (good : model.cause world input cause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ Edge world incoming middle selected ∧
      Path (Edge world) middle output (fiber.getCont .contE true (some cause)).fiber.stack := by
  simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at found ⊢
  exact popFrom_cause_selected model interp Edge family mask world input output fiber.stack _ cause selected rfl good stack found


include interp family mask in
/-- The actual selected value callback retains its result over the remaining ordered suffix.
Supplied exits and finalizer interception stay explicit at the selected incoming class. -/
theorem resumeValue_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (provided : Option (Exit β ε δ ι α))
    (good : model.value world input value)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected)
    (supplied : ∀ incoming, model.value world incoming value → ∀ exit ∈ provided, ExitAt model world incoming exit)
    (pure : programOf model world selected (provided.getD (.success value)) = none)
    (evaluated : selected.armA interp value provided = some (next, pushed)) :
    ∃ events, fiber.resumeValue interp value provided =
      (.running {(fiber.getCont .contA false).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contA false).fiber.stack}, events) ∧
      FamilyResult model Edge world output next (pushed ++ (fiber.getCont .contA false).fiber.stack) := by
  obtain ⟨incoming, middle, incomingGood, callback, suffix⟩ :=
    getCont_value_selected model interp Edge family mask world input output fiber value selected good stack found
  obtain ⟨head, code, path⟩ := family.answer world incoming middle selected callback world
    (model.future_refl world) value provided next pushed incomingGood (supplied incoming incomingGood) pure evaluated
  exact ⟨_, FrameFiber.resumeValue_frame interp fiber value provided selected next pushed found evaluated,
    head, code, Path.append path suffix⟩

include interp family mask in
/-- The actual selected cause callback consumes the carried cause after real handler discards. -/
theorem resumeCause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (good : model.cause world input cause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (pure : programOf model world selected
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none)
    (evaluated : selected.armE interp
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) none = some (next, pushed)) :
    ∃ events, fiber.resumeCause interp cause none =
      (.running {(fiber.getCont .contE true (some cause)).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack}, events) ∧
      FamilyResult model Edge world output next (pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack) := by
  obtain ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩ :=
    getCont_cause_selected model interp Edge family mask world input output fiber cause selected good stack found
  have equation := FrameFiber.resumeCause_frame interp fiber cause none selected next pushed found evaluated
  simp only [carried, Option.getD_some] at evaluated
  simp only [FramePop.deliveredExit, carried, Option.getD_some] at pure
  obtain ⟨head, code, path⟩ := family.cause world incoming middle selected callback world
    (model.future_refl world) delivered none next pushed incomingGood
    (by intro exit member; cases member) pure evaluated
  exact ⟨_, equation, head, code, Path.append path suffix⟩

include interp family mask in
/-- Actual value finalizer interception consumes the selected external edge's program clause. -/
theorem getCont_value_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (selected next : Prim ν σ β ε δ ι α)
    (good : model.value world input value) (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected)
    (installed : programOf model world selected (.success value) = some next) :
    FamilyResult model Edge world output next (fiber.getCont .contA false).fiber.stack := by
  obtain ⟨incoming, middle, incomingGood, callback, suffix⟩ :=
    getCont_value_selected model interp Edge family mask world input output fiber value selected good stack found
  exact ⟨middle, family.program world incoming middle selected callback world
    (model.future_refl world) (.success value) next incomingGood installed, suffix⟩

include interp family mask in
/-- Actual cause finalizer interception consumes the carried exit after prior handler discards. -/
theorem getCont_cause_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α) (selected next : Prim ν σ β ε δ ι α)
    (good : model.cause world input cause) (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (installed : programOf model world selected
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some next) :
    FamilyResult model Edge world output next (fiber.getCont .contE true (some cause)).fiber.stack := by
  obtain ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩ :=
    getCont_cause_selected model interp Edge family mask world input output fiber cause selected good stack found
  simp only [FramePop.deliveredExit, carried, Option.getD_some] at installed
  exact ⟨middle, family.program world incoming middle selected callback world
    (model.future_refl world) (.failure delivered) next incomingGood installed, suffix⟩

end Effect4.Machine.AnswerFlow.External
