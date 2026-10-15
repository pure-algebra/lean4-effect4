import Effect4.Laws.Machine.AnswerFlowContextualFamily
import Effect4.Machine.Fibers

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: lexical source and numeric callback permissions share actual native value pop transport.
Reach: external saved edges, exact incoming value, actual mask hooks, and the ordered suffix.
Consumers: AnswerFlowPop's unchanged semantic headers and NativeFrameScope's lexical adapters.
Pending causes, supplied exits, source history, and progress remain explicit obligations.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow.Contextual
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
variable (Allowed : World → Option (Cause ε δ ι α) → Prop)
variable (family : ContextualSavedFamily model interp Edge Allowed)
variable (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))

/-- The model's cause classes absorb a recorded interrupt. Latest's failure walk adds it to the
cause it carries past a skipped restoring mask (Effect 4.0.1 `internal/core.ts:580-608`; U-01).
A premise of the failure transport, stated at a fiber's own recorded cause: a fiber with none
meets it at once. -/
def AbsorbsInterrupt (world : World) (recorded : Option (Cause ε δ ι α)) : Prop :=
  ∀ interrupted, recorded = some interrupted → ∀ kind cause,
    model.cause world kind cause → model.cause world kind (Cause.combine cause interrupted)

/-- A fiber with no recorded interrupt meets the premise. -/
theorem absorbsInterrupt_none (world : World) : AbsorbsInterrupt model world none := by
  intro interrupted recorded
  cases recorded

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
    exact popFrom_value_selected model interp Edge Allowed family mask world input output fiber.stack _ value selected rfl good stack found


omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A hook keeps the recorded interrupt. A step of `popFrom_cause_selected`'s scratch
invariant. -/
theorem ensure_recorded (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α) :
    (code.ensure fiber).1.interruptedCause = fiber.interruptedCause := by
  cases code with
  | onExit _ _ _ =>
    simp only [Prim.ensure]
    split <;> rfl
  | asyncFinalizer _ =>
    simp only [Prim.ensure]
    split <;> rfl
  | setInterruptible _ =>
    simp only [Prim.ensure]
    split
    · split <;> rfl
    · rfl
  | yieldNowWith _ => rfl
  | async _ _ _ => rfl
  | success _ => rfl
  | failure _ => rfl
  | sync _ => rfl
  | suspend _ => rfl
  | withFiber _ => rfl
  | yieldableError _ => rfl
  | iterator _ _ => rfl
  | onSuccess _ _ => rfl
  | onSuccessConst _ _ => rfl
  | onFailure _ _ => rfl
  | onSuccessAndFailure _ _ _ => rfl
  | exitFrame _ => rfl
  | whileLoop _ _ => rfl

/-- A drain of a hook's push keeps the recorded interrupt. A step of `popFrom_cause_selected`'s
scratch invariant. -/
private theorem drain_recorded (demand : Arm) (skip : Bool) (fiber : FrameFiber ν σ β ε δ ι α) :
    (FrameFiber.passPushed demand skip fiber).fiber.interruptedCause = fiber.interruptedCause := by
  cases stack : fiber.stack with
  | nil => rw [FrameFiber.passPushed_nil demand skip fiber stack]
  | cons pushed below =>
    rw [FrameFiber.passPushed_fiber demand skip fiber pushed below stack, ensure_recorded]

/-- The fused failure pop discards a restoring mask's replacement. The carried cause is kept,
or, where the restore meets a recorded interrupt, the interrupt is added to it (latest's walk,
Effect 4.0.1 `internal/core.ts:580-608`; U-01).
Consumer: the structural induction proceeds through the original saved list. -/
theorem drain_cause (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (empty : fiber.stack = []) :
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).answer = .empty ∧
    ((FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).carriedCause = some cause ∨
      ∃ interrupted, fiber.interruptedCause = some interrupted ∧
        (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).carriedCause =
          some (Cause.combine cause interrupted)) := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · have nil : (code.ensure fiber).1.stack = [] := kept.trans empty
    exact ⟨by simp only [FrameFiber.passPushed, nil], Or.inl (by simp only [FrameFiber.passPushed, nil])⟩
  · have shape : (code.ensure fiber).1.stack = [.setInterruptible true] := by rw [pushed, empty]
    simp only [FrameFiber.passPushed, shape]
    cases pending : (code.ensure fiber).1.interruptedCause with
    | none => simp only [Prim.ensure]; exact ⟨rfl, Or.inl rfl⟩
    | some interrupted =>
      simp only [Prim.ensure]
      exact ⟨rfl, Or.inr ⟨interrupted, (ensure_recorded code fiber).symm.trans pending, rfl⟩⟩

include interp family in
/-- Passing an interrupted saved frame uses its exact discard or missing-arm clause. -/
theorem saved_discard_cause (world : World) (input middle : Kind)
    (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α)
    (saved : Edge world input middle code)
    (good : model.cause world input cause)
    (interrupted : (code.ensure fiber).1.interrupted = true)
    (absorbs : AbsorbsInterrupt model world (code.ensure fiber).1.interruptedCause)
    (admitted : Allowed world (code.ensure fiber).1.interruptedCause := by trivial) :
    ∃ delivered, FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered ∧
      model.cause world middle delivered := by
  cases arm : code.hasArm .contE with
  | false =>
    have passed := family.skipCause world input middle code saved world
      (model.future_refl world) cause good arm
    cases pending : (code.ensure fiber).1.interruptedCause with
    | none =>
      exact ⟨cause, by simp only [FrameFiber.skippedCause, pending], passed⟩
    | some recorded =>
      exact ⟨Cause.combine cause recorded,
        by simp only [FrameFiber.skippedCause, pending, arm, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte],
        absorbs recorded pending middle cause passed⟩
  | true =>
    have produced : ∃ delivered,
        FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered := by
      cases pending : (code.ensure fiber).1.interruptedCause with
      | none => exact ⟨cause, by simp only [FrameFiber.skippedCause, pending]⟩
      | some other => exact ⟨Cause.sanitize cause other, by simp only [FrameFiber.skippedCause, arm, pending]; rfl⟩
    rcases produced with ⟨delivered, equation⟩
    exact ⟨delivered, equation, family.discard world input middle code saved world
      (model.future_refl world) fiber cause delivered good arm admitted interrupted equation⟩

include interp family mask in
/-- The selected failure callback retains the cause actually carried past earlier discarded handlers. -/
theorem popFrom_cause_selected (world : World) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (selected : Prim ν σ β ε δ ι α)
    (empty : fiber.stack = [])
    (good : model.cause world input cause)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (stack : Path (Edge world) input output frames)
    (found : (FrameFiber.popFrom .contE true frames fiber (some cause)).answer = .frame selected)
    (admitted : Allowed world fiber.interruptedCause := by trivial) :
    ∃ incoming middle delivered,
      (FrameFiber.popFrom .contE true frames fiber (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ Edge world incoming middle selected ∧
      Path (Edge world) middle output
        (FrameFiber.popFrom .contE true frames fiber (some cause)).fiber.stack := by
  have popFamily : PopTrace.Family .contE true (Edge world)
      (fun scratch => scratch.stack = [] ∧ scratch.interruptedCause = fiber.interruptedCause)
      (fun input output carried pop => ∀ cause, carried = some cause → model.cause world input cause →
        pop.answer = .frame selected → ∃ incoming middle delivered,
          pop.carriedCause = some delivered ∧ model.cause world incoming delivered ∧
          Edge world incoming middle selected ∧ Path (Edge world) middle output pop.fiber.stack) := by
    constructor
    · intro kind current before scratch cause incoming good found
      cases found
    · intro input middle output head tail current before answer callback path scratch chosen kept cause incoming good found
      have shape := Prim.answerOf_frame_eq head selected .contE _
        (chosen.trans (congrArg some found))
      rw [shape.1]
      have suffix : Path (Edge world) middle middle current.stack := by
        rw [scratch.1]; exact .nil middle
      exact ⟨input, middle, cause, incoming, good, callback,
        Path.append (ensure_path model Edge mask world middle middle head current suffix) path⟩
    · intro input middle head current after callback scratch
      rw [FrameFiber.passPushed_fiber_cause]
      exact ⟨PopTrace.drain_empty .contE true head current scratch.1,
        (drain_recorded .contE true (head.ensure current).1).trans
          ((ensure_recorded head current).trans scratch.2)⟩
    · intro input middle output head tail current before after tailPop callback path scratch passed drained next cause incoming good found
      have recorded : AbsorbsInterrupt model world (head.ensure current).1.interruptedCause := by
        rw [ensure_recorded head current, scratch.2]; exact absorbs
      have admissible : Allowed world (head.ensure current).1.interruptedCause := by
        rw [ensure_recorded head current, scratch.2]; exact admitted
      have advanced : ∃ delivered, after = some delivered ∧ model.cause world middle delivered := by
        rcases passed with ⟨chosen, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · have missing := PopTrace.answer_missing head .contE _ chosen
          exact ⟨cause, unchanged.trans incoming,
            family.skipCause world input middle head callback world (model.future_refl world) cause good missing⟩
        · rcases saved_discard_cause (admitted := admissible) model interp Edge Allowed family world input middle head current cause callback good
            (by simpa only [Bool.true_and] using skipped) recorded with ⟨delivered, equation, nextGood⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation), nextGood⟩
      rcases advanced with ⟨delivered, changed, nextGood⟩
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      rcases (drain_cause head current delivered scratch.1).2 with kept | ⟨interrupted, pending, combined⟩
      · exact next delivered (by rw [changed]; exact kept) nextGood found
      · exact next (Cause.combine delivered interrupted) (by rw [changed]; exact combined)
          (absorbs interrupted (scratch.2.symm.trans pending) middle delivered nextGood) found
    · intro input middle output head tail current before after tailPop callback path scratch passed answered cause incoming good found
      have recorded : AbsorbsInterrupt model world (head.ensure current).1.interruptedCause := by
        rw [ensure_recorded head current, scratch.2]; exact absorbs
      have admissible : Allowed world (head.ensure current).1.interruptedCause := by
        rw [ensure_recorded head current, scratch.2]; exact admitted
      have produced : ∃ delivered, after = some delivered := by
        rcases passed with ⟨_, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · exact ⟨cause, unchanged.trans incoming⟩
        · rcases saved_discard_cause (admitted := admissible) model interp Edge Allowed family world input middle head current cause callback good
            (by simpa only [Bool.true_and] using skipped) recorded with ⟨delivered, equation, _⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation)⟩
      rcases produced with ⟨delivered, changed⟩
      rw [changed, (drain_cause head current delivered scratch.1).1] at answered
      exact False.elim (answered rfl)
  exact popFamily.popFrom input output frames fiber (some cause) stack ⟨empty, rfl⟩ cause rfl good found

include interp family mask in
/-- Actual getCont selects a failure callback at the class of its delivered cause. -/
theorem getCont_cause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected : Prim ν σ β ε δ ι α)
    (good : model.cause world input cause)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (admitted : Allowed world fiber.interruptedCause := by trivial) :
    ∃ incoming middle delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ Edge world incoming middle selected ∧
      Path (Edge world) middle output (fiber.getCont .contE true (some cause)).fiber.stack := by
  simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at found ⊢
  exact popFrom_cause_selected (admitted := admitted) model interp Edge Allowed family mask world input output fiber.stack _ cause selected rfl good
    absorbs stack found


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
    getCont_value_selected model interp Edge Allowed family mask world input output fiber value selected good stack found
  obtain ⟨head, code, path⟩ := family.answer world incoming middle selected callback world
    (model.future_refl world) value provided next pushed incomingGood (supplied incoming incomingGood) pure evaluated
  exact ⟨_, FrameFiber.resumeValue_frame interp fiber value provided selected next pushed found evaluated,
    head, code, Path.append path suffix⟩

include interp family mask in
/-- The selected cause arm retains the actual mapped supplied exit.
Consumer: a current failure and the numeric form's declared catch callback. -/
theorem resumeCause_provided_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α))
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (good : model.cause world input cause)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (supplied : ∀ incoming delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered →
      model.cause world incoming delivered →
      ∀ exit ∈ provided.map (fiber.getCont .contE true (some cause)).deliveredExit,
        ExitAt model world incoming exit)
    (pure : ∀ delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered →
      programOf model world selected
        ((provided.map (fiber.getCont .contE true (some cause)).deliveredExit).getD
          (.failure delivered)) = none)
    (evaluated : selected.armE interp
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
      (provided.map (fiber.getCont .contE true (some cause)).deliveredExit) = some (next, pushed))
    (admitted : Allowed world fiber.interruptedCause := by trivial) :
    ∃ events, fiber.resumeCause interp cause provided =
      (.running {(fiber.getCont .contE true (some cause)).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack}, events) ∧
      FamilyResult model Edge world output next
        (pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack) := by
  obtain ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩ :=
    getCont_cause_selected (admitted := admitted) model interp Edge Allowed family mask world input output fiber cause selected good absorbs
      stack found
  have equation := FrameFiber.resumeCause_frame interp fiber cause provided selected next pushed found evaluated
  simp only [carried, Option.getD_some] at evaluated
  obtain ⟨head, code, path⟩ := family.cause world incoming middle selected callback world
    (model.future_refl world) delivered _ next pushed incomingGood
    (supplied incoming delivered carried incomingGood) (pure delivered carried) evaluated
  exact ⟨_, equation, head, code, Path.append path suffix⟩

include interp family mask in
/-- The actual selected cause callback consumes the carried cause after real handler discards. -/
theorem resumeCause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (good : model.cause world input cause)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (pure : programOf model world selected
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none)
    (evaluated : selected.armE interp
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) none = some (next, pushed))
    (admitted : Allowed world fiber.interruptedCause := by trivial) :
    ∃ events, fiber.resumeCause interp cause none =
      (.running {(fiber.getCont .contE true (some cause)).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack}, events) ∧
      FamilyResult model Edge world output next (pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack) := by
  exact resumeCause_provided_selected (admitted := admitted) model interp Edge Allowed family mask world input output fiber cause none
    selected next pushed good absorbs stack found
    (by intro incoming delivered carried good exit member; cases member)
    (by intro delivered carried
        simpa only [FramePop.deliveredExit, carried, Option.getD_some, Option.map_none,
          Option.getD_none] using pure)
    evaluated

include interp family mask in
/-- Actual value finalizer interception consumes the selected external edge's program clause. -/
theorem getCont_value_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (selected next : Prim ν σ β ε δ ι α)
    (good : model.value world input value) (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected)
    (installed : programOf model world selected (.success value) = some next) :
    FamilyResult model Edge world output next (fiber.getCont .contA false).fiber.stack := by
  obtain ⟨incoming, middle, incomingGood, callback, suffix⟩ :=
    getCont_value_selected model interp Edge Allowed family mask world input output fiber value selected good stack found
  exact ⟨middle, family.program world incoming middle selected callback world
    (model.future_refl world) (.success value) next incomingGood installed, suffix⟩

include interp family mask in
/-- Actual cause finalizer interception consumes the carried exit after prior handler discards. -/
theorem getCont_cause_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α) (selected next : Prim ν σ β ε δ ι α)
    (good : model.cause world input cause) (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (stack : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (installed : programOf model world selected
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some next)
    (admitted : Allowed world fiber.interruptedCause := by trivial) :
    FamilyResult model Edge world output next (fiber.getCont .contE true (some cause)).fiber.stack := by
  obtain ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩ :=
    getCont_cause_selected (admitted := admitted) model interp Edge Allowed family mask world input output fiber cause selected good absorbs
      stack found
  simp only [FramePop.deliveredExit, carried, Option.getD_some] at installed
  exact ⟨middle, family.program world incoming middle selected callback world
    (model.future_refl world) (.failure delivered) next incomingGood installed, suffix⟩

include family mask in
/-- Actual native finalizer installation retains the selected external callback and its suffix.
Consumers: Timeout's native form adapters and its recursive root suffix.
The model supplies the actual installed wrapper for the exit delivered by getCont. On a failure
exit its cause classes absorb the fiber's recorded interrupt, which latest's walk adds past a
skipped restoring mask. -/
theorem finalizer_step {χ : Type u} {St : Type (max u v)}
    (runInterp : RunInterp ν σ β ε δ ι α χ St)
    (world : World) (input output : Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (exit : Exit β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (name : ν) (flag : Bool) (program : Prim ν σ β ε δ ι α)
    (good : ExitAt model world input exit)
    (absorbs : ∀ cause, exit = .failure cause →
      AbsorbsInterrupt model world fiber.frame.interruptedCause)
    (stack : Path (Edge world) input output fiber.frame.stack)
    (chosen : (fiber.frame.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body name flag))
    (hook : runInterp.finalizerProgram name
      ((fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program)
    (installed : model.finalizer world name
      ((fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) =
      some (finalizerCode runInterp
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) program))
    (admitted : Allowed world fiber.frame.interruptedCause := by trivial) :
    let result := evaluatePrim.finalizerOr runInterp machine fiber yielding exit
    result.machine.state = machine.state ∧
      FamilyResult model Edge world output result.fiber.frame.current result.fiber.frame.stack := by
  cases exit with
  | success value =>
    have typed := getCont_value_finalizer model interp Edge Allowed family mask world input output fiber.frame value
      (.onExit body name flag) (finalizerCode runInterp (.success value) program) good stack chosen installed
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [chosen]
    dsimp only
    rw [hook]
    exact ⟨rfl, typed⟩
  | failure cause =>
    have typed := getCont_cause_finalizer (admitted := admitted) model interp Edge Allowed family mask world input output fiber.frame cause
      (.onExit body name flag)
      (finalizerCode runInterp ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) program)
      good (absorbs cause rfl) stack chosen installed
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [chosen]
    dsimp only
    rw [hook]
    exact ⟨rfl, typed⟩

end Effect4.Machine.AnswerFlow.Contextual

namespace Effect4.Machine.AnswerFlow.External
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
variable (family : SavedFamily model interp Edge)
variable (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))

abbrev AbsorbsInterrupt := Contextual.AbsorbsInterrupt model
abbrev absorbsInterrupt_none := Contextual.absorbsInterrupt_none model
abbrev ensure_path := @Contextual.ensure_path
abbrev drain_cause := @Contextual.drain_cause

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev popFrom_value_selected := Contextual.popFrom_value_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev getCont_value_selected := Contextual.getCont_value_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev saved_discard_cause := Contextual.saved_discard_cause model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True))

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev popFrom_cause_selected := Contextual.popFrom_cause_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev getCont_cause_selected := Contextual.getCont_cause_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev resumeValue_selected := Contextual.resumeValue_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev resumeCause_provided_selected := Contextual.resumeCause_provided_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev resumeCause_selected := Contextual.resumeCause_selected model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev getCont_value_finalizer := Contextual.getCont_value_finalizer model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev getCont_cause_finalizer := Contextual.getCont_cause_finalizer model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

/-- The legacy unconditional family uses the common contextual transport. -/
abbrev finalizer_step {χ : Type u} {St : Type (max u v)} := Contextual.finalizer_step (χ := χ) (St := St) model interp Edge (fun _ _ => True) (family.contextual model interp Edge (fun _ _ => True)) mask

end Effect4.Machine.AnswerFlow.External
