import Effect4.Laws.Machine.AnswerFlowFamilyPop

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual terminal returns reuse the shared selected-arm and pop-family proofs.
Reach: arbitrary saved families and mask edges over the existing continuation pop.
Limit: callback answers, installed finalizers and admissible pending causes remain explicit.
Consumer: initialized crew native primitive evaluation.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow.External
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
variable (mask : ∀ world kind, Edge world kind kind (.setInterruptible true))

include model mask in
/-- The actual fused continuation pop retains an ordered saved suffix at some incoming class. -/
theorem popFrom_suffix (world : World) (input output : Kind) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) (empty : fiber.stack = [])
    (stack : Path (Edge world) input output frames) :
    ∃ incoming, Path (Edge world) incoming output (FrameFiber.popFrom demand skip frames fiber cause).fiber.stack := by
  have family : PopTrace.Family demand skip (Edge world) (fun fiber => fiber.stack = [])
      (fun _ output _ pop => ∃ incoming, Path (Edge world) incoming output pop.fiber.stack) := by
    constructor
    · intro kind fiber cause scratch
      exact ⟨kind, by rw [scratch]; exact .nil kind⟩
    · intro input middle output head tail fiber cause answer callback path scratch chosen kept
      have detached : Path (Edge world) middle middle fiber.stack := by rw [scratch]; exact .nil middle
      exact ⟨middle, Path.append (ensure_path model Edge mask world middle middle head fiber detached) path⟩
    · intro input middle head fiber after callback scratch
      rw [FrameFiber.passPushed_fiber_cause]
      exact PopTrace.drain_empty demand skip head fiber scratch
    · intro input middle output head tail fiber before after tailPop callback path scratch passed drained next
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained]
      exact next
    · intro input middle output head tail fiber before after tailPop callback path scratch passed answered
      have cleared := PopTrace.drain_empty demand skip head fiber scratch
      rw [← FrameFiber.passPushed_fiber_cause demand skip (head.ensure fiber).1 after] at cleared
      unfold FrameFiber.passOn FrameFiber.joinPushed
      split
      · rename_i drained
        exact (answered drained).elim
      · exact ⟨middle, by rw [cleared, List.nil_append]; exact path⟩
  exact family.popFrom input output frames fiber cause stack empty

include model mask in
/-- Every actual getCont branch retains an ordered saved suffix, including deferred interrupts. -/
theorem getCont_suffix (world : World) (input output : Kind) (fiber : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (stack : Path (Edge world) input output fiber.stack) :
    ∃ incoming, Path (Edge world) incoming output (fiber.getCont demand skip cause).fiber.stack := by
  unfold FrameFiber.getCont
  split
  · exact ⟨input, stack⟩
  · exact popFrom_suffix model Edge mask world input output demand skip fiber.stack _ cause rfl stack
omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Every replacement emitted by an existing mask hook is an actual failure primitive. -/
theorem ensure_replacement_failure (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (next : Prim ν σ β ε δ ι α)
    (found : (frame.ensure fiber).2 = some next) : ∃ cause, next = .failure cause := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (add norm simp [Prim.ensure])

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Existing hook answers replace code only with a failure primitive. -/
theorem answer_replacement_failure (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (next : Prim ν σ β ε δ ι α)
    (found : frame.answerOf demand (frame.ensure fiber).2 = some (.replacement next)) :
    ∃ cause, next = .failure cause := by
  cases replacement : (frame.ensure fiber).2 with
  | some program =>
    rw [replacement, Prim.answerOf_replacement] at found
    cases found
    exact ensure_replacement_failure frame fiber next replacement
  | none =>
    simp only [replacement, Prim.answerOf] at found
    split at found <;> cases found

/-- The actual one-frame hook drain also replaces code only with a failure primitive. -/
theorem drain_replacement_failure (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (recorded : Option (Cause ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (found : (FrameFiber.passPushed demand skip fiber recorded).answer = .replacement next) :
    ∃ cause, next = .failure cause := by
  unfold FrameFiber.passPushed at found
  cases frames : fiber.stack with
  | nil => rw [frames] at found; cases found
  | cons pushed below =>
    rw [frames] at found
    dsimp only at found
    split at found
    · rename_i answer selected
      split at found
      · cases found
      · cases found
        exact answer_replacement_failure pushed {fiber with stack := below} demand next selected
    · cases found

/-- Actual fused pops replace code only with a represented failure from a mask hook. -/
theorem popFrom_replacement_failure (world : World) (input output : Kind) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (recorded : Option (Cause ε δ ι α)) (stack : Path (Edge world) input output frames)
    (empty : fiber.stack = []) (next : Prim ν σ β ε δ ι α)
    (found : (FrameFiber.popFrom demand skip frames fiber recorded).answer = .replacement next) :
    ∃ cause, next = .failure cause := by
  have family : PopTrace.Family demand skip (Edge world) (fun fiber => fiber.stack = [])
      (fun _ _ _ pop => pop.answer = .replacement next → ∃ cause, next = .failure cause) := by
    constructor
    · intro kind fiber cause scratch found
      cases found
    · intro input middle output head tail fiber cause answer callback path scratch chosen kept found
      cases found
      exact answer_replacement_failure head fiber demand next chosen
    · intro input middle head fiber after callback scratch
      rw [FrameFiber.passPushed_fiber_cause]
      exact PopTrace.drain_empty demand skip head fiber scratch
    · intro input middle output head tail fiber before after tailPop callback path scratch passed drained nextProof found
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found
      exact nextProof found
    · intro input middle output head tail fiber before after tailPop callback path scratch passed answered found
      unfold FrameFiber.passOn FrameFiber.joinPushed at found
      split at found
      · rename_i drained
        exact (answered drained).elim
      · exact drain_replacement_failure _ demand skip after next found
  exact family.popFrom input output frames fiber recorded stack empty found

/-- Actual continuation lookup can replace current code only with a failure primitive. -/
theorem getCont_replacement_failure (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (recorded : Option (Cause ε δ ι α)) (stack : Path (Edge world) input output fiber.stack)
    (next : Prim ν σ β ε δ ι α) (found : (fiber.getCont demand skip recorded).answer = .replacement next) :
    ∃ cause, next = .failure cause := by
  unfold FrameFiber.getCont at found
  split at found
  · cases found
  · exact popFrom_replacement_failure Edge world input output demand skip fiber.stack _ recorded stack rfl next found

/-- A running frame retains its typed saved path; a finished step asserts no terminal answer class. -/
def RunningStep (world : World) (output : Kind) : FrameStep ν σ β ε δ ι α → Prop
  | .running fiber => FamilyResult model Edge world output fiber.current fiber.stack
  | .finished _ => True

variable (interp : PrimInterp ν σ β ε δ ι α) (family : SavedFamily model interp Edge)

include family mask in
/-- A whole value return consumes the existing selected-arm theorem and the retained saved suffix. -/
theorem resume_value (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Exit β ε δ ι α))
    (good : model.value world input value) (stack : Path (Edge world) input output fiber.stack)
    (causes : ∀ kind cause, model.cause world kind cause)
    (replacement : ∀ next, (fiber.getCont .contA false).answer = .replacement next →
      ∀ kind, model.code world kind next)
    (supplied : ∀ incoming, model.value world incoming value → ∀ exit ∈ provided, ExitAt model world incoming exit)
    (pure : ∀ selected, (fiber.getCont .contA false).answer = .frame selected →
      programOf model world selected (provided.getD (.success value)) = none) :
    RunningStep model Edge world output (fiber.resumeValue interp value provided).1 := by
  have suffix := getCont_suffix model Edge mask world input output fiber .contA false none stack
  cases selected : (fiber.getCont .contA false).answer with
  | empty => rw [FrameFiber.resumeValue_empty interp fiber value provided selected]; trivial
  | deferred cause =>
    rw [FrameFiber.resumeValue_deferred interp fiber value provided cause selected]
    obtain ⟨incoming, path⟩ := suffix
    exact ⟨incoming, model.failure world incoming cause (causes incoming cause), path⟩
  | replacement next =>
    rw [FrameFiber.resumeValue_replacement interp fiber value provided next selected]
    obtain ⟨incoming, path⟩ := suffix
    exact ⟨incoming, replacement next selected incoming, path⟩
  | frame frame =>
    cases actual : frame.armA interp value provided with
    | none => simp only [FrameFiber.resumeValue, selected, actual, RunningStep]
    | some result =>
      obtain ⟨next, pushed⟩ := result
      obtain ⟨events, equation, typed⟩ := resumeValue_selected model interp Edge family mask world input output
        fiber value frame next pushed provided good stack selected supplied (pure frame selected) actual
      rw [equation]
      exact typed

include family mask in
/-- A whole cause return consumes the actual delivered cause and shared selected-arm theorem. -/
theorem resume_cause (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (good : model.cause world input cause) (stack : Path (Edge world) input output fiber.stack)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (causes : ∀ kind reason, model.cause world kind reason)
    (replacement : ∀ next, (fiber.getCont .contE true (some cause)).answer = .replacement next →
      ∀ kind, model.code world kind next)
    (supplied : ∀ incoming delivered, (fiber.getCont .contE true (some cause)).carriedCause = some delivered →
      model.cause world incoming delivered →
      ∀ exit ∈ provided.map (fiber.getCont .contE true (some cause)).deliveredExit, ExitAt model world incoming exit)
    (pure : ∀ selected, (fiber.getCont .contE true (some cause)).answer = .frame selected →
      ∀ delivered, (fiber.getCont .contE true (some cause)).carriedCause = some delivered →
      programOf model world selected
        ((provided.map (fiber.getCont .contE true (some cause)).deliveredExit).getD (.failure delivered)) = none) :
    RunningStep model Edge world output (fiber.resumeCause interp cause provided).1 := by
  have suffix := getCont_suffix model Edge mask world input output fiber .contE true (some cause) stack
  cases selected : (fiber.getCont .contE true (some cause)).answer with
  | empty => rw [FrameFiber.resumeCause_empty interp fiber cause provided selected]; trivial
  | deferred reason =>
    rw [FrameFiber.resumeCause_deferred interp fiber cause reason provided selected]
    obtain ⟨incoming, path⟩ := suffix
    exact ⟨incoming, model.failure world incoming reason (causes incoming reason), path⟩
  | replacement next =>
    rw [FrameFiber.resumeCause_replacement interp fiber cause provided next selected]
    obtain ⟨incoming, path⟩ := suffix
    exact ⟨incoming, replacement next selected incoming, path⟩
  | frame frame =>
    cases actual : frame.armE interp ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
        (provided.map (fiber.getCont .contE true (some cause)).deliveredExit) with
    | none => simp only [FrameFiber.resumeCause, selected, actual, RunningStep]
    | some result =>
      obtain ⟨next, pushed⟩ := result
      obtain ⟨events, equation, typed⟩ := resumeCause_provided_selected model interp Edge family mask world input output
        fiber cause provided frame next pushed good absorbs stack selected supplied (pure frame selected) actual
      rw [equation]
      exact typed
end Effect4.Machine.AnswerFlow.External
