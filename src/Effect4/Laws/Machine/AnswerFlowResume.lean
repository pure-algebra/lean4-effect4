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
/-- An actual replacing hook is the restoring mask and returns its actual recorded cause. -/
theorem ensure_replacement_recorded (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (next : Prim ν σ β ε δ ι α)
    (found : (frame.ensure fiber).2 = some next) :
    ∃ cause, frame = .setInterruptible true ∧ fiber.interruptedCause = some cause ∧ next = .failure cause := by
  fun_cases Prim.ensure frame fiber
  all_goals aesop (rule_sets := [Effect4.Fibers]) (add norm simp [Prim.ensure])

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Every replacement emitted by an existing mask hook is an actual failure primitive. -/
theorem ensure_replacement_failure (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (next : Prim ν σ β ε δ ι α)
    (found : (frame.ensure fiber).2 = some next) : ∃ cause, next = .failure cause := by
  obtain ⟨cause, mask, recorded, failure⟩ := ensure_replacement_recorded frame fiber next found
  exact ⟨cause, failure⟩

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

/-- A replacement retains its actual original hook or the actual hook-drain site.
Consumer: Timeout's numeric restoring-mask permission; the old failure reader follows below. -/
def ReplacementOrigin (Input : Kind → Prop) (world : World) (output : Kind)
    (demand : Arm) (skip : Bool) (recorded : Option (Cause ε δ ι α))
    (next : Prim ν σ β ε δ ι α) (returned : List (Prim ν σ β ε δ ι α)) : Prop :=
  (∃ input middle head rest, ∃ scratch : FrameFiber ν σ β ε δ ι α,
    Edge world input middle head ∧ Path (Edge world) middle output rest ∧ Input input ∧
    scratch.stack = [] ∧ scratch.interruptedCause = recorded ∧
    head.answerOf demand (head.ensure scratch).2 = some (.replacement next) ∧
    returned = (head.ensure scratch).1.stack ++ rest) ∨
  (∃ input middle head rest, ∃ scratch : FrameFiber ν σ β ε δ ι α, ∃ before after,
    Edge world input middle head ∧ Path (Edge world) middle output rest ∧ Input input ∧
    scratch.stack = [] ∧ scratch.interruptedCause = recorded ∧
    PopTrace.Passes demand skip head scratch before after ∧
    (FrameFiber.passPushed demand skip (head.ensure scratch).1 after).answer = .replacement next ∧
    returned = (FrameFiber.passPushed demand skip (head.ensure scratch).1 after).fiber.stack ++ rest)

/-- The nonrecursive hook drain retains the actual recorded cause. -/
theorem passPushed_recorded (demand : Arm) (skip : Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) :
    (FrameFiber.passPushed demand skip fiber cause).fiber.interruptedCause = fiber.interruptedCause := by
  rw [FrameFiber.passPushed_fiber_cause]
  cases stack : fiber.stack with
  | nil => rw [FrameFiber.passPushed_nil _ _ _ stack]
  | cons head rest =>
    rw [FrameFiber.passPushed_fiber _ _ _ head rest stack, Contextual.ensure_recorded]

/-- One actual pop producer retains incoming data and the exact replacement site.
The transport premise concerns only original frames that the actual pop passes. -/
theorem popFrom_replacement_origin (Input : Kind → Prop) (world : World) (demand : Arm) (skip : Bool)
    (transport : ∀ input middle head scratch before after,
      Edge world input middle head → PopTrace.Passes demand skip head scratch before after →
      Input input → Input middle)
    (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (carried recorded : Option (Cause ε δ ι α)) (stack : Path (Edge world) input output frames)
    (empty : fiber.stack = []) (same : fiber.interruptedCause = recorded) (good : Input input)
    (next : Prim ν σ β ε δ ι α)
    (found : (FrameFiber.popFrom demand skip frames fiber carried).answer = .replacement next) :
    ReplacementOrigin Edge Input world output demand skip recorded next
      (FrameFiber.popFrom demand skip frames fiber carried).fiber.stack := by
  have family : PopTrace.Family demand skip (Edge world)
      (fun fiber => fiber.stack = [] ∧ fiber.interruptedCause = recorded)
      (fun input output _ pop => Input input → pop.answer = .replacement next →
        ReplacementOrigin Edge Input world output demand skip recorded next pop.fiber.stack) := by
    constructor
    · intro kind fiber cause scratch good found
      cases found
    · intro input middle output head tail fiber cause answer callback path scratch chosen kept good found
      cases found
      exact .inl ⟨input, middle, head, tail, fiber, callback, path, good, scratch.1, scratch.2, chosen, rfl⟩
    · intro input middle head fiber after callback scratch
      exact ⟨(FrameFiber.passPushed_fiber_cause demand skip (head.ensure fiber).1 after) ▸
        PopTrace.drain_empty demand skip head fiber scratch.1,
        (passPushed_recorded demand skip (head.ensure fiber).1 after).trans
          ((Contextual.ensure_recorded head fiber).trans scratch.2)⟩
    · intro input middle output head tail fiber before after tailPop callback path scratch passed drained nextProof good found
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      exact nextProof (transport input middle head fiber before after callback passed good) found
    · intro input middle output head tail fiber before after tailPop callback path scratch passed answered good found
      unfold FrameFiber.passOn FrameFiber.joinPushed at found ⊢
      split at found
      · rename_i drained
        exact (answered drained).elim
      · rename_i answer selected
        exact .inr ⟨input, middle, head, tail, fiber, before, after,
          callback, path, good, scratch.1, scratch.2, passed, found, rfl⟩
  exact family.popFrom input output frames fiber carried stack ⟨empty, same⟩ good found

/-- Actual fused pops replace code only with a represented failure from a mask hook. -/
theorem popFrom_replacement_failure (world : World) (input output : Kind) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (recorded : Option (Cause ε δ ι α)) (stack : Path (Edge world) input output frames)
    (empty : fiber.stack = []) (next : Prim ν σ β ε δ ι α)
    (found : (FrameFiber.popFrom demand skip frames fiber recorded).answer = .replacement next) :
    ∃ cause, next = .failure cause := by
  have origin := popFrom_replacement_origin Edge (fun _ => True) world demand skip
    (fun _ _ _ _ _ _ _ _ good => good) input output frames fiber recorded
    fiber.interruptedCause stack empty rfl trivial next found
  rcases origin with ⟨input, middle, head, rest, scratch, callback, path, good, empty, same, actual, suffix⟩ |
    ⟨input, middle, head, rest, scratch, before, after, callback, path, good, empty, same, passed, actual, suffix⟩
  · exact answer_replacement_failure head scratch demand next actual
  · exact drain_replacement_failure _ demand skip after next actual

/-- Actual value lookup retains the incoming value class and recorded cause at its replacement site.
Consumer: numeric read and unit classes do not need a fabricated global cause premise. -/
theorem getCont_value_replacement_origin
    (interp : PrimInterp ν σ β ε δ ι α)
    (Allowed : World → Option (Cause ε δ ι α) → Prop)
    (family : ContextualSavedFamily model interp Edge Allowed)
    (world : World) (input output : Kind) (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (good : model.value world input value) (stack : Path (Edge world) input output fiber.stack)
    (next : Prim ν σ β ε δ ι α)
    (found : (fiber.getCont .contA false).answer = .replacement next) :
    ReplacementOrigin Edge (fun kind => model.value world kind value) world output .contA false
      fiber.interruptedCause next (fiber.getCont .contA false).fiber.stack := by
  have transport : ∀ input middle head scratch before after,
      Edge world input middle head → PopTrace.Passes .contA false head scratch before after →
      model.value world input value → model.value world middle value := by
    intro input middle head scratch before after callback passed good
    have missing : head.hasArm .contA = false := by
      rcases passed with ⟨absent, same⟩ | ⟨answer, selected, skipped, same⟩
      · exact PopTrace.answer_missing head .contA _ absent
      · cases skipped
    exact family.skip world input middle head callback world (model.future_refl world) value good missing
  unfold FrameFiber.getCont at found ⊢
  split at found
  · cases found
  · rename_i normal
    rw [if_neg normal]
    exact popFrom_replacement_origin Edge (fun kind => model.value world kind value) world .contA false
      transport input output fiber.stack {fiber with stack := [], deferredInterrupt := false}
      none fiber.interruptedCause stack rfl rfl good next found

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A real async finalizer lacks the value arm but still inserts a mask.
Control: replacement provenance must retain actual hook drains. -/
theorem asyncFinalizer_value_mask (name : ν) (fiber : FrameFiber ν σ β ε δ ι α)
    (interruptible : fiber.interruptible = true) :
    (Prim.asyncFinalizer name : Prim ν σ β ε δ ι α).hasArm .contA = false ∧
      ((Prim.asyncFinalizer name).ensure fiber).1.stack = .setInterruptible true :: fiber.stack := by
  constructor
  · rfl
  · simp only [Prim.ensure, interruptible, ↓reduceIte]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A replacement answer is exactly the program returned by its actual ensure hook. -/
theorem answer_replacement_hook (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (next : Prim ν σ β ε δ ι α)
    (found : frame.answerOf demand (frame.ensure fiber).2 = some (.replacement next)) :
    (frame.ensure fiber).2 = some next := by
  cases actual : (frame.ensure fiber).2 with
  | none =>
    simp only [actual, Prim.answerOf] at found
    split at found <;> cases found
  | some program =>
    simp only [actual, Prim.answerOf_replacement] at found
    cases found
    rfl

/-- The actual value replacement identifies its original typed edge and unchanged recorded cause.
An actual hook-generated mask has the middle class reached by the passed original frame. -/
theorem getCont_value_replacement_hooked
    (mask : Contextual.HookMask Edge)
    (interp : PrimInterp ν σ β ε δ ι α)
    (Allowed : World → Option (Cause ε δ ι α) → Prop)
    (family : ContextualSavedFamily model interp Edge Allowed)
    (world : World) (input output : Kind) (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (good : model.value world input value) (stack : Path (Edge world) input output fiber.stack)
    (next : Prim ν σ β ε δ ι α)
    (found : (fiber.getCont .contA false).answer = .replacement next) :
    ∃ incoming middle head rest, ∃ scratch : FrameFiber ν σ β ε δ ι α,
      Edge world incoming middle head ∧ Path (Edge world) middle output rest ∧
      model.value world incoming value ∧ scratch.stack = [] ∧
      scratch.interruptedCause = fiber.interruptedCause ∧ (head.ensure scratch).2 = some next ∧
      (fiber.getCont .contA false).fiber.stack = (head.ensure scratch).1.stack ++ rest := by
  have origin := getCont_value_replacement_origin model Edge interp Allowed family world input output
    fiber value good stack next found
  rcases origin with ⟨incoming, middle, head, rest, scratch, callback, path, good, empty, same, actual, suffix⟩ |
    ⟨incoming, middle, head, rest, scratch, before, after, callback, path, good, empty, same, passed, actual, suffix⟩
  · exact ⟨incoming, middle, head, rest, scratch, callback, path, good, empty, same,
      answer_replacement_hook head scratch .contA next actual, suffix⟩
  · have missing : head.hasArm .contA = false := by
      rcases passed with ⟨absent, equal⟩ | ⟨answer, selected, skipped, equal⟩
      · exact PopTrace.answer_missing head .contA _ absent
      · cases skipped
    have middleGood := family.skip world incoming middle head callback world (model.future_refl world)
      value good missing
    rcases FrameFiber.ensure_stack_cases head scratch with kept | ⟨pushed, wasInterruptible, nowMasked⟩
    · rw [FrameFiber.passPushed_answer_cause,
        FrameFiber.passPushed_nil _ _ _ (kept.trans empty)] at actual
      cases actual
    · have pushedOne : (head.ensure scratch).1.stack = [.setInterruptible true] := by rw [pushed, empty]
      rw [FrameFiber.passPushed_answer_cause,
        FrameFiber.passPushed_answer _ _ _ (.setInterruptible true) [] pushedOne] at actual
      cases selected : Prim.answerOf (.setInterruptible true) .contA
          ((Prim.setInterruptible true).ensure {(head.ensure scratch).1 with stack := []}).2 with
      | none => rw [selected] at actual; cases actual
      | some answer =>
        rw [selected] at actual
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at actual
        cases actual
        refine ⟨middle, middle, .setInterruptible true,
          rest, {(head.ensure scratch).1 with stack := []},
          mask world incoming middle head callback scratch pushed, path, middleGood,
          rfl, (Contextual.ensure_recorded head scratch).trans same,
          answer_replacement_hook _ _ .contA next selected, ?_⟩
        rw [FrameFiber.passPushed_fiber_cause,
          FrameFiber.passPushed_fiber _ _ _ (.setInterruptible true) [] pushedOne] at suffix
        exact suffix


/-- The earlier unconditional mask reader specializes the actual-edge replacement producer. -/
abbrev getCont_value_replacement_selected
    (mask : ∀ world kind, Edge world kind kind (.setInterruptible true)) :=
  getCont_value_replacement_hooked model Edge (Contextual.unconditional_hook_mask Edge mask)

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
