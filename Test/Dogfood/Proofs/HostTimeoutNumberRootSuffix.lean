import Test.Dogfood.Proofs.HostTimeoutNumberRootResult
import Test.Dogfood.Proofs.HostTimeoutNumberResult
import Effect4.Laws.Machine.AnswerFlowContextualFamily

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual root encoder and catch retain selected retry provenance through the saved suffix.
Consumer: the coupled root return producer of both Timeout numeric goals.
Reach: actual source callback points and the same popped frame's recorded interruption.
Limit: the source loop continuation and initialized command closure remain open.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootSuffix
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberPhase HostTimeoutNumberRootModel

/-- Contextual discard reads the pending cause from the actual ensured frame. -/
def Allowed (_state : Stores) (recorded : Option CauseV) : Prop :=
  ∀ cause, recorded = some cause → HostTimeoutNumberFlow.NoTypedFailure cause

/-- The source suffix adds actual encoder and catch callbacks to the existing tagged local edges. -/
inductive LocalEdge (state : Stores) : Kind → Kind → NCode → Prop
  | base {input output : Kind} {frame : NCode} (held : HostTimeoutNumberRootModel.LocalEdge state input output frame) :
      LocalEdge state input output frame
  | answer (phase : Phase) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
      LocalEdge state (.numeric (.published phase)) (.retry phase n delay previous)
        (.onSuccess body (.cont (HostTimeoutNumberResult.answerPoint captured fuel delay n previous)))
  | caught (phase : Phase) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
      LocalEdge state (.retry phase n delay previous) (.retry phase n delay previous)
        (.onFailure body (.caughtError (HostTimeoutNumberResult.catchPoint captured fuel delay n previous)))

/-- The actual source catch can skip only with the same frame's clean recorded cause. -/
theorem catch_skipped (state : Stores) (phase : Phase) (fiber : HostTimeoutFrames.NativeFrame)
    (body : NCode) (name : EffName) (cause delivered : CauseV)
    (good : HostTimeoutNumberPhaseFlow.CauseAt state (.published phase) cause)
    (recordedClean : Allowed state fiber.interruptedCause)
    (skipped : FrameFiber.skippedCause .contE (.onFailure body name) fiber (some cause) = some delivered) :
    HostTimeoutNumberPhaseFlow.CauseAt state (.published phase) delivered := by
  cases recorded : fiber.interruptedCause with
  | none =>
      simp only [FrameFiber.skippedCause, recorded] at skipped
      change some cause = some delivered at skipped
      rw [← Option.some.inj skipped]
      exact good
  | some interrupted =>
      have clean := recordedClean interrupted recorded
      have step : FrameFiber.skippedCause .contE (.onFailure body name) fiber (some cause) =
          some (Cause.sanitize cause interrupted) := by
        simp only [FrameFiber.skippedCause, recorded]
        rfl
      rw [step] at skipped
      rw [← Option.some.inj skipped]
      exact HostTimeoutNumberPhaseFlow.cause_sanitize state (.published phase) cause interrupted good clean

/-- The source callbacks share the existing contextual pop producer and retain their selected-exit classes. -/
theorem local_family (view : View) :
    AnswerFlow.ContextualSavedFamily (model view) (interpreter view).toPrimInterp LocalEdge Allowed := by
  have base := HostTimeoutNumberRootModel.local_family view
  constructor
  · intro state input output frame edge next future value good absent
    cases edge with
    | base edge => exact base.skip state input output frame edge next future value good absent
    | answer phase captured fuel delay n previous body => cases absent
    | caught phase captured fuel delay n previous body => exact good
  · intro state input output frame edge next future cause good absent
    cases edge with
    | base edge => exact base.skipCause state input output frame edge next future cause good absent
    | answer phase captured fuel delay n previous body => exact good
    | caught phase captured fuel delay n previous body => cases absent
  · intro state input output frame edge after future value provided next pushed good supplied absent arm
    cases edge with
    | base edge =>
        obtain ⟨middle, code, path⟩ := base.answer state input output frame edge after future value provided next pushed good supplied absent arm
        exact ⟨middle, code, path.map (fun _ _ _ edge => .base edge)⟩
    | answer phase captured fuel delay n previous body =>
        rw [Prim.armA_onSuccess] at arm
        cases arm
        rw [HostTimeoutNumberResult.answer_code]
        obtain ⟨selected, heap, equal⟩ := good
        exact ⟨.retry phase n delay previous, Or.inl ⟨_, rfl, selected, heap, Or.inl ⟨value, equal, rfl⟩⟩, .nil _⟩
    | caught phase captured fuel delay n previous body => cases arm
  · intro state input output frame edge after future cause provided next pushed good supplied absent arm
    cases edge with
    | base edge =>
        obtain ⟨middle, code, path⟩ := base.cause state input output frame edge after future cause provided next pushed good supplied absent arm
        exact ⟨middle, code, path.map (fun _ _ _ edge => .base edge)⟩
    | answer phase captured fuel delay n previous body => cases arm
    | caught phase captured fuel delay n previous body =>
        rw [Prim.armE_onFailure] at arm
        cases arm
        rw [HostTimeoutNumberResult.catch_code]
        cases handled : caughtErrorValue?
            (HostTimeoutSlots.ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
            HostTimeoutSource.retryTest cause with
        | none => exact ⟨.retry phase n delay previous, Or.inr ⟨cause, rfl, good⟩, .nil _⟩
        | some error =>
            obtain ⟨selected, heap, origin⟩ := good
            exact ⟨.retry phase n delay previous,
              Or.inl ⟨_, rfl, selected, heap, Or.inr ⟨cause, error, origin, handled, rfl⟩⟩, .nil _⟩
  · intro state input output frame edge after future exit next good installed
    cases edge with
    | base edge => exact base.program state input output frame edge after future exit next good installed
    | answer phase captured fuel delay n previous body => cases installed
    | caught phase captured fuel delay n previous body => cases installed
  · intro state input output frame edge after future fiber cause delivered good arm admitted interrupted skipped
    cases edge with
    | base edge => exact base.discard state input output frame edge after future fiber cause delivered good arm interrupted skipped
    | answer phase captured fuel delay n previous body => cases arm
    | caught phase captured fuel delay n previous body =>
        exact catch_skipped after phase _ body _ cause delivered good admitted skipped

/-- Numeric callbacks and the contextual source suffix use the coordinator's one embedding composition. -/
abbrev Edge (view : View) := AnswerFlow.EmbeddedEdgeOver
  (fun state : Stores => state) Kind.numeric (fun _ => True) LocalEdge
  (AnswerFlow.SavedAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp)

/-- The combined root family admits only the actual clean recorded cause at handler discard. -/
theorem family (view : View) :
    AnswerFlow.ContextualSavedFamily (model view) (interpreter view).toPrimInterp (Edge view) Allowed :=
  (numeric_embedding view).contextual_family_over (interpreter view).toPrimInterp LocalEdge _ Allowed Allowed
    (by intro state ready recorded admitted; exact admitted) (local_family view)
    (AnswerFlow.SavedFamily.contextual (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp _ Allowed
      (AnswerFlow.saved_family (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp))

/-- Every actual restoring hook has its identity edge in the contextual source suffix. -/
theorem mask_edge (view : View) (state : Stores) (kind : Kind) : Edge view state kind kind (.setInterruptible true) :=
  .saved (.base (.mask kind true))

/-- Existing readonly and form edges retain their tags in the larger source suffix family. -/
theorem lift_edge (view : View) (state : Stores) (input output : Kind) (frame : NCode)
    (edge : HostTimeoutNumberRootModel.Edge view state input output frame) : Edge view state input output frame := by
  cases edge with
  | saved edge => exact .saved (.base edge)
  | mapped ready edge => exact .mapped ready edge

/-- The actual source encoder and catch compose at the returned retry class. -/
theorem encoder_catch_path (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (answerFuel catchFuel delay : Nat) (n : Fin 4) (previous : Val) (answerBody catchBody : NCode) :
    Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) (.retry phase n delay previous)
      [.onSuccess answerBody (.cont (HostTimeoutNumberResult.answerPoint captured answerFuel delay n previous)),
       .onFailure catchBody (.caughtError (HostTimeoutNumberResult.catchPoint captured catchFuel delay n previous))] :=
  .cons (.saved (.answer phase captured answerFuel delay n previous answerBody))
    (.cons (.saved (.caught phase captured catchFuel delay n previous catchBody)) (.nil _))

/-- The actual root control joins its source suffix using the same tagged contextual path. -/
theorem control_path (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (control : HostTimeoutNumberRootControl.RootControl frame suffix) (output : Kind)
    (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix) :
    Effect4.Contracts.Path (Edge view state) (.read phase) output frame.stack := by
  rw [control.stack]
  have front := (HostTimeoutNumberRootModel.read_path view state phase control.front control.saved).map
    (lift_edge view state)
  exact Effect4.Contracts.Path.append
    (Effect4.Contracts.Path.append front
      (.cons (.saved (.base (.form phase control.captured control.fuel control.delay control.cursor control.previous control.body))) (.nil _))) tail

/-- The actual value pop uses the same contextual family without a fabricated discard premise. -/
theorem value_selected (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (control : HostTimeoutNumberRootControl.RootControl frame suffix) (output : Kind)
    (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix)
    (value : Val) (selected : NCode) (heap : HostTimeoutNumberPhaseFlow.At phase state)
    (found : (frame.getCont .contA false).answer = .frame selected) :
    ∃ incoming middle, (model view).value state incoming value ∧ Edge view state incoming middle selected ∧
      Effect4.Contracts.Path (Edge view state) middle output (frame.getCont .contA false).fiber.stack :=
  AnswerFlow.Contextual.getCont_value_selected (model view) (interpreter view).toPrimInterp
    (Edge view) Allowed (family view) (mask_edge view) state (.read phase) output frame value selected heap
    (control_path view state phase frame suffix control output tail) found

/-- The actual root failure pop consumes the recorded cause of the very frame being popped. -/
theorem cause_selected (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (control : HostTimeoutNumberRootControl.RootControl frame suffix) (output : Kind)
    (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix)
    (cause : CauseV) (selected : NCode) (heap : HostTimeoutNumberPhaseFlow.At phase state)
    (recorded : Allowed state frame.interruptedCause)
    (found : (frame.getCont .contE true (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (frame.getCont .contE true (some cause)).carriedCause = some delivered ∧
      (model view).cause state incoming delivered ∧ Edge view state incoming middle selected ∧
      Effect4.Contracts.Path (Edge view state) middle output (frame.getCont .contE true (some cause)).fiber.stack :=
  AnswerFlow.Contextual.getCont_cause_selected (admitted := recorded) (model view) (interpreter view).toPrimInterp
    (Edge view) Allowed (family view) (mask_edge view) state (.read phase) output frame cause selected heap
    (absorbs_recorded view state frame recorded) (control_path view state phase frame suffix control output tail) found

/-- The returned source retry value still declares the exact singleton stored by the form. -/
theorem retry_declared (state : Stores) (phase : Phase) (n : Fin 4) (delay : Nat) (previous value : Val)
    (tag message : String) (annotations : ReasonAnnotations Ann)
    (good : RetryValue state phase n delay previous value)
    (published : HostTimeoutNumberPhaseFlow.At
      (phase.form phase.count (.failure {reasons := [.fail (.tagged tag message) annotations]})) state) :
    HostTimeoutNumberLedger.exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  obtain ⟨selected, heap, success | ⟨cause, error, origin, handled, equalValue⟩⟩ := good
  · have equal := HostTimeoutNumberRootResult.selected_unique phase selected
      (.failure {reasons := [.fail (.tagged tag message) annotations]}) (heap.symm.trans published)
    obtain ⟨body, returned, encoded⟩ := success
    rw [equal] at returned
    cases returned
  · have equal := HostTimeoutNumberRootResult.selected_unique phase selected
      (.failure {reasons := [.fail (.tagged tag message) annotations]}) (heap.symm.trans published)
    rw [equal] at origin
    exact HostTimeoutNumberRootResult.caught_declared n delay previous tag message annotations cause error origin handled

end Test.Dogfood.Proofs.HostTimeoutNumberRootSuffix
