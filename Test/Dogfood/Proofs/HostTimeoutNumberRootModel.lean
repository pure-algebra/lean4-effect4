import Test.Dogfood.Proofs.HostTimeoutNumberRootControl
import Effect4.Laws.Machine.AnswerFlowEmbedding

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual root pop retains readonly control until its source form finalizer starts.
Consumer: the coupled native producer of both Timeout numeric goals.
Reach: the existing numeric model with an additional readonly control class.
Limit: source entry, race membership, and actual pending-cause permission remain explicit.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootModel
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberPhase HostTimeoutNumberRootControl

/-- Numeric computation reuses the phase model; readonly control also retains its actual code shape. -/
inductive Kind
  | read (phase : Phase)
  | numeric (kind : HostTimeoutNumberPhaseFlow.Kind)

/-- The readonly input retains the current exact heap without restricting its delivered value. -/
def ValueAt (state : Stores) : Kind → Val → Prop
  | .read phase, _ => HostTimeoutNumberPhaseFlow.At phase state
  | .numeric kind, value => HostTimeoutNumberPhaseFlow.ValueAt state kind value

/-- The readonly input retains the current exact heap without changing the actual delivered cause. -/
def CauseAt (state : Stores) : Kind → CauseV → Prop
  | .read phase, _ => HostTimeoutNumberPhaseFlow.At phase state
  | .numeric kind, cause => HostTimeoutNumberPhaseFlow.CauseAt state kind cause

/-- The readonly code refinement survives callback selection instead of being forgotten at the pop. -/
def CodeAt (state : Stores) : Kind → NCode → Prop
  | .read phase, code => ReadCode code ∧ HostTimeoutNumberPhaseFlow.At phase state
  | .numeric kind, code => HostTimeoutNumberPhaseFlow.CodeAt state kind code

/-- This model changes proof assertions on existing code and leaves the interpreter unchanged. -/
def model (view : View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Stores Kind where
  future := HostTimeoutNumberFlow.Future
  future_refl := (HostTimeoutNumberPhaseFlow.model view).future_refl
  future_trans := (HostTimeoutNumberPhaseFlow.model view).future_trans
  value := ValueAt
  cause := CauseAt
  code := CodeAt
  finalizer := (HostTimeoutNumberPhaseFlow.model view).finalizer
  success := by
    intro state kind value good
    cases kind with
    | read phase => exact ⟨.success value, good⟩
    | numeric kind => exact HostTimeoutNumberPhaseFlow.CodeAt.success kind value good
  failure := by
    intro state kind cause good
    cases kind with
    | read phase => exact ⟨.failure cause, good⟩
    | numeric kind => exact HostTimeoutNumberPhaseFlow.CodeAt.failure kind cause good

/-- Every existing numeric saved family embeds unchanged into the refined root model. -/
theorem numeric_embedding (view : View) :
    AnswerFlow.FamilyEmbedding (HostTimeoutNumberPhaseFlow.model view) (model view)
      (fun state => state) Kind.numeric (fun _ => True) where
  ready_future := by intros; trivial
  future := by intros; assumption
  value_read := by intros; assumption
  value_write := by intros; assumption
  cause_read := by intros; assumption
  cause_write := by intros; assumption
  code := by intros; assumption
  finalizer := by intros; rfl

/-- Actual readonly saved callbacks retain their control shape at every completed-exit view. -/
theorem read_saved (frame : NCode) (held : ReadSaved frame) (view : View) (state : Stores) (phase : Phase) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (Kind.read phase) (Kind.read phase) frame := by
  cases held with
  | restore body selected =>
      apply AnswerFlow.saved_success
      · intro next future value good
        cases selected with
        | success saved => exact ⟨.success saved, good⟩
        | failure cause => exact ⟨.failure cause, good⟩
      · intro next future cause good
        exact good
  | rethrow body cause =>
      apply AnswerFlow.saved_success
      · intro next future value good
        exact ⟨.failure cause, good⟩
      · intro next future delivered good
        exact good
  | mask flag => exact AnswerFlow.saved_mask (model view) (interpreter view).toPrimInterp state (Kind.read phase) flag
  | constant first body next =>
      apply AnswerFlow.saved_constant
      · intro after future value good
        exact ⟨next, good⟩
      · intro after future cause good
        exact good
  | cancel race token owner =>
      refine AnswerFlow.SavedAt.mk state (Kind.read phase) (Kind.read phase) _ ?_ ?_ ?_ ?_ ?_ ?_
      · intro next future value good absent
        exact good
      · intro next future cause good absent
        cases absent
      · intro next future value provided code pushed good supplied absent arm
        cases arm
      · intro next future cause provided code pushed good supplied absent arm
        cases interrupted : cause.hasInterrupts with
        | false =>
            rw [Prim.armE_asyncFinalizer_no_interrupt _ _ cause provided interrupted] at arm
            cases arm
            exact AnswerFlow.ResultAt.mk next (Kind.read phase) (Kind.read phase) _ []
              ⟨.failure cause, good⟩ (.nil _ _)
        | true =>
            rw [Prim.armE_asyncFinalizer_interrupt _ _ cause provided interrupted] at arm
            cases arm
            rw [HostTimeoutNumberFlow.race_cancel_program]
            exact AnswerFlow.ResultAt.mk next (Kind.read phase) (Kind.read phase) _ []
              ⟨.rethrow _ cause (.cancel race), good⟩ (.nil _ _)
      · intro next future exit code good installed
        cases installed
      · intro next future fiber cause delivered good arm interrupted skipped
        have quiet : ((Prim.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token)).ensure fiber).1.interrupted = false := by
          cases flag : fiber.interruptible with
          | false =>
              rw [Prim.ensure_asyncFinalizer_already_masked _ fiber flag]
              change (fiber.interruptible && fiber.interruptedCause.isSome) = false
              rw [flag]
              rfl
          | true =>
              rw [Prim.ensure_asyncFinalizer_masks _ fiber flag]
              rfl
        rw [quiet] at interrupted
        cases interrupted

/-- The actual protected form callback is precisely the boundary into the existing numeric model. -/
theorem form_saved (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (Kind.read phase)
      (.numeric (.published phase))
      (.onExit body (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false) := by
  apply AnswerFlow.saved_protected_finalizer
  intro next future exit good
  have heap : HostTimeoutNumberPhaseFlow.At phase next := by cases exit <;> exact good
  refine ⟨finalizerCode (interpreter view) exit (resolve HostTimeoutSource.program
    (HostTimeoutNumberCallbacks.completedPoint {captured with completed := view} fuel delay n previous exit)), ?_, ?_⟩
  · change (((interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) exit).map
        (finalizerCode (interpreter view) exit)) = _
    rw [HostTimeoutNumberFinalizers.form_program, Option.map_some]
  · exact HostTimeoutNumberPhaseFlow.finalizer_code view next phase exit _
      (HostTimeoutNumberPhaseFlow.CodeAt.form phase {captured with completed := view} fuel delay n previous exit heap)

/-- A local edge retains its actual readonly frame or source form-finalizer identity. -/
inductive LocalEdge (_state : Stores) : Kind → Kind → NCode → Prop
  | read (phase : Phase) (frame : NCode) (held : ReadSaved frame) :
      LocalEdge _state (.read phase) (.read phase) frame
  | form (phase : Phase) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
      LocalEdge _state (.read phase) (.numeric (.published phase))
        (.onExit body (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false)

/-- Every tagged local edge has its semantic contract at each actual interpreter view. -/
theorem LocalEdge.contract (state : Stores) (input output : Kind) (frame : NCode)
    (edge : LocalEdge state input output frame) (view : View) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state input output frame := by
  cases edge with
  | read phase frame held => exact read_saved frame held view state phase
  | form phase captured fuel delay n previous body => exact form_saved view state phase captured fuel delay n previous body

/-- Local value callbacks push no recursive frame; their existing suffix remains the shared path. -/
theorem LocalEdge.value_empty (state : Stores) (input output : Kind) (frame : NCode)
    (edge : LocalEdge state input output frame) (view : View) (value : Val) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (arm : frame.armA (interpreter view).toPrimInterp value provided = some (next, pushed)) : pushed = [] := by
  cases edge with
  | read phase frame held =>
      cases held <;> simp only [Prim.armA] at arm
      all_goals cases arm <;> rfl
  | form phase captured fuel delay n previous body =>
      simp only [Prim.armA] at arm
      cases arm
      rfl

/-- Local cause callbacks push no recursive frame, including actual race cancellation callbacks. -/
theorem LocalEdge.cause_empty (state : Stores) (input output : Kind) (frame : NCode)
    (edge : LocalEdge state input output frame) (view : View) (cause : CauseV) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (arm : frame.armE (interpreter view).toPrimInterp cause provided = some (next, pushed)) : pushed = [] := by
  cases edge with
  | read phase frame held =>
      cases held <;> simp only [Prim.armE] at arm
      all_goals cases arm <;> rfl
  | form phase captured fuel delay n previous body =>
      simp only [Prim.armE] at arm
      cases arm
      rfl

/-- The tagged local family consumes existing saved contracts without another continuation-pop induction. -/
theorem local_family (view : View) : AnswerFlow.SavedFamily (model view)
    (interpreter view).toPrimInterp LocalEdge := by
  have semantic := AnswerFlow.saved_family (model view) (interpreter view).toPrimInterp
  constructor
  · intro state input output frame edge next future value good absent
    exact semantic.skip state input output frame (LocalEdge.contract state input output frame edge view)
      next future value good absent
  · intro state input output frame edge next future cause good absent
    exact semantic.skipCause state input output frame (LocalEdge.contract state input output frame edge view)
      next future cause good absent
  · intro state input output frame edge after future value provided next pushed good supplied absent arm
    have empty := LocalEdge.value_empty state input output frame edge view value provided next pushed arm
    subst pushed
    obtain ⟨middle, code, path⟩ := semantic.answer state input output frame
      (LocalEdge.contract state input output frame edge view) after future value provided next [] good supplied absent arm
    cases path
    exact ⟨output, code, .nil output⟩
  · intro state input output frame edge after future cause provided next pushed good supplied absent arm
    have empty := LocalEdge.cause_empty state input output frame edge view cause provided next pushed arm
    subst pushed
    obtain ⟨middle, code, path⟩ := semantic.cause state input output frame
      (LocalEdge.contract state input output frame edge view) after future cause provided next [] good supplied absent arm
    cases path
    exact ⟨output, code, .nil output⟩
  · intro state input output frame edge after future exit next good installed
    exact semantic.program state input output frame (LocalEdge.contract state input output frame edge view)
      after future exit next good installed
  · intro state input output frame edge after future fiber cause delivered good arm interrupted skipped
    exact semantic.discard state input output frame (LocalEdge.contract state input output frame edge view)
      after future fiber cause delivered good arm interrupted skipped

/-- Existing numeric edges and tagged local control edges share the coordinator's one embedding producer. -/
abbrev Edge (view : View) := AnswerFlow.EmbeddedEdgeOver
  (fun state : Stores => state) Kind.numeric (fun _ => True) LocalEdge
  (AnswerFlow.SavedAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp)

/-- The actual shared pop reads one family with readonly and numeric callback endpoints. -/
theorem family (view : View) : AnswerFlow.SavedFamily (model view) (interpreter view).toPrimInterp (Edge view) :=
  (numeric_embedding view).family_over (interpreter view).toPrimInterp LocalEdge _
    (local_family view) (AnswerFlow.saved_family (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp)

/-- Actual root cause transport reads the recorded interruption from the same frame being popped. -/
theorem absorbs_recorded (view : View) (state : Stores) (fiber : HostTimeoutFrames.NativeFrame)
    (recorded : ∀ cause, fiber.interruptedCause = some cause → HostTimeoutNumberFlow.NoTypedFailure cause) :
    AnswerFlow.External.AbsorbsInterrupt (model view) state fiber.interruptedCause := by
  intro interrupted present kind cause good
  cases kind with
  | read phase => exact good
  | numeric kind => exact HostTimeoutNumberPhaseFlow.cause_combine state kind cause interrupted good (recorded interrupted present)

/-- A restoring hook has an identity edge at both readonly and numeric classes. -/
theorem mask_edge (view : View) (state : Stores) (kind : Kind) : Edge view state kind kind (.setInterruptible true) := by
  cases kind with
  | read phase => exact .saved (.read phase _ (.mask true))
  | numeric kind =>
      exact .mapped True.intro
        (AnswerFlow.saved_mask (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp state kind true)

/-- The actual saved readonly prefix becomes a path in the tagged family. -/
theorem read_path (view : View) (state : Stores) (phase : Phase) (front : List NCode)
    (held : ∀ frame ∈ front, ReadSaved frame) :
    Effect4.Contracts.Path (Edge view state) (.read phase) (.read phase) front := by
  induction front with
  | nil => exact .nil _
  | cons head tail ih =>
      exact .cons (.saved (.read phase head (held head (List.mem_cons_self ..))))
        (ih (fun frame member => held frame (List.mem_cons_of_mem head member)))

/-- The root's exact source form boundary joins its actual numeric continuation suffix. -/
theorem control_path (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) (control : RootControl frame suffix)
    (output : Kind) (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix) :
    Effect4.Contracts.Path (Edge view state) (.read phase) output frame.stack := by
  rw [control.stack]
  exact Effect4.Contracts.Path.append
    (Effect4.Contracts.Path.append (read_path view state phase control.front control.saved)
      (.cons (.saved (.form phase control.captured control.fuel control.delay control.cursor control.previous control.body)) (.nil _))) tail

/-- The actual root value pop retains its tagged selected callback and exact remaining suffix. -/
theorem value_selected (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) (control : RootControl frame suffix)
    (output : Kind) (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix)
    (value : Val) (selected : NCode) (heap : HostTimeoutNumberPhaseFlow.At phase state)
    (found : (frame.getCont .contA false).answer = .frame selected) :
    ∃ incoming middle, (model view).value state incoming value ∧ Edge view state incoming middle selected ∧
      Effect4.Contracts.Path (Edge view state) middle output (frame.getCont .contA false).fiber.stack :=
  AnswerFlow.External.getCont_value_selected (model view) (interpreter view).toPrimInterp (Edge view)
    (family view) (mask_edge view) state (.read phase) output frame value selected heap
    (control_path view state phase frame suffix control output tail) found

/-- The actual root cause pop retains provenance through recorded interruptions and its tagged selected callback. -/
theorem cause_selected (view : View) (state : Stores) (phase : Phase)
    (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) (control : RootControl frame suffix)
    (output : Kind) (tail : Effect4.Contracts.Path (Edge view state) (.numeric (.published phase)) output suffix)
    (cause : CauseV) (selected : NCode) (heap : HostTimeoutNumberPhaseFlow.At phase state)
    (recorded : ∀ pending, frame.interruptedCause = some pending → HostTimeoutNumberFlow.NoTypedFailure pending)
    (found : (frame.getCont .contE true (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (frame.getCont .contE true (some cause)).carriedCause = some delivered ∧
      (model view).cause state incoming delivered ∧ Edge view state incoming middle selected ∧
      Effect4.Contracts.Path (Edge view state) middle output (frame.getCont .contE true (some cause)).fiber.stack :=
  AnswerFlow.External.getCont_cause_selected (model view) (interpreter view).toPrimInterp (Edge view)
    (family view) (mask_edge view) state (.read phase) output frame cause selected heap
    (absorbs_recorded view state frame recorded) (control_path view state phase frame suffix control output tail) found

end Test.Dogfood.Proofs.HostTimeoutNumberRootModel
