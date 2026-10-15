import Test.Dogfood.Proofs.HostTimeoutNumberPhase
import Effect4.Laws.Machine.AnswerFlowProtected
import Test.Dogfood.Proofs.HostTimeoutNumberFinalizers

/-!
Concept: scope-lifetime-finalization R11, with translation-simulation R10.
Question: numeric source contracts retain counted cleanup and permit an uncounted interruption before finalizer installation.
Consumer: the uncounted root phase in both Timeout numeric command producers.
Reach: the actual count prefix, attempt cleanup, form finalizer, and constant yield continuation.
Limit: the producer must retain the phase while the form reads and publishes its log entry.
No equality between the retry cursor and the committed count is assumed here.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutSlots HostTimeoutNumberPhase HostTimeoutNumberCallbacks
open HostTimeoutNumberFinalizers

/-- A phase assertion reads the existing three-cell heap. -/
def At (phase : Phase) (state : Stores) : Prop := state.refs = phase.heap

/-- The completed-form assertion records the actual heap count independently of the source cursor. -/
inductive Kind
  | fresh (phase : Phase)
  | attempt (before entered : Phase) (own : entered.count = entered.cleanups.length + 1)
  | read (phase : Phase)
  | unit (phase : Phase)
  | countUnit (phase : Phase)
  | before (phase : Phase)
  | published (phase : Phase)
  | cleanupExit (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
  | paused (phase : Phase) (incoming : Kind)

/-- Saved numeric phases move from ordinary work through protected cleanup to its returned exit.
Consumer: the authored-finalizer membership contradiction for read and unit runtime permissions. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
def Kind.grade : Kind → Nat
  | .fresh _ => 0
  | .countUnit _ | .before _ => 1
  | .read _ => 2
  | .unit _ => 3
  | .cleanupExit _ _ | .published _ => 4
  | .attempt _ _ _ => 5
  | .paused _ incoming => incoming.grade

/-- A restored success names the selected exit that the actual form log has just published. -/
def ValueAt (state : Stores) : Kind → Val → Prop
  | .fresh phase, _ => At phase state
  | .paused phase _, _ => At phase state
  | .attempt _ entered own, _ => ∃ selected, At (entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)) state
  | .read phase, value => At phase state ∧ value = .nat phase.count
  | .unit phase, value => At phase state ∧ value = .unit
  | .countUnit phase, value => At phase state ∧ value = .unit
  | .before phase, _ => At phase state
  | .cleanupExit phase own, _ => ∃ selected, At (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)) state
  | .published phase, value => ∃ selected, At (phase.form phase.count selected) state ∧ selected = .success value

/-- Every delivered typed failure originates in the selected exit already stored by the form. -/
def TypedFrom (selected : ExitV) (cause : CauseV) : Prop :=
  ∀ reason ∈ cause.reasons, reason.tag = .fail →
    match selected with
    | .success _ => False
    | .failure original => reason ∈ original.reasons

/-- Restoring the selected failure retains each of its actual typed reasons. -/
theorem typedFrom_selected (cause : CauseV) : TypedFrom (.failure cause) cause := by
  intro reason member tag
  exact member

/-- An interruption-only cause introduces no typed reason into any selected exit. -/
theorem typedFrom_clean (selected : ExitV) (cause : CauseV)
    (clean : HostTimeoutNumberFlow.NoTypedFailure cause) : TypedFrom selected cause := by
  intro reason member tag
  exact False.elim (clean reason member tag)

/-- The actual restoring-mask union adds no typed reason from a clean recorded interruption. -/
theorem typedFrom_combine (selected : ExitV) (cause interrupted : CauseV)
    (origin : TypedFrom selected cause) (clean : HostTimeoutNumberFlow.NoTypedFailure interrupted) :
    TypedFrom selected (Cause.combine cause interrupted) := by
  intro reason member tag
  rcases (Cause.mem_combine reason cause interrupted).mp member with before | after
  · exact origin reason before tag
  · exact False.elim (clean reason after tag)

/-- An interruption may replace the delivered cause after the selected exit is already published. -/
def CauseAt (state : Stores) : Kind → CauseV → Prop
  | .paused _ incoming, cause => CauseAt state incoming cause
  | .fresh phase, cause => At phase state ∧ HostTimeoutNumberFlow.NoTypedFailure cause
  | .countUnit phase, cause => At phase state ∧ HostTimeoutNumberFlow.NoTypedFailure cause
  | .attempt before entered own, cause =>
      (∃ selected, At (entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)) state) ∨
        (At before state ∧ HostTimeoutNumberFlow.NoTypedFailure cause)
  | .before phase, _ => At phase state
  | .cleanupExit phase own, _ => ∃ selected, At (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)) state
  | .published phase, cause => ∃ selected, At (phase.form phase.count selected) state ∧
      TypedFrom selected cause
  | _, _ => False

/-- Every phase cause class absorbs the actual clean recorded interruption at a restoring mask. -/
theorem cause_combine (state : Stores) (kind : Kind) (cause interrupted : CauseV)
    (good : CauseAt state kind cause) (clean : HostTimeoutNumberFlow.NoTypedFailure interrupted) :
    CauseAt state kind (Cause.combine cause interrupted) := by
  induction kind with
  | fresh phase => exact ⟨good.1, HostTimeoutNumberFlow.no_typed_combine cause interrupted good.2 clean⟩
  | attempt before entered own =>
      rcases good with cleaned | ⟨heap, quiet⟩
      · exact Or.inl cleaned
      · exact Or.inr ⟨heap, HostTimeoutNumberFlow.no_typed_combine cause interrupted quiet clean⟩
  | read phase => exact False.elim good
  | unit phase => exact False.elim good
  | countUnit phase => exact ⟨good.1, HostTimeoutNumberFlow.no_typed_combine cause interrupted good.2 clean⟩
  | paused phase incoming ih => exact ih good
  | before phase => exact good
  | cleanupExit phase own => exact good
  | published phase =>
      obtain ⟨selected, heap, origin⟩ := good
      exact ⟨selected, heap, typedFrom_combine selected cause interrupted origin clean⟩

/-- Skipping a handler removes typed failures without losing their selected-exit provenance. -/
theorem cause_strip (state : Stores) (kind : Kind) (cause : CauseV)
    (good : CauseAt state kind cause) : CauseAt state kind cause.stripFail := by
  induction kind with
  | fresh phase => exact ⟨good.1, HostTimeoutNumberFlow.no_typed_strip cause⟩
  | attempt before entered own =>
      rcases good with cleaned | ⟨heap, quiet⟩
      · exact Or.inl cleaned
      · exact Or.inr ⟨heap, HostTimeoutNumberFlow.no_typed_strip cause⟩
  | read phase => exact False.elim good
  | unit phase => exact False.elim good
  | countUnit phase => exact ⟨good.1, HostTimeoutNumberFlow.no_typed_strip cause⟩
  | paused phase incoming ih => exact ih good
  | before phase => exact good
  | cleanupExit phase own => exact good
  | published phase =>
      obtain ⟨selected, heap, origin⟩ := good
      exact ⟨selected, heap, typedFrom_clean selected cause.stripFail (HostTimeoutNumberFlow.no_typed_strip cause)⟩

/-- Actual handler sanitization retains phase facts under the recorded interruption premise. -/
theorem cause_sanitize (state : Stores) (kind : Kind) (cause interrupted : CauseV)
    (good : CauseAt state kind cause) (clean : HostTimeoutNumberFlow.NoTypedFailure interrupted) :
    CauseAt state kind (Cause.sanitize cause interrupted) :=
  cause_combine state kind cause.stripFail interrupted (cause_strip state kind cause good) clean

/-- An unrelated typed reason in a combined cause is refused by the selected-exit provenance relation. -/
theorem typedFrom_unrelated (selected cause extra : CauseV) (reason : Reason Err Defect FiberId Ann)
    (member : reason ∈ extra.reasons) (typed : reason.tag = .fail)
    (unrelated : reason ∉ selected.reasons) : ¬ TypedFrom (.failure selected) (Cause.combine cause extra) := by
  intro origin
  exact unrelated (origin reason ((Cause.mem_combine reason cause extra).mpr (Or.inr member)) typed)

/-- The code assertion classifies the existing form source and its saved native restore wrappers. -/
inductive CodeAt : Stores → Kind → NCode → Prop
  | success {state : Stores} (kind : Kind) (value : Val) (good : ValueAt state kind value) : CodeAt state kind (.success value)
  | failure {state : Stores} (kind : Kind) (cause : CauseV) (good : CauseAt state kind cause) : CodeAt state kind (.failure cause)
  | get {state : Stores} (phase : Phase) (heap : At phase state) : CodeAt state (.read phase) (.sync (.op (.refGet ⟨0⟩)))
  | form {state : Stores} (phase : Phase) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val)
      (selected : ExitV) (heap : At phase state) :
      CodeAt state (.unit (phase.form phase.count selected))
        (resolve HostTimeoutSource.program (completedPoint captured fuel delay n previous selected))
  | write {state : Stores} (phase : Phase) (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
      (previous : Val) (selected : ExitV) (heap : At phase state) :
      CodeAt state (.unit (phase.form phase.count selected))
        (resolve HostTimeoutSource.program
          ({completedPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)))
  | cleanup {state : Stores} (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
      (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV)
      (heap : At phase state) :
      CodeAt state (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
        (resolve HostTimeoutSource.program (cleanupPoint captured fuel delay n previous selected))
  | cleanupBound {state : Stores} (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
      (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV)
      (heap : At phase state) :
      CodeAt state (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
        (resolve HostTimeoutSource.program
          ({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)))
  | cleanupWrite {state : Stores} (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
      (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV)
      (heap : At phase state) :
      CodeAt state (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
        (resolve HostTimeoutSource.program
          (({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)).child 0))
  | cleanupReturn {state : Stores} (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
      (selected : ExitV) (body : NCode)
      (first : CodeAt state (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) body) :
      CodeAt state (.cleanupExit phase own) (.onSuccess body (.restore selected))
  | park {state : Stores} (phase : Phase) (kind : ParkKind) (heap : At phase state) :
      CodeAt state (.before phase) (.suspend (.park kind))
  | cancelRace {state : Stores} (phase : Phase) (race : Nat) (heap : At phase state) :
      CodeAt state (.before phase) (.withFiber (.store (.act (.cancelRace race))))
  | maskedCancelRace {state : Stores} (phase : Phase) (race : Nat) (heap : At phase state) :
      CodeAt state (.before phase) (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
  | bind {state : Stores} (input output : Kind) (first : NCode) (name : EffName)
      (head : CodeAt state input first) (ordered : input.grade ≤ output.grade)
      (callback : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ value,
        ValueAt next input value → ∀ view, CodeAt next output ((interpreter view).contA name value))
      (skip : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ cause,
        CauseAt next input cause → CauseAt next output cause) :
      CodeAt state output (.onSuccess first name)
  | pausing {state : Stores} (phase : Phase) (kind : Kind) (priority : Nat) (body : NCode)
      (heap : At phase state) (owned : CodeAt state kind body) :
      CodeAt state kind (.onSuccessConst (.yieldNowWith priority) body)
  | yieldNow {state : Stores} (kind : Kind) (priority : Nat) (good : ValueAt state kind .unit) :
      CodeAt state kind (.yieldNowWith priority)
  | constant {state : Stores} (input output : Kind) (first body : NCode) (head : CodeAt state input first) (ordered : input.grade ≤ output.grade)
      (callback : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ value,
        ValueAt next input value → CodeAt next output body)
      (skip : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ cause,
        CauseAt next input cause → CauseAt next output cause) :
      CodeAt state output (.onSuccessConst first body)
  | attemptReturn {state : Stores} (before entered : Phase) (own : entered.count = entered.cleanups.length + 1)
      (selected : ExitV) (body : NCode)
      (first : CodeAt state (.unit (entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) body) :
      CodeAt state (.attempt before entered own) (.onSuccess body (.restore selected))
  | attemptEntry {state : Stores} (phase : Phase) (n : Fin 4) (cleanups : phase.cleanups.length = phase.count)
      (forms : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val)
      (captured : Point) (fuel delay : Nat) (previous : Val) (heap : At phase state) :
      CodeAt state (.attempt phase (phase.counted n cleanups forms cursor)
        (by change phase.count + 1 = phase.cleanups.length + 1; rw [cleanups]))
        (resolve HostTimeoutSource.program (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous))
  | attemptBody {state : Stores} (phase : Phase) (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val)
      (heap : At phase state) :
      CodeAt state (.before phase)
        (resolve HostTimeoutSource.program
          (((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0).childWith 1 .unit))
  | count {state : Stores} (phase : Phase) (n : Fin 4) (cleanups : phase.cleanups.length = phase.count)
      (forms : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val)
      (captured : Point) (fuel delay : Nat) (previous : Val) (heap : At phase state) :
      CodeAt state (.countUnit (phase.counted n cleanups forms cursor))
        (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm
          (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).env)))
  | countBind {state : Stores} (phase : Phase) (n : Fin 4) (cleanups : phase.cleanups.length = phase.count)
      (forms : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val)
      (captured : Point) (fuel delay : Nat) (previous : Val) (heap : At phase state) :
      CodeAt state (.before (phase.counted n cleanups forms cursor))
        (resolve HostTimeoutSource.program
          ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0))
  | countEntry {state : Stores} (phase : Phase) (n : Fin 4) (cleanups : phase.cleanups.length = phase.count)
      (forms : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val)
      (captured : Point) (fuel delay : Nat) (previous : Val) (heap : At phase state) :
      CodeAt state (.cleanupExit (phase.counted n cleanups forms cursor)
        (by change phase.count + 1 = phase.cleanups.length + 1; rw [cleanups]))
        (resolve HostTimeoutSource.program (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous))
  | merge {state : Stores} (phase : Phase) (exit : ExitV) (body : NCode) (first : CodeAt state (.unit phase) body) :
      CodeAt state (.unit phase) (.onFailure body (.merge exit))
  | restore {state : Stores} (phase : Phase) (selected : ExitV) (body : NCode)
      (first : CodeAt state (.unit (phase.form phase.count selected)) body) :
      CodeAt state (.published phase) (.onSuccess body (.restore selected))

/-- The general form instance shares the actual interpreter and ordered saved-frame relation. -/
def model (view : View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err)
    (δ := Defect) (ι := FiberId) (α := Ann) Stores Kind where
  future := HostTimeoutNumberFlow.Future
  future_refl := fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  future_trans := fun _ _ _ first second => ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩
  value := ValueAt
  cause := CauseAt
  code := CodeAt
  finalizer := fun _ name exit =>
    ((interpreter view).finalizerProgram name exit).map (finalizerCode (interpreter view) exit)
  success := fun _ => CodeAt.success
  failure := fun _ => CodeAt.failure

/-- The count-read callback uses its actual heap number even if the attempt never counted. -/
theorem read_saved (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.read phase)
      (.unit (phase.form phase.count selected))
      (.onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont (completedPoint captured fuel delay n previous selected))) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨heap, equal⟩ := good
    rw [equal, completed_callback]
    exact CodeAt.write phase view captured fuel delay n previous selected heap
  · intro next future cause good
    exact False.elim good

/-- The form's failure wrapper cannot fabricate a failure from its infallible numeric log write. -/
theorem merge_saved (view : View) (state : Stores) (phase : Phase) (exit : ExitV) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.unit phase) (.unit phase)
      (.onFailure body (.merge exit)) := by
  apply AnswerFlow.saved_failure
  · intro next future value good
    exact good
  · intro next future cause good
    exact False.elim good
  · intro next future fiber cause delivered good interrupted skipped
    exact False.elim good

/-- Restoring the selected exit requires the actual completed log entry, not a hypothetical count increment. -/
theorem restore_saved (view : View) (state : Stores) (phase : Phase) (selected : ExitV) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (phase.form phase.count selected)) (.published phase) (.onSuccess body (.restore selected)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    cases selected with
    | success saved => exact CodeAt.success _ saved ⟨.success saved, good.1, rfl⟩
    | failure saved => exact CodeAt.failure _ saved ⟨.failure saved, good.1, typedFrom_selected saved⟩
  · intro next future cause good
    exact False.elim good

/-- The actual native finalizer wrapper publishes and restores the same selected exit. -/
theorem finalizer_code (view : View) (state : Stores) (phase : Phase) (selected : ExitV) (body : NCode)
    (first : CodeAt state (.unit (phase.form phase.count selected)) body) :
    CodeAt state (.published phase) (finalizerCode (interpreter view) selected body) := by
  cases selected with
  | success value => exact CodeAt.restore phase _ body first
  | failure cause => exact CodeAt.restore phase _ _ (CodeAt.merge _ _ body first)

/-- The actual form finalizer consumes any valid numeric phase, including an uncounted race exit. -/
theorem form_saved (view : View) (state : Stores) (phase : Phase)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.before phase) (.published phase) (.onExit body (.fin (formPoint captured fuel delay n previous)) false) := by
  apply AnswerFlow.saved_protected_finalizer
  intro next future exit good
  have heap : At phase next := by cases exit <;> exact good
  refine ⟨finalizerCode (interpreter view) exit (resolve HostTimeoutSource.program
    (completedPoint {captured with completed := view} fuel delay n previous exit)), ?_, ?_⟩
  · change (((interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n previous)) exit).map
      (finalizerCode (interpreter view) exit)) = _
    rw [form_program, Option.map_some]
  · exact finalizer_code view next phase exit _
      (CodeAt.form phase {captured with completed := view} fuel delay n previous exit heap)

/-- The cleanup count callback retains the actual committed count before installing its note binder. -/
theorem cleanup_read_saved (view : View) (state : Stores) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.read phase)
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont (cleanupPoint captured fuel delay n previous selected))) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨heap, equal⟩ := good
    rw [equal]
    have code : (interpreter view).contA (.cont (cleanupPoint captured fuel delay n previous selected)) (.nat phase.count) =
        resolve HostTimeoutSource.program
          ({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)) := by
      kernel_rfl
    rw [code]
    exact CodeAt.cleanupBound phase own view captured fuel delay n previous selected heap
  · intro next future cause good
    exact False.elim good

/-- The cleanup note's saved callback returns unit only at its exact committed post-write phase. -/
theorem cleanup_done_saved (view : View) (state : Stores) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) :
    let point := {cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.onSuccess (resolve HostTimeoutSource.program (point.child 0)) (.cont point)) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨heap, equal⟩ := good
    rw [equal]
    have code : (interpreter view).contA
        (.cont ({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)))
        .unit = .success .unit := by kernel_rfl
    rw [code]
    exact CodeAt.success _ _ ⟨heap, rfl⟩
  · intro next future cause good
    exact False.elim good

/-- The attempt restore requires its own completed cleanup, independently of the completed form column. -/
theorem cleanup_restore_saved (view : View) (state : Stores) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (selected : ExitV) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.cleanupExit phase own) (.onSuccess body (.restore selected)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    cases selected with
    | success saved => exact CodeAt.success _ saved ⟨.success saved, good.1⟩
    | failure saved => exact CodeAt.failure _ saved ⟨.failure saved, good.1⟩
  · intro next future cause good
    exact False.elim good

/-- The actual attempt finalizer restores its captured exit after publishing its numeric cleanup. -/
theorem cleanup_finalizer_code (view : View) (state : Stores) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (selected : ExitV) (body : NCode)
    (first : CodeAt state (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) body) :
    CodeAt state (.cleanupExit phase own) (finalizerCode (interpreter view) selected body) := by
  cases selected with
  | success value => exact CodeAt.cleanupReturn phase own _ body first
  | failure cause => exact CodeAt.cleanupReturn phase own _ _ (CodeAt.merge _ _ body first)

/-- The actual attempt finalizer consumes only its own counted phase and publishes its cleanup. -/
theorem attempt_saved (view : View) (state : Stores) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.before phase) (.cleanupExit phase own)
      (.onExit body (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous)) false) := by
  apply AnswerFlow.saved_protected_finalizer
  intro next future exit good
  have heap : At phase next := by cases exit <;> exact good
  refine ⟨finalizerCode (interpreter view) exit (resolve HostTimeoutSource.program
    (cleanupPoint {captured with completed := view} fuel delay n previous exit)), ?_, ?_⟩
  · change (((interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous)) exit).map
      (finalizerCode (interpreter view) exit)) = _
    rw [attempt_program, Option.map_some]
  · exact cleanup_finalizer_code view next phase own exit _
      (CodeAt.cleanup phase own {captured with completed := view} fuel delay n previous exit heap)

/-- A counted attempt's native restore inhabits the pending-or-cleaned result family. -/
theorem flexible_finalizer_code (view : View) (state : Stores) (before entered : Phase)
    (own : entered.count = entered.cleanups.length + 1) (selected : ExitV) (body : NCode)
    (first : CodeAt state (.unit (entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) body) :
    CodeAt state (.attempt before entered own) (finalizerCode (interpreter view) selected body) := by
  cases selected with
  | success value => exact CodeAt.attemptReturn before entered own _ body first
  | failure cause => exact CodeAt.attemptReturn before entered own _ _ (CodeAt.merge _ _ body first)

/-- The installed attempt finalizer permits the completed cleanup branch of the flexible result family. -/
theorem flexible_attempt_saved (view : View) (state : Stores) (before entered : Phase)
    (own : entered.count = entered.cleanups.length + 1) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.before entered) (.attempt before entered own)
      (.onExit body (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous)) false) := by
  apply AnswerFlow.saved_protected_finalizer
  intro next future exit good
  have heap : At entered next := by cases exit <;> exact good
  refine ⟨finalizerCode (interpreter view) exit (resolve HostTimeoutSource.program
    (cleanupPoint {captured with completed := view} fuel delay n previous exit)), ?_, ?_⟩
  · change (((interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous)) exit).map
      (finalizerCode (interpreter view) exit)) = _
    rw [attempt_program, Option.map_some]
  · exact flexible_finalizer_code view next before entered own exit _
      (CodeAt.cleanup entered own {captured with completed := view} fuel delay n previous exit heap)

/-- A constant continuation shares the existing ordered saved-frame rule. -/
theorem constant_saved (view : View) (state : Stores) (input output : Kind) (first body : NCode)
    (callback : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ value,
      ValueAt next input value → CodeAt next output body)
    (skip : ∀ next, HostTimeoutNumberFlow.Future state next → ∀ cause,
      CauseAt next input cause → CauseAt next output cause) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state input output
      (.onSuccessConst first body) :=
  AnswerFlow.saved_constant (model view) (interpreter view).toPrimInterp state input output first body callback skip

/-- The attempt restore consumes a completed cleanup in the flexible pending-or-cleaned result family. -/
theorem flexible_restore_saved (view : View) (state : Stores) (before entered : Phase)
    (own : entered.count = entered.cleanups.length + 1) (selected : ExitV) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.attempt before entered own) (.onSuccess body (.restore selected)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    cases selected with
    | success saved => exact CodeAt.success _ saved ⟨.success saved, good.1⟩
    | failure saved => exact CodeAt.failure _ saved (Or.inl ⟨.failure saved, good.1⟩)
  · intro next future cause good
    exact False.elim good

/-- The injected pre-entry yield retains the actual count source as its constant continuation. -/
theorem fresh_entry_yield (state : Stores) (phase : Phase) (n : Fin 4)
    (cleanups : phase.cleanups.length = phase.count) (forms : phase.count ≤ phase.exits.length)
    (cursor : phase.count ≤ n.val) (captured : Point) (fuel delay : Nat) (previous : Val)
    (priority : Nat) (heap : At phase state) :
    CodeAt state (.attempt phase (phase.counted n cleanups forms cursor)
      (by change phase.count + 1 = phase.cleanups.length + 1; rw [cleanups]))
      (.onSuccessConst (.yieldNowWith priority)
        (resolve HostTimeoutSource.program (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous))) := by
  apply CodeAt.constant (.fresh phase) _ _ _ (CodeAt.yieldNow (.fresh phase) priority heap) (by dsimp only [Kind.grade]; decide)
  · intro next future value good
    exact CodeAt.attemptEntry phase n cleanups forms cursor captured fuel delay previous good
  · intro next future cause good
    exact Or.inr good

/-- A read-only race restore retains its exact reference phase when the awaited work has returned. -/
theorem race_restore_saved (view : View) (state : Stores) (phase : Phase) (selected : ExitV) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.before phase) (.before phase)
      (.onSuccess body (.store (.restore selected))) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    cases selected with
    | success saved => exact CodeAt.success _ saved good
    | failure cause => exact CodeAt.failure _ cause good
  · intro next future cause good
    exact good

/-- The actual interrupted-race callback retains its cancellation body at the current reference phase. -/
theorem race_cancel_code (view : View) (state : Stores) (phase : Phase) (race token : Nat)
    (owner : FiberId) (cause : CauseV) (heap : At phase state) :
    CodeAt state (.before phase)
      ((interpreter view).cancelThenFail (.withWaiter (.store (.cancelRace race)) owner token) cause) := by
  rw [HostTimeoutNumberFlow.race_cancel_program]
  apply CodeAt.bind (.before phase) (.before phase) _ (.reFail cause) (CodeAt.cancelRace phase race heap) (by dsimp only [Kind.grade]; decide)
  · intro next future value good nextView
    exact CodeAt.failure _ cause good
  · intro next future delivered good
    exact good

/-- The parked race's actual async finalizer uses the same phase for every permitted future heap. -/
theorem race_cancel_saved (view : View) (state : Stores) (phase : Phase)
    (race token : Nat) (owner : FiberId) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.before phase) (.before phase)
      (.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token)) := by
  refine AnswerFlow.SavedAt.mk state (Kind.before phase) (Kind.before phase) _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro next future value good absent
    exact good
  · intro next future cause good absent
    cases absent
  · intro next future value provided code pushed good supplied noProgram arm
    cases arm
  · intro next future cause provided code pushed good supplied noProgram arm
    cases interrupted : cause.hasInterrupts with
    | false =>
      rw [Prim.armE_asyncFinalizer_no_interrupt _ _ cause provided interrupted] at arm
      cases arm
      exact .mk next (Kind.before phase) (Kind.before phase) _ [] (CodeAt.failure _ cause good) (.nil _ _)
    | true =>
      rw [Prim.armE_asyncFinalizer_interrupt _ _ cause provided interrupted] at arm
      cases arm
      exact .mk next (Kind.before phase) (Kind.before phase) _ []
        (race_cancel_code view next phase race token owner cause good) (.nil _ _)
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

/-- The saved count binder requires the post-count phase only when it receives the count update's unit answer. -/
theorem count_saved (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) :
    let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.countUnit phase) (.before phase)
      (.onSuccess (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm point.env))) (.cont (point.child 0))) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨heap, equal⟩ := good
    rw [equal]
    have code : (interpreter view).contA
        (.cont ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0)) .unit =
        resolve HostTimeoutSource.program
          (((HostTimeoutNumberEntry.attemptPoint {captured with completed := view} (fuel + 1) delay n previous).child 0).childWith 1 .unit) := rfl
    rw [code]
    exact CodeAt.attemptBody phase {captured with completed := view} fuel delay n previous heap
  · intro next future cause good
    exact good.1

/-- The count binder installs its post-count callback before the actual write. -/
theorem count_bind_push (view : View) (state : Stores) (phase : Phase) (n : Fin 4)
    (cleanups : phase.cleanups.length = phase.count) (forms : phase.count ≤ phase.exits.length)
    (cursor : phase.count ≤ n.val) (captured : Point) (fuel delay : Nat) (previous : Val)
    (heap : At phase state) (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.before (phase.counted n cleanups forms cursor)) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  have code : resolve HostTimeoutSource.program
      ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0) =
      .onSuccess (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm
        (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).env)))
        (.cont ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).child 0)) := by kernel_rfl
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.countUnit (phase.counted n cleanups forms cursor)) (.before (phase.counted n cleanups forms cursor))
    output fiber _ _ (current.trans code)
    (CodeAt.count phase n cleanups forms cursor captured fuel delay previous heap)
    (count_saved view state (phase.counted n cleanups forms cursor) captured fuel delay n previous) stack

/-- Installing the actual finalizer retains the pre-count heap and types its future committed answer. -/
theorem count_entry_push (view : View) (state : Stores) (phase : Phase) (n : Fin 4)
    (cleanups : phase.cleanups.length = phase.count) (forms : phase.count ≤ phase.exits.length)
    (cursor : phase.count ≤ n.val) (captured : Point) (fuel delay : Nat) (previous : Val)
    (heap : At phase state) (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit (phase.counted n cleanups forms cursor)
        (by change phase.count + 1 = phase.cleanups.length + 1; rw [cleanups])) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous
  let body := resolve HostTimeoutSource.program (point.child 0)
  have own : (phase.counted n cleanups forms cursor).count =
      (phase.counted n cleanups forms cursor).cleanups.length + 1 := by
    change phase.count + 1 = phase.cleanups.length + 1
    rw [cleanups]
  have code : resolve HostTimeoutSource.program point = .onExit body (.fin point) false := by kernel_rfl
  refine ⟨{fiber with current := body, stack := .onExit body (.fin point) false :: fiber.stack},
    [.pushed (.onExit body (.fin point) false)], ?_, ?_⟩
  · simp only [FrameFiber.step, current.trans code]
  · exact ⟨.before (phase.counted n cleanups forms cursor),
      CodeAt.countBind phase n cleanups forms cursor captured fuel delay previous heap,
      .cons (attempt_saved view state (phase.counted n cleanups forms cursor) own captured fuel delay n previous body) stack⟩

/-- The source's completed-log update term remains existing first-order data. -/
def formTerm : Term :=
  match (HostTimeoutNative.performParts [1,1,1,0,0,1,0,0,1,1]).1 with
  | .refUpdateWith term => term
  | _ => .lit .unit

/-- The actual form writer resolves at every count, independently of its captured retry number. -/
theorem write_code (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (previous : Val) (selected : ExitV) (seen : Nat) :
    let point := {completedPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat seen)
    resolve HostTimeoutSource.program point = .sync (.op (.refUpdate ⟨2⟩ formTerm point.env)) := by
  dsimp only
  kernel_rfl

/-- The native log update publishes its selected exit at the count actually read from this phase. -/
theorem write_step (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) :
    let point := {completedPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)
    syncOpStep (.refUpdate ⟨2⟩ formTerm point.env) {state with refs := phase.heap} =
      some ({state with refs := (phase.form phase.count selected).heap}, .unit) := by
  dsimp only
  kernel_rfl

/-- The actual bind push connects its heap count read to the general-phase form writer. -/
theorem form_push (view : View) (state : Stores) (phase : Phase) (captured : Point)
    (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) (heap : At phase state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (completedPoint captured fuel delay n previous selected))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (phase.form phase.count selected)) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.read phase) (.unit (phase.form phase.count selected)) output fiber _ _
    (current.trans (completed_code captured fuel delay n previous selected)) (CodeAt.get phase heap)
    (read_saved view state phase captured fuel delay n previous selected) stack

/-- A native synchronous phase transition shares one actual-store and future-world proof. -/
theorem native_answer (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (before after : Phase)
    (operation : SyncOp) (value : Val) (input output : Kind)
    (heap : At before machine.state) (current : fiber.frame.current = .sync (.op operation))
    (step : syncOpStep operation {machine.state with refs := before.heap} =
      some ({machine.state with refs := after.heap}, value))
    (good : ValueAt {machine.state with refs := after.heap} input value)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      input output fiber.frame.stack) :
    let next := {machine.state with refs := after.heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success value}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success value} := by
  dsimp only
  have unchanged : {machine.state with refs := before.heap} = machine.state := by rw [← heap]
  rw [unchanged] at step
  have future : HostTimeoutNumberFlow.Future machine.state {machine.state with refs := after.heap} := by
    constructor
    · change machine.state.refs.length ≤ 3
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ControlSteps.native_sync_answer HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine fiber yielding operation _ value id (model view) (interpreter view).toPrimInterp input output
    current step future good stack

/-- The real native writer retains cleanup order even when this form owns no counted attempt. -/
theorem native_write (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (phase : Phase)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV)
    (heap : At phase machine.state) (output : Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      ({completedPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (phase.form phase.count selected)) output fiber.frame.stack) :
    let next := {machine.state with refs := (phase.form phase.count selected).heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} :=
  native_answer view machine fiber yielding phase (phase.form phase.count selected) _ .unit (.unit (phase.form phase.count selected)) output heap
    (current.trans (write_code view captured fuel delay n previous selected phase.count))
    (write_step view machine.state phase captured fuel delay n previous selected) ⟨rfl, rfl⟩ stack

/-- The count write commits the next ordered attempt under the source cursor's existing bound. -/
theorem native_count (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (phase : Phase) (n : Fin 4)
    (cleanups : phase.cleanups.length = phase.count) (forms : phase.count ≤ phase.exits.length)
    (cursor : phase.count ≤ n.val) (captured : Point) (fuel delay : Nat) (previous : Val)
    (heap : At phase machine.state) (output : Kind)
    (current : fiber.frame.current = .sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm
      (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous).env)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.countUnit (phase.counted n cleanups forms cursor)) output fiber.frame.stack) :
    let next := {machine.state with refs := (phase.counted n cleanups forms cursor).heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} := by
  apply native_answer view machine fiber yielding phase (phase.counted n cleanups forms cursor)
    _ .unit (.countUnit (phase.counted n cleanups forms cursor)) output heap current _ ⟨rfl, rfl⟩ stack
  kernel_rfl

/-- The actual cleanup writer's term remains existing source data. -/
def cleanupTerm : Term :=
  match (HostTimeoutNative.performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).1 with
  | .refUpdateWith term => term
  | _ => .lit .unit

/-- The actual cleanup note resolves independently of the count's relationship with the retry cursor. -/
theorem cleanup_write_code (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (previous : Val) (selected : ExitV) (seen : Nat) :
    let point := ({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat seen)).child 0
    resolve HostTimeoutSource.program point = .sync (.op (.refUpdate ⟨1⟩ cleanupTerm point.env)) := by
  dsimp only
  kernel_rfl

/-- The real cleanup write closes exactly the current owning attempt's gap. -/
theorem native_cleanup (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (previous : Val) (selected : ExitV) (heap : At phase machine.state) (output : Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      (({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) output fiber.frame.stack) :
    let next := {machine.state with refs := (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)).heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} := by
  let point := ({cleanupPoint captured fuel delay n previous selected with completed := view}.childWith 1 (.nat phase.count)).child 0
  have step : syncOpStep (.refUpdate ⟨1⟩ cleanupTerm point.env) {machine.state with refs := phase.heap} =
      some ({machine.state with refs := (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)).heap}, .unit) := by
    have source := phase.cleanup_source view machine.state fuel delay n previous selected own
    unfold HostTimeoutNumberSteps.sourceStep at source
    have code : resolve HostTimeoutSource.program
        (HostTimeoutNumberSteps.sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous ++
            [reifyExitVal selected, .nat phase.count]) fuel) =
        .sync (.op (.refUpdate ⟨1⟩ cleanupTerm point.env)) := by kernel_rfl
    rw [code] at source
    exact source
  exact native_answer view machine fiber yielding phase
    (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)) _ .unit
    (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected))) output heap
    (current.trans (cleanup_write_code view captured fuel delay n previous selected phase.count)) step ⟨rfl, rfl⟩ stack

end Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow
