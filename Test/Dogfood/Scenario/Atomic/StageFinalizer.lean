import Test.Dogfood.Scenario.Atomic.StageWorld
import Effect4.Laws.Machine.AnswerFlowContextualFamily
import Effect4.Program.Compile

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
Question: actual request finalizer callbacks retain deposit and positive cleanup evidence.
Reach: existing restore and merge names, every future stage world and every interpreter view.
Consumer: the coupled request saved-frame graph.
Admission of the actual recorded cause remains a command-invariant premise.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageFinalizer
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- A deposited or rejected body cannot return to an undecided stage. -/
theorem body_value_future (before after : StageWorld.World) (future : Future before after)
    (id : Nat) (value : Val) (good : ValueAt before (.body id) value) :
    ValueAt after (.body id) value := by
  cases value
  case bool admitted =>
    cases admitted <;> simp only [ValueAt, Bool.false_eq_true, ↓reduceIte] at good ⊢
    all_goals have step := future.1 id
    all_goals rw [good] at step
    · exact step.rejected
    · exact step.deposited
  all_goals exact good.elim

/-- A typed body failure retains its already-recorded deposit in every future world. -/
theorem body_cause_future (before after : StageWorld.World) (future : Future before after)
    (id : Nat) (cause : CauseV) (good : CauseAt before (.body id) cause) :
    CauseAt after (.body id) cause := by
  intro reason member typed
  have step := future.1 id
  rw [good reason member typed] at step
  exact step.deposited

/-- The captured body exit retains its stage class throughout finalizer execution. -/
def BodyExit (world : StageWorld.World) (id : Nat) : ExitV → Prop
  | .success value => ValueAt world (.body id) value
  | .failure cause => CauseAt world (.body id) cause

theorem body_exit_future (before after : StageWorld.World) (future : Future before after)
    (id : Nat) (exit : ExitV) (good : BodyExit before id exit) : BodyExit after id exit := by
  cases exit with
  | success value => exact body_value_future before after future id value good
  | failure cause => exact body_cause_future before after future id cause good

/-- Only actual recorded causes without typed failures enter request handler discard. -/
def Allowed (_ : StageWorld.World) (pending : Option CauseV) : Prop :=
  ∀ cause ∈ pending, ∀ reason ∈ cause.reasons, reason.tag ≠ .fail

/-- The native restore and merge wrappers retain the captured body exit. -/
inductive Edge (owner : Nat) : StageWorld.World → Kind → Kind → NCode → Prop
  | restore (world : StageWorld.World) (exit : ExitV) (body : NCode)
      (good : BodyExit world owner exit) :
      Edge owner world (.cleanup owner) (.finalized owner) (.onSuccess body (.restore exit))
  | merge (world : StageWorld.World) (exit : ExitV) (body : NCode)
      (good : BodyExit world owner exit) :
      Edge owner world (.note owner) (.cleanup owner) (.onFailure body (.merge exit))

/-- Saved finalizer names retain their captured body exit when the stage world advances. -/
theorem edge_future (before after : StageWorld.World) (future : Future before after)
    (id : Nat) (input output : Kind) (frame : NCode) (held : Edge id before input output frame) :
    Edge id after input output frame := by
  cases held with
  | restore exit body captured =>
    exact .restore after exit body (body_exit_future before after future id exit captured)
  | merge exit body captured =>
    exact .merge after exit body (body_exit_future before after future id exit captured)

variable (model : Model (ν := EffName) (σ := EffThunk) (β := Val)
  (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) StageWorld.World Kind)
variable (futureEq : model.future = Future) (valueEq : model.value = ValueAt) (causeEq : model.cause = CauseAt)

include valueEq causeEq in
/-- Restoring the captured exit consumes the cleanup completion's actual evidence. -/
theorem restore_code (world : StageWorld.World) (id : Nat) (exit : ExitV) (good : BodyExit world id exit)
    (value : Val) (finished : ValueAt world (.cleanup id) value) :
    model.code world (.finalized id) (Prim.ofExit exit) := by
  cases exit with
  | success answer =>
    apply model.success
    rw [valueEq]
    exact restored_value world id answer good
  | failure cause =>
    apply model.failure
    rw [causeEq]
    exact restored_cause world id cause good ⟨rfl, finished.2⟩

include causeEq in
/-- The actual failure merge adds no new typed failure from finalizer execution. -/
theorem merge_code (world : StageWorld.World) (id : Nat) (exit : ExitV) (good : BodyExit world id exit)
    (cause : CauseV) (finished : CauseAt world (.note id) cause) :
    model.code world (.cleanup id) (Prim.ofExit (Exit.restoreAfterFinalizer exit (.failure cause))) := by
  cases exit with
  | success answer =>
    apply model.failure
    rw [causeEq]
    intro reason member typed
    exact False.elim (finished.1 reason member typed)
  | failure original =>
    apply model.failure
    rw [causeEq]
    exact merged_cause world id original cause good finished

include futureEq valueEq causeEq in
/-- Actual native restore and merge callbacks form one admitted saved-frame family. -/
theorem family (id : Nat) (root : NativeEff) (table : RowTable) (view) :
    ContextualSavedFamily model (interpAt root view table).toPrimInterp (Edge id) Allowed := by
  constructor
  · intro world input output frame held nextWorld future value good missing
    cases held with
    | restore => cases missing
    | merge exit body captured => simpa only [valueEq, ValueAt] using good
  · intro world input output frame held nextWorld future cause good missing
    cases held with
    | restore exit body captured => simpa only [causeEq, CauseAt] using good
    | merge => cases missing
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    cases held with
    | restore exit body captured =>
      change some (Prim.ofExit exit, []) = some (next, pushed) at actual
      cases actual
      have forward : Future world nextWorld := by rw [← futureEq]; exact future
      have finished : ValueAt nextWorld (.cleanup id) value := by rw [← valueEq]; exact good
      exact ⟨.finalized id, restore_code model valueEq causeEq nextWorld id exit
        (body_exit_future world nextWorld forward id exit captured) value finished, .nil _⟩
    | merge => cases actual
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    cases held with
    | restore => cases actual
    | merge exit body captured =>
      change some (Prim.ofExit (Exit.restoreAfterFinalizer exit (.failure cause)), []) = some (next, pushed) at actual
      cases actual
      have forward : Future world nextWorld := by rw [← futureEq]; exact future
      have finished : CauseAt nextWorld (.note id) cause := by rw [← causeEq]; exact good
      exact ⟨.cleanup id, merge_code model causeEq nextWorld id exit
        (body_exit_future world nextWorld forward id exit captured) cause finished, .nil _⟩
  · intro world input output frame held nextWorld future exit next good installed
    cases held <;> cases installed
  · intro world input output frame held nextWorld future fiber cause delivered good selected admitted interrupted actual
    cases held with
    | restore => cases selected
    | merge exit body captured =>
      rw [causeEq]
      have finished : CauseAt nextWorld (.note id) cause := by rw [← causeEq]; exact good
      cases pending : fiber.interruptedCause with
      | none =>
        simp only [Prim.ensure, FrameFiber.skippedCause, pending] at actual
        cases actual
        intro reason member typed
        exact False.elim (finished.1 reason member typed)
      | some recorded =>
        have clean := admitted recorded pending
        simp only [Prim.ensure, FrameFiber.skippedCause, pending] at actual
        cases actual
        intro reason member typed
        exact False.elim (Cause.sanitize_clean cause recorded clean reason member typed)

end Test.Dogfood.Scenario.Atomic.StageFinalizer
