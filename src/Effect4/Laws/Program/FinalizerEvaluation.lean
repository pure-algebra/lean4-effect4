import Effect4.Laws.Program.FinalizerFunding
import Effect4.Laws.Program.CodeClosure.StepFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: primitive source accounting serves `once_placed_outside_census`.
Consumer: native evaluator and whole-command source funding.
The generated source weights and actual callback bounds instantiate one frame producer.
Registration consumes a source reservation; release start returns its captured descendant reservation.
This step law establishes no complete history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- The finalizer source consumes only the common registration constructor slots. -/
theorem consumed_slots (q : List Nat) :
    consumedFrame q = CodeClosure.Events.event (successPush q) (exitPush q) := by
  funext event
  cases event
  case pushed code => cases code <;> rfl
  all_goals rfl

/-- Saving a unary success callback transfers only its existing or recorded reservation. -/
theorem success_saved_le (q : List Nat) (body : NCode) (callback : EffName) :
    savedSuccess q (name q) callback ≤ name q callback + producedFrame q (.pushed (.onSuccess body callback)) := by
  cases callback <;> simp only [savedSuccess, name, producedFrame, Nat.add_zero, Nat.zero_add, Nat.le_refl]

/-- Actual callback invocation supplies the shared frame-accounting producer. -/
theorem step_inputs (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (fiber : SourceFrame) (held : FrameAt q fiber) :
    CodeClosure.Funding.StepInputs (nativeWeights root q) (savedSuccess q (name q))
      (frameModel root q) (interpAt root view table).toPrimInterp fiber where
  current_eq := rfl
  saved_eq := rfl
  value := fun value provided => resumeValue_le root q view table placed fiber value provided held
  cause := fun cause provided => resumeCause_le root q view table placed fiber cause provided held
  suspend := by
    intro thunk selected
    rcases selected with selected | selected
    all_goals have owned := held.1
    all_goals rw [selected] at owned
    all_goals exact (interp_suspend root q view table thunk placed owned).2
  iterator := by
    intro callback cursor next pushed selected evaluated
    have owned := held.1
    rw [selected] at owned
    exact armA_le root q view table placed (.iterator callback cursor) cursor none next pushed owned evaluated
  loop := by
    intro callback cursor selected
    have owned := held.1
    rw [selected] at owned
    exact (interp_loop_enter root q view table callback cursor placed (ordinary_name q callback owned)).2

/-- Every actual frame step spends its source reservation or transfers existing release custody. -/
theorem step_bound (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (fiber : SourceFrame) (held : FrameAt q fiber) :
    FrameWeights.returned (frameModel root q) ((fiber.step (interpAt root view table).toPrimInterp).1) +
      (((fiber.step (interpAt root view table).toPrimInterp).2).map (consumedFrame q)).sum ≤
      frame root q fiber + (((fiber.step (interpAt root view table).toPrimInterp).2).map (producedFrame q)).sum := by
  rw [consumed_slots]
  exact CodeClosure.Funding.step_bound (nativeWeights root q) (savedSuccess q (name q))
    (frameModel root q) (interpAt root view table).toPrimInterp fiber
    (step_inputs root q view table placed fiber held) (producedFrame q) (success_saved_le q)

end Effect4.Program.FinalizerSource
