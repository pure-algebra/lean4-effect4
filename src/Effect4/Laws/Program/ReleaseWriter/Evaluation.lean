import Effect4.Laws.Program.ReleaseWriter.Frames
import Effect4.Laws.Program.CodeClosure.StepFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: a frame step retains its write reservation or receives it at the recorded release push.
Reach: actual source-owned frames under the shared direct-release contract.
Consumers: both crews' writer evaluator debit.
The shared FrameWeights laws own the continuation pop accounting.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto


/-- Only the actual selected release-start frame issues a write reservation. -/
def frameIssue (target : Target) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed (.onSuccess _ (.releaseUnder point _ _)) => selected target point.path
  | _ => 0

/-- Saving a success callback either transfers its reservation or records the release start. -/
theorem success_push_bound (target : Target) (body : NCode) (callback : EffName) :
    name target callback ≤ successName target callback + frameIssue target (.pushed (.onSuccess body callback)) := by
  cases callback <;> simp only [successName, frameIssue, name, Nat.add_zero, Nat.zero_add, Nat.le_refl]

/-- Actual writer callbacks instantiate the shared frame-accounting producer. -/
theorem Source.step_inputs {target : Target} {root : NativeEff} (contract : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    CodeClosure.Funding.StepInputs (weights target) (savedSuccess target) (model target)
      (interpAt root view table).toPrimInterp fiber where
  current_eq := funext (current_fold target)
  saved_eq := rfl
  value := fun value provided => contract.resumeValue_bound table view fiber value provided owned
  cause := fun cause provided => contract.resumeCause_bound table view fiber cause provided owned
  suspend := by
    intro thunk selected
    rcases selected with selected | selected
    all_goals have source := owned.1
    all_goals rw [selected] at source
    all_goals have bounded := contract.interp_suspend_bound table view thunk source
    all_goals rw [current_fold] at bounded
    all_goals exact bounded
  iterator := by
    intro callback cursor next pushed selected found
    have source := owned.1
    rw [selected] at source
    have bounded := contract.armA_bound table view (.iterator callback cursor) cursor none next pushed source found
    rw [current_fold] at bounded
    exact bounded
  loop := by
    intro callback cursor _
    have zero := contract.interp_next_zero table view callback cursor
    cases entered : (interpAt root view table).loopEnter callback cursor
    all_goals change (match (interpAt root view table).loopEnter callback cursor with
      | .continue _ body | .finish body => current target body) = 0 at zero
    all_goals rw [entered] at zero
    all_goals dsimp only [CodeClosure.Funding.loopWeight] at *
    all_goals rw [current_fold] at zero
    all_goals exact zero

/-- Every actual frame step spends at most its current and saved note reservations. -/
theorem Source.step_bound {target : Target} {root : NativeEff} (contract : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    Machine.FrameWeights.returned (model target) ((fiber.step (interpAt root view table).toPrimInterp).1) ≤
      frame target fiber + ((fiber.step (interpAt root view table).toPrimInterp).2.map (frameIssue target)).sum := by
  have bounded := CodeClosure.Funding.step_bound (weights target) (savedSuccess target)
    (model target) (interpAt root view table).toPrimInterp fiber
    (contract.step_inputs table view fiber owned) (frameIssue target) (success_push_bound target)
  exact Nat.le_trans (Nat.le_add_right _ _) bounded

end Effect4.Program.ReleaseWriter
