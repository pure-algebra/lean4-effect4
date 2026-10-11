import Test.Dogfood.Scenario.Timeout
import Effect4.Laws.Auto.KernelRfl

/-! The original reply-based timeout contract is stronger than first-exit selection.
These retained kernel-checked scripts serve the amended R10 retry claim as red controls.
The complete returned form result is distinct from reply application.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.TimeoutCounterexample
open Effect4 Effect4.Machine Test.Dogfood.Scenario
open Test.Dogfood.Scenario.Timeout Effect4.Laws.Auto

/-- The host applies a success, then the attempt yields before its exit observer runs. -/
def yieldedSuccess : List Move := script [parked,
  [.control (.yieldVerdict ⟨1⟩ true), .receive http (ok body1), .apply http,
    .tick 2000, .tick 100, .tick 200, .flush, .hold http]]

/-- A nonretryable applied failure can yield at the same cut and lose to the timer. -/
def yieldedFailure : List Move := script [parked,
  [.control (.yieldVerdict ⟨1⟩ true), .receive http (failed "BadRequest" "bad"), .apply http,
    .tick 2000, .tick 100, .tick 200, .flush, .hold http]]

theorem yieldedSuccess_plain : yieldedSuccess.all Move.plain = true := by decide
theorem yieldedFailure_plain : yieldedFailure.all Move.plain = true := by decide

/-- Both scripts refute the old claim while reading the new returned-outcome contract. -/
theorem yieldedSuccess_observation :
    ((Effect4.Api.Author.build fetch).toOption.map fun b =>
      let o := observe (Test.Dogfood.Scenario.play (opened b) yieldedSuccess)
      (o.replyBasedRetriesDeclared, o.retriesDeclared, o.attempts,
        o.forms.map fun result => (result.attempt, result.selected, result.role, result.exit))) =
      some (false, true, 2, [(1, some ⟨2⟩, .timer, .failure (Cause.fail (.tagged "Timeout" "2000 ms")))]) := by kernel_rfl

theorem yieldedFailure_observation :
    ((Effect4.Api.Author.build fetch).toOption.map fun b =>
      let o := observe (Test.Dogfood.Scenario.play (opened b) yieldedFailure)
      (o.replyBasedRetriesDeclared, o.retriesDeclared, o.attempts,
        o.forms.map fun result => (result.attempt, result.selected, result.role, result.exit))) =
      some (false, true, 2, [(1, some ⟨2⟩, .timer, .failure (Cause.fail (.tagged "Timeout" "2000 ms")))]) := by kernel_rfl

/-- The original proposition remains explicitly refuted after repairing the timeout form. -/
theorem replyBasedRetry_refuted : ¬ ReplyBasedRetriesDeclared := by
  intro h
  have hcx := yieldedSuccess_observation
  cases hb : Effect4.Api.Author.build fetch with
  | error e =>
    rw [hb] at hcx
    cases hcx
  | ok b =>
    rw [hb] at hcx
    have htrue := h b yieldedSuccess hb yieldedSuccess_plain
    simp only [Except.toOption, Option.map_some] at hcx
    have wrong := congrArg Prod.fst (Option.some.inj hcx)
    rw [htrue] at wrong
    cases wrong

end Test.Dogfood.Proofs.TimeoutCounterexample
