import Effect4Test.Flow.DeferredsContract
import Effect4Test.Counterexamples.Flow.Deferreds

/-!
# `Deferreds` kernel dependency report

Every authored theorem of the `Deferreds` contract and of its counterexample
battery, listed once, in source order. The accepted ceiling is no dependency,
`propext`, or `propext` with `Quot.sound`; `Classical.choice` and
project-local axioms are not admitted.

The `#guard` receipts of the contract are not listed: a `#guard` adds no
declaration to the environment, so it has no kernel dependency to report. What
it does have is a reduction, performed at elaboration time, of exactly the term
the golden was rendered from.
-/

/-! ## The sequential projection (`Effect4Test/Flow/DeferredsContract.lean`) -/

#print axioms Effect4Test.Flow.DeferredsContract.isDone_eq_poll_isSome
#print axioms Effect4Test.Flow.DeferredsContract.succeed_once
#print axioms Effect4Test.Flow.DeferredsContract.fail_after_succeed
#print axioms Effect4Test.Flow.DeferredsContract.awaitValue_of_completed
#print axioms Effect4Test.Flow.DeferredsContract.awaitValue_pending
#print axioms Effect4Test.Flow.DeferredsContract.pendingAwait_is_a_frontier

/-! ## `E4-SEM-CE-012` — a pending await is not a failure -/

#print axioms Effect4Test.Counterexamples.Flow.Deferreds.stall_as_failure_is_indistinguishable
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.stall_as_failure_agrees_under_every_mask
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.frontier_separates_under_the_outcome_mask
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.frontier_separates_under_every_mask
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.frontier_log_has_no_outcome

/-! ## `E4-SEM-CE-013` — the sequential projection is not the whole behaviour -/

#print axioms Effect4Test.Counterexamples.Flow.Deferreds.the_child_changes_the_answer
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.no_state_function_matches_both
#print axioms Effect4Test.Counterexamples.Flow.Deferreds.the_shared_prefix_is_the_frontier_log
