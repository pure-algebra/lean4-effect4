import Effect4.Concurrency.Scheduler

/-!
# Fiber representative kernel dependency report

Every authored public theorem in `Fiber`, `Interrupt`, and `Scheduler` is
listed exactly once. The accepted ceiling is no dependency, `propext`, or
`propext` with `Quot.sound`; `Classical.choice` and project-local axioms are
not admitted.
-/

#print axioms Effect4.InterruptMask.cases_receipt
#print axioms Effect4.CleanupState.cases_receipt
#print axioms Effect4.FiberStatus.active_iff
#print axioms Effect4.FiberStatus.cases_receipt
#print axioms Effect4.Event.cleanupId_eq_some
#print axioms Effect4.Machine.fiber_eq_find
#print axioms Effect4.Machine.terminal_eq
#print axioms Effect4.Machine.mask_eq
#print axioms Effect4.Machine.interruptPending_eq
#print axioms Effect4.Machine.cleanupState_eq
#print axioms Effect4.Machine.cleanupCount_eq
#print axioms Effect4.Machine.cleanupEventIds_eq
#print axioms Effect4.Machine.transition_fibers
#print axioms Effect4.Machine.transition_trace
#print axioms Effect4.Machine.transition_cleanupEventIds
#print axioms Effect4.Machine.transition_fiber_other
#print axioms Effect4.Machine.finished_iff
#print axioms Effect4.SchedulerRefusal.cases_receipt
#print axioms Effect4.SchedulerDecision.cases_receipt
#print axioms Effect4.Event.cases_receipt
#print axioms Effect4.StepResult.machine_advanced
#print axioms Effect4.StepResult.machine_refused
#print axioms Effect4.ReplayResult.machine_finished
#print axioms Effect4.ReplayResult.machine_refused
#print axioms Effect4.ReplayResult.machine_frontier
#print axioms Effect4.step_iff
#print axioms Effect4.stepEval_schedule_missing
#print axioms Effect4.stepEval_schedule_runnable
#print axioms Effect4.stepEval_schedule_invalid
#print axioms Effect4.stepEval_join_missing_waiter
#print axioms Effect4.stepEval_join_missing_target
#print axioms Effect4.stepEval_join_done
#print axioms Effect4.stepEval_join_done_missing_terminal
#print axioms Effect4.stepEval_join_waiting
#print axioms Effect4.stepEval_join_invalid
#print axioms Effect4.stepEval_join_done_invalid
#print axioms Effect4.stepEval_join_self_invalid
#print axioms Effect4.stepEval_interrupt_missing_requester
#print axioms Effect4.stepEval_interrupt_missing_target
#print axioms Effect4.stepEval_interrupt_masked
#print axioms Effect4.stepEval_interrupt_unmasked
#print axioms Effect4.stepEval_interrupt_invalid
#print axioms Effect4.stepEval_enterMask_missing
#print axioms Effect4.stepEval_enterMask
#print axioms Effect4.stepEval_enterMask_invalid
#print axioms Effect4.stepEval_enterMask_inactive
#print axioms Effect4.stepEval_exitMask_missing
#print axioms Effect4.stepEval_exitMask_pending
#print axioms Effect4.stepEval_exitMask_clear
#print axioms Effect4.stepEval_exitMask_invalid
#print axioms Effect4.stepEval_exitMask_inactive
#print axioms Effect4.stepEval_complete_missing
#print axioms Effect4.stepEval_complete_running
#print axioms Effect4.stepEval_complete_invalid
#print axioms Effect4.stepEval_cleanup_missing
#print axioms Effect4.stepEval_cleanup_ready
#print axioms Effect4.stepEval_cleanup_invalid
#print axioms Effect4.step_deterministic
#print axioms Effect4.step_preserves_wellFormed
#print axioms Effect4.runs_nil_iff
#print axioms Effect4.runs_cons_iff
#print axioms Effect4.fixedTape_deterministic
#print axioms Effect4.finite_replay_total
#print axioms Effect4.step_total
#print axioms Effect4.runs_preserves_wellFormed
#print axioms Effect4.done_join_exists
#print axioms Effect4.waiting_join_exists
#print axioms Effect4.masked_request_exists
#print axioms Effect4.unmasked_request_exists
#print axioms Effect4.enter_mask_exists
#print axioms Effect4.pending_unmask_exists
#print axioms Effect4.unmask_without_pending_exists
#print axioms Effect4.completion_exists
#print axioms Effect4.cleanup_exists
#print axioms Effect4.unknown_schedule_refuses
#print axioms Effect4.invalid_completion_refuses
#print axioms Effect4.runs_nil_finished
#print axioms Effect4.runs_nil_frontier
#print axioms Effect4.join_agreement
#print axioms Effect4.double_join_agreement
#print axioms Effect4.unmasked_interrupt_delivers
#print axioms Effect4.masked_interrupt_defers
#print axioms Effect4.unmask_delivers_pending
#print axioms Effect4.cleanup_preserves_terminal
#print axioms Effect4.cleanup_at_most_once
#print axioms Effect4.cleanup_events_at_most_once
#print axioms Effect4.cleanup_events_agree
#print axioms Effect4.cleanup_count_monotone
#print axioms Effect4.cleanup_safe_on_finish
#print axioms Effect4.representative_inputs_exist
#print axioms Effect4.exists_representative_finished_run
#print axioms Effect4.interrupt_complete_order_distinct
