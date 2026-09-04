import Effect4.Machine.Exit
import Effect4.Machine.Frames

/-!
# Frame-machine runtime kernel dependency report

Every authored public theorem named by `test/contracts/frames.contract.md` is
listed exactly once, in contract order. The accepted ceiling is no dependency,
`propext`, or `propext` with `Quot.sound`; `Classical.choice` and
project-local axioms are not admitted.

This report is breaker-owned and red until the fenced declarations exist.
-/

/-! ## F0 — the three continuation slots (census: rule.frames-are-primitives) -/

#print axioms Effect4.Arm.all_nodup
#print axioms Effect4.Arm.mem_all
#print axioms Effect4.Arm.cases_receipt
#print axioms Effect4.Arm.demandable_eq
#print axioms Effect4.Arm.contAll_not_demandable

/-! ## F1 — the primitive syntax (census: op.Success .. op.While) -/

#print axioms Effect4.Prim.cases_receipt

/-! ## F2 — the fiber state (census: rule.frames-are-primitives) -/

#print axioms Effect4.FrameFiber.start_eq
#print axioms Effect4.FrameFiber.pendingCause_some
#print axioms Effect4.FrameFiber.pendingCause_none
#print axioms Effect4.FrameFiber.masked_eq
#print axioms Effect4.FrameFiber.interrupted_eq

/-! ## F2b — pop answers, trace events, and step results (census: checkpoint.getcont-deferred,
rule.frames-are-primitives) -/

#print axioms Effect4.FrameEvent.poppedFrames_nil
#print axioms Effect4.FrameEvent.poppedFrames_cons_popped
#print axioms Effect4.FrameEvent.finalizersRun_nil
#print axioms Effect4.FrameEvent.finalizersRun_cons_ran
#print axioms Effect4.FrameEvent.finalizersRun_cons_popped

/-! ## F3 — the frame-arm matrix (census: frame-arm.OnSuccess .. frame-arm.Iterator,
rule.frames-are-primitives) -/

#print axioms Effect4.Prim.hasArm_eq
#print axioms Effect4.Prim.isFrame_eq
#print axioms Effect4.Prim.isFrame_iff
#print axioms Effect4.Prim.arms_onSuccess
#print axioms Effect4.Prim.arms_onFailure
#print axioms Effect4.Prim.arms_onSuccessAndFailure
#print axioms Effect4.Prim.arms_exitFrame
#print axioms Effect4.Prim.arms_onExit
#print axioms Effect4.Prim.arms_setInterruptible
#print axioms Effect4.Prim.arms_whileLoop
#print axioms Effect4.Prim.arms_iterator
#print axioms Effect4.Prim.arms_asyncFinalizer
#print axioms Effect4.Prim.hasArm_asyncFinalizer_contA_false
#print axioms Effect4.Prim.non_frames_have_no_arms

/-! ## F3b — an Exit is a steppable primitive (census: exit.success-failure) -/

#print axioms Effect4.Prim.ofExit_asExit?
#print axioms Effect4.Prim.asExit?_success
#print axioms Effect4.Prim.asExit?_failure
#print axioms Effect4.Prim.asExit?_eq_some
#print axioms Effect4.Prim.ofExit_isFrame

/-! ## F4 — the ensure hook and the answer selection (census: frame-arm.OnExit,
frame-arm.SetInterruptible, op.SetInterruptible, checkpoint.set-interruptible-contall) -/

#print axioms Effect4.Prim.ensure_of_no_contAll
#print axioms Effect4.Prim.ensure_onExit_masks
#print axioms Effect4.Prim.ensure_onExit_told_not_to
#print axioms Effect4.Prim.ensure_onExit_already_masked
#print axioms Effect4.Prim.ensure_onExit_no_replacement
#print axioms Effect4.Prim.ensure_setInterruptible_flag
#print axioms Effect4.Prim.ensure_setInterruptible_stack
#print axioms Effect4.Prim.ensure_setInterruptible_substitutes
#print axioms Effect4.Prim.ensure_setInterruptible_false_no_replacement
#print axioms Effect4.Prim.ensure_setInterruptible_no_pending
#print axioms Effect4.Prim.ensure_asyncFinalizer_masks
#print axioms Effect4.Prim.ensure_asyncFinalizer_already_masked
#print axioms Effect4.Prim.ensure_asyncFinalizer_no_replacement
#print axioms Effect4.Prim.answerOf_replacement
#print axioms Effect4.Prim.answerOf_arm
#print axioms Effect4.Prim.answerOf_missing
#print axioms Effect4.Prim.answerOf_frame_eq

/-! ## F5 — the arms (census: op.OnSuccess, op.OnFailure, op.OnSuccessAndFailure, op.Exit,
op.OnExit, op.Iterator, op.While) -/

#print axioms Effect4.Prim.armA_isSome
#print axioms Effect4.Prim.armE_isSome
#print axioms Effect4.Prim.armA_onSuccess
#print axioms Effect4.Prim.armA_onSuccessAndFailure
#print axioms Effect4.Prim.armE_onFailure
#print axioms Effect4.Prim.armE_onSuccessAndFailure
#print axioms Effect4.Prim.armE_onSuccess_none
#print axioms Effect4.Prim.armA_onFailure_none
#print axioms Effect4.Prim.armA_setInterruptible_none
#print axioms Effect4.Prim.armE_setInterruptible_none
#print axioms Effect4.Prim.armE_whileLoop_none
#print axioms Effect4.Prim.armE_iterator_none
#print axioms Effect4.Prim.armA_asyncFinalizer_none
#print axioms Effect4.Prim.armE_asyncFinalizer_interrupt
#print axioms Effect4.Prim.armE_asyncFinalizer_no_interrupt
#print axioms Effect4.Prim.armE_asyncFinalizer_pushes_nothing
#print axioms Effect4.Prim.armA_exitFrame_provided
#print axioms Effect4.Prim.armA_exitFrame_none
#print axioms Effect4.Prim.armE_exitFrame_provided
#print axioms Effect4.Prim.armE_exitFrame_none
#print axioms Effect4.Prim.armA_onExit
#print axioms Effect4.Prim.armE_onExit
#print axioms Effect4.Prim.onExit_finalizer_success_restores
#print axioms Effect4.Prim.onExit_finalizer_failure_merges
#print axioms Effect4.Prim.onExit_success_finalizer_failure
#print axioms Effect4.Prim.onExit_arm_is_per_frame
#print axioms Effect4.Prim.onSuccess_arm_is_per_instance
#print axioms Effect4.Prim.onFailure_arm_is_per_instance
#print axioms Effect4.Prim.onSuccessAndFailure_arms_are_per_instance
#print axioms Effect4.Prim.armA_whileLoop_continue
#print axioms Effect4.Prim.armA_whileLoop_stop
#print axioms Effect4.Prim.armA_iterator_done
#print axioms Effect4.Prim.armA_iterator_halt
#print axioms Effect4.Prim.armA_iterator_resume
#print axioms Effect4.Prim.iteratorFolded_eq
#print axioms Effect4.Prim.iterator_folds_inline
#print axioms Effect4.Prim.finalizerEvents_onExit
#print axioms Effect4.Prim.finalizerEvents_onSuccess
#print axioms Effect4.Prim.finalizerEvents_onFailure

/-! ## F6 — the pop (census: checkpoint.getcont-deferred, checkpoint.exit-failcause-skip,
rule.frames-are-primitives, rule.interrupt-bypasses-handlers) -/

#print axioms Effect4.FrameFiber.getCont_deferred
#print axioms Effect4.FrameFiber.getCont_deferred_pops_nothing
#print axioms Effect4.FrameFiber.getCont_eq_popFrom
#print axioms Effect4.FrameFiber.getCont_skip_clears_deferred
#print axioms Effect4.FrameFiber.getCont_empty_stack
#print axioms Effect4.FrameFiber.popFrom_nil
#print axioms Effect4.FrameFiber.popFrom_answer_answer
#print axioms Effect4.FrameFiber.popFrom_answer_popped
#print axioms Effect4.FrameFiber.popFrom_answer_events
#print axioms Effect4.FrameFiber.popFrom_answer_fiber
#print axioms Effect4.FrameFiber.popFrom_continue_answer
#print axioms Effect4.FrameFiber.popFrom_continue_popped
#print axioms Effect4.FrameFiber.popFrom_continue_events
#print axioms Effect4.FrameFiber.popFrom_continue_fiber
#print axioms Effect4.FrameFiber.popFrom_answer_hasArm
#print axioms Effect4.FrameFiber.getCont_answer_hasArm
#print axioms Effect4.FrameFiber.passEvents_ranContAll
#print axioms Effect4.FrameFiber.passEvents_poppedFrames
#print axioms Effect4.FrameFiber.popFrom_popped_eq_events
#print axioms Effect4.FrameFiber.popFrom_ranContAll
#print axioms Effect4.FrameFiber.stack_nil_eq
#print axioms Effect4.FrameFiber.ensure_stack_cases
#print axioms Effect4.FrameFiber.passPushed_nil
#print axioms Effect4.FrameFiber.passPushed_answer_hasArm
#print axioms Effect4.FrameFiber.passPushed_setInterruptible_substitutes
#print axioms Effect4.FrameFiber.passPushed_setInterruptible_no_pending
#print axioms Effect4.FrameFiber.joinPushed_of_empty
#print axioms Effect4.FrameFiber.joinPushed_of_answer
#print axioms Effect4.FrameFiber.continueFrom_cases
#print axioms Effect4.FrameFiber.popFrom_pass_no_push
#print axioms Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push
#print axioms Effect4.FrameFiber.getCont_ranContAll
#print axioms Effect4.FrameFiber.getCont_skip_of_no_pending_cause
#print axioms Effect4.FrameFiber.interrupt_skips_every_handler
#print axioms Effect4.FrameFiber.getCont_mask_stops_skip

/-! ## F7 — resuming and stepping (census: op.Success .. op.While, exit.success-failure) -/

#print axioms Effect4.FrameFiber.resumeValue_empty
#print axioms Effect4.FrameFiber.resumeValue_deferred
#print axioms Effect4.FrameFiber.resumeValue_replacement
#print axioms Effect4.FrameFiber.resumeValue_frame
#print axioms Effect4.FrameFiber.resumeCause_empty
#print axioms Effect4.FrameFiber.resumeCause_deferred
#print axioms Effect4.FrameFiber.resumeCause_replacement
#print axioms Effect4.FrameFiber.resumeCause_frame
#print axioms Effect4.FrameFiber.step_success
#print axioms Effect4.FrameFiber.step_failure
#print axioms Effect4.FrameFiber.step_sync
#print axioms Effect4.FrameFiber.step_suspend
#print axioms Effect4.FrameFiber.step_withFiber
#print axioms Effect4.FrameFiber.step_yieldableError
#print axioms Effect4.FrameFiber.step_onSuccess
#print axioms Effect4.FrameFiber.step_onFailure
#print axioms Effect4.FrameFiber.step_onSuccessAndFailure
#print axioms Effect4.FrameFiber.step_exitFrame
#print axioms Effect4.FrameFiber.step_onExit
#print axioms Effect4.FrameFiber.step_setInterruptible_not_evaluable
#print axioms Effect4.FrameFiber.step_asyncFinalizer_not_evaluable
#print axioms Effect4.FrameFiber.step_yieldNowWith_frontier
#print axioms Effect4.FrameFiber.step_async_frontier
#print axioms Effect4.FrameFiber.step_parking_is_a_fixed_point
#print axioms Effect4.FrameFiber.step_whileLoop_true
#print axioms Effect4.FrameFiber.step_whileLoop_false
#print axioms Effect4.FrameFiber.step_iterator
#print axioms Effect4.FrameFiber.step_ofExit_finishes
#print axioms Effect4.FrameFiber.run_zero
#print axioms Effect4.FrameFiber.run_succ_finished
#print axioms Effect4.FrameFiber.run_succ_running

/-! ## F8 — masks and the stack side of the two brackets (census:
checkpoint.set-fiber-interruptible, scope.scoped, scope.acquire-release) -/

#print axioms Effect4.FrameFiber.uninterruptible_already_masked
#print axioms Effect4.FrameFiber.uninterruptible_masks
#print axioms Effect4.FrameFiber.uninterruptibleMask_eq
#print axioms Effect4.FrameFiber.setFiberInterruptible_flag
#print axioms Effect4.FrameFiber.setFiberInterruptible_pushes
#print axioms Effect4.FrameFiber.setFiberInterruptible_immediate_failure
#print axioms Effect4.FrameFiber.setFiberInterruptible_no_pending
#print axioms Effect4.FrameFiber.interruptibleRegion_already
#print axioms Effect4.FrameFiber.interruptibleRegion_masked
#print axioms Effect4.FrameFiber.restoreAcquire_asked
#print axioms Effect4.FrameFiber.restoreAcquire_not_asked
#print axioms Effect4.Prim.scopedFrame_eq
#print axioms Effect4.Prim.scopedFrame_finalizer_masked
#print axioms Effect4.FrameFiber.step_scopedFrame

/-! ## F9 — the two foreign boundaries (census: op.WithFiber, op.YieldableError) -/

#print axioms Effect4.Prim.withFiber_refused
#print axioms Effect4.Prim.yieldableError_host_class_refused


/-! ## F10 — the uninterrupted fragment and fuel additivity (census:
checkpoint.getcont-deferred, checkpoint.exit-failcause-skip,
exit.success-failure) -/

#print axioms Effect4.FrameFiber.popFrom_interruptedCause
#print axioms Effect4.FrameFiber.popFrom_deferredInterrupt
#print axioms Effect4.FrameFiber.getCont_fiber_uninterrupted
#print axioms Effect4.FrameFiber.popFrom_never_skips
#print axioms Effect4.FrameFiber.popFrom_answer_ne_deferred
#print axioms Effect4.FrameFiber.getCont_never_defers
#print axioms Effect4.FrameFiber.step_preserves_uninterrupted
#print axioms Effect4.FrameFiber.run_preserves_uninterrupted
#print axioms Effect4.FrameFiber.run_add
#print axioms Effect4.FrameFiber.run_add_finished
#print axioms Effect4.FrameFiber.run_add_running
#print axioms Effect4.FrameFiber.run_mono
