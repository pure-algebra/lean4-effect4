import Lean
import Effect4.Machine.Supervision
import Effect4.Machine.Cause
import Effect4.Machine.Exit
import Effect4.Machine.Scope
import Effect4.Machine.Frames
import Effect4.Laws.Machine.Clauses
import Effect4.Machine.Stores
import Effect4.Laws.Machine.Witnesses
import Effect4.Laws.Program.Intro

/-!
# Effect v4 fiber runtime coverage

This test-only checker joins the mechanical behaviour census of the pinned
`effect@4.0.0-rc.112` fiber runtime (`generated/effect-runtime-census.tsv`,
produced by `scripts/generate-effect-runtime-census.sh`) to the Lean
declarations that witness those behaviours.

The census keys are *observed runtime behaviours*, never "function X exists".
This module holds the frozen row list — one row per census id, carrying the
disposition defined in `docs/RUNTIME-COVERAGE.md`, the declared coverage state, and the witness
theorems. It fails the build on a missing witness, a witness that is not a
theorem, a duplicate id, or an inconsistent disposition/coverage pairing.
`scripts/check-effect-runtime-census.sh` cross-checks the row ids and kinds
against the census.

Until 2026-09-13 the module also froze every witness's statement in a `#check`
ascription (627 of them, transcribed by hand) and every witness's axiom
receipt. Both were copies: a statement lives in its theorem, and its change is
that theorem's diff; the ceiling is `#effect4_axiom_gate`'s, held over every
declaration. The join now says only what nothing else says — which theorem
witnesses which behaviour, and that it is a theorem.

Nothing here adds to or removes from the `Effect4` surface. Since
2026-09-04 the fiber rows are witnessed by the reference machine
(`src/Effect4/Laws/Machine/Clauses.lean`, `Witnesses.lean`, `Stores.lean`)
and the frame machine (`src/Effect4/Machine/Frames.lean`); the retired
scheduler and supervision calculi cite nothing here any more. Since the join
of 2026-09-07 the layer rows and the two scope rows the Layer machine carried
are witnessed on the compile route (`src/Effect4/Program/{Compile,Agreement,
Intro}.lean`) and by the store laws (`src/Effect4/Laws/Machine/StoresLaws.lean`);
`Machine/Layer.lean` retired with the join.
-/

open Lean Elab Command

namespace Test.Audit.RuntimeCoverage

/-! ## The frozen census join -/

/-- One census row. `id` and `kind` must match `generated/effect-runtime-census.tsv`
exactly; the cross-check lives in `scripts/check-effect-runtime-census.sh`. -/
private structure Row where
  /-- Stable kebab id, identical to the census row id. -/
  id : String
  /-- Census kind, identical to the census row kind. -/
  kind : String
  /-- `PORT-MANIFEST.md` disposition vocabulary. -/
  disposition : String
  /-- `green`, `partial` or `absent`. -/
  coverage : String
  /-- The witness theorems. -/
  witnesses : List Name

/-- Manifest dispositions that place a row outside the coverage denominator. -/
private def excludedDispositions : List String :=
  ["excludedInternal", "targetOnly", "evidenceOnly"]

private def knownDispositions : List String :=
  [ "owned", "split", "downstreamAdapter", "separateCalculus", "derivedExpansion"
  , "foreignBoundary", "targetOnly", "evidenceOnly", "excludedInternal" ]

private def knownKinds : List String :=
  [ "op", "frame-arm", "checkpoint", "interrupt", "fork", "scope", "scheduler"
  , "exit", "cause", "entry", "rule", "ref", "deferred", "layer" ]

private def knownCoverage : List String := ["green", "partial", "absent"]

private def censusRows : List Row :=
  [ { id := "op.Success", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.getCont_empty_stack
        , `Effect4.FrameFiber.resumeValue_empty
        , `Effect4.FrameFiber.resumeValue_frame
        , `Effect4.FrameFiber.step_success
        , `Effect4.FrameFiber.step_ofExit_finishes ] }
  , { id := "op.Failure", kind := "op", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "annotates the cause with the current stack frame" needs a fiber Context and a StackTrace service key
    , witnesses :=
        [ `Effect4.FrameFiber.interrupt_skips_every_handler
        , `Effect4.FrameFiber.resumeCause_empty
        , `Effect4.FrameFiber.resumeCause_frame
        , `Effect4.FrameFiber.step_failure ] }
  , { id := "op.WithFiber", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the raw FiberImpl host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ `Effect4.FrameFiber.step_withFiber
        , `Effect4.Prim.withFiber_refused ] }
  , { id := "op.YieldableError", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the host Error subclass identity clause is closed by refusal, not by a model
    , witnesses :=
        [ `Effect4.FrameFiber.step_yieldableError
        , `Effect4.Prim.yieldableError_host_class_refused ] }
  , { id := "op.Sync", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.step_sync
        , `Effect4.Machine.evaluatePrim_sync_answers
        , `Effect4.Machine.evaluatePrim_sync_pure
        , `Effect4.Machine.settle_answered
        , `Effect4.Machine.drive_loop_answered
        , `Effect4.Machine.drive_deliver
        , `Effect4.Machine.Witnesses.w13_completion_pop_sees_the_waiter_interrupt
        , `Effect4.Machine.Witnesses.w13_sync_meets_the_finalizer_program ] }
  , { id := "op.Suspend", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.step_suspend ] }
  , { id := "op.Yield", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.evaluatePrim_yieldNowWith ] }
  , { id := "op.Async", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.step_async_frontier
        , `Effect4.Machine.evaluatePrim_async_immediate
        , `Effect4.Machine.evaluatePrim_async_parks ] }
  , { id := "op.AsyncFinalizer", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armE_asyncFinalizer_interrupt
        , `Effect4.Prim.armE_asyncFinalizer_no_interrupt
        , `Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push
        , `Effect4.Prim.ensure_asyncFinalizer_masks
        , `Effect4.Machine.withFiber_dropObservers
        , `Effect4.Machine.Witnesses.w14_join_cleanup_drops_the_observer ] }
  , { id := "op.Iterator", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armA_iterator_done
        , `Effect4.Prim.armA_iterator_halt
        , `Effect4.Prim.armA_iterator_resume
        , `Effect4.Prim.iteratorFolded_eq
        , `Effect4.Prim.iterator_folds_inline
        , `Effect4.FrameFiber.step_iterator ] }
  , { id := "op.OnSuccess", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armA_onSuccess
        , `Effect4.Prim.armA_onSuccessConst
        , `Effect4.FrameFiber.step_onSuccessConst
        , `Effect4.FrameFiber.resumeValue_onSuccessConst
        , `Effect4.FrameFiber.step_success_onSuccessConst
        , `Effect4.Prim.onSuccess_arm_is_per_instance
        , `Effect4.FrameFiber.step_onSuccess ] }
  , { id := "op.OnFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armE_onFailure
        , `Effect4.Prim.onFailure_arm_is_per_instance
        , `Effect4.FrameFiber.step_onFailure ] }
  , { id := "op.OnSuccessAndFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armA_onSuccessAndFailure
        , `Effect4.Prim.armE_onSuccessAndFailure
        , `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance
        , `Effect4.FrameFiber.step_onSuccessAndFailure ] }
  , { id := "op.Exit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armA_exitFrame_provided
        , `Effect4.Prim.armA_exitFrame_none
        , `Effect4.Prim.armE_exitFrame_provided
        , `Effect4.Prim.armE_exitFrame_none
        , `Effect4.FrameFiber.step_exitFrame ] }
  , { id := "op.OnExit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.ensure_onExit_masks
        , `Effect4.Prim.ensure_onExit_told_not_to
        , `Effect4.Prim.ensure_onExit_already_masked
        , `Effect4.Prim.armA_onExit
        , `Effect4.Prim.armE_onExit
        , `Effect4.Prim.onExit_finalizer_success_restores
        , `Effect4.Prim.onExit_finalizer_failure_merges
        , `Effect4.Prim.onExit_success_finalizer_failure
        , `Effect4.Prim.finalizerEvents_onExit
        , `Effect4.Prim.finalizerEvents_onSuccess
        , `Effect4.Prim.finalizerEvents_onFailure
        , `Effect4.FrameFiber.step_onExit ] }
  , { id := "op.SetInterruptible", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_setInterruptible
        , `Effect4.Prim.ensure_setInterruptible_flag
        , `Effect4.Prim.ensure_setInterruptible_stack
        , `Effect4.Prim.ensure_setInterruptible_substitutes
        , `Effect4.Prim.ensure_setInterruptible_false_no_replacement
        , `Effect4.Prim.ensure_setInterruptible_no_pending
        , `Effect4.Prim.armA_setInterruptible_none
        , `Effect4.Prim.armE_setInterruptible_none
        , `Effect4.FrameFiber.step_setInterruptible_not_evaluable ] }
  , { id := "op.While", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.armA_whileLoop_continue
        , `Effect4.Prim.armA_whileLoop_stop
        , `Effect4.FrameFiber.step_whileLoop_true
        , `Effect4.FrameFiber.step_whileLoop_false ] }
  , { id := "frame-arm.OnSuccess", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_onSuccess
        , `Effect4.Prim.arms_onSuccessConst
        , `Effect4.Prim.ensure_onSuccessConst
        , `Effect4.Prim.armE_onSuccessConst_none
        , `Effect4.Prim.armA_isSome
        , `Effect4.Prim.armE_isSome
        , `Effect4.Prim.armE_onSuccess_none
        , `Effect4.Prim.onSuccess_arm_is_per_instance ] }
  , { id := "frame-arm.OnFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_onFailure
        , `Effect4.Prim.armA_onFailure_none
        , `Effect4.Prim.onFailure_arm_is_per_instance ] }
  , { id := "frame-arm.OnSuccessAndFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_onSuccessAndFailure
        , `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance ] }
  , { id := "frame-arm.Exit", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_exitFrame
        , `Effect4.Prim.ensure_of_no_contAll ] }
  , { id := "frame-arm.OnExit", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_onExit
        , `Effect4.Prim.ensure_onExit_masks
        , `Effect4.Prim.ensure_onExit_told_not_to
        , `Effect4.Prim.ensure_onExit_already_masked
        , `Effect4.Prim.ensure_onExit_no_replacement
        , `Effect4.Prim.onExit_arm_is_per_frame
        , `Effect4.Machine.Witnesses.w13_sync_meets_the_finalizer_program ] }
  , { id := "frame-arm.SetInterruptible", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_setInterruptible
        , `Effect4.Prim.ensure_setInterruptible_substitutes
        , `Effect4.Prim.answerOf_replacement
        , `Effect4.Prim.armA_setInterruptible_none
        , `Effect4.Prim.armE_setInterruptible_none
        , `Effect4.FrameFiber.resumeValue_replacement
        , `Effect4.FrameFiber.resumeCause_replacement ] }
  , { id := "frame-arm.AsyncFinalizer", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_asyncFinalizer
        , `Effect4.Prim.hasArm_asyncFinalizer_contA_false ] }
  , { id := "frame-arm.While", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_whileLoop
        , `Effect4.Prim.armE_whileLoop_none
        , `Effect4.FrameFiber.step_whileLoop_true ] }
  , { id := "frame-arm.Iterator", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.arms_iterator
        , `Effect4.Prim.armE_iterator_none
        , `Effect4.FrameFiber.step_iterator ] }
  , { id := "checkpoint.runloop-top", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.runloopTop_deferred
        , `Effect4.Machine.runloopTop_idle
        , `Effect4.Machine.runloopTop_clears
        , `Effect4.Machine.iteration_evaluates ] }
  , { id := "checkpoint.getcont-deferred", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.pendingCause_some
        , `Effect4.FrameFiber.pendingCause_none
        , `Effect4.FrameFiber.getCont_deferred
        , `Effect4.FrameFiber.getCont_deferred_pops_nothing
        , `Effect4.FrameFiber.getCont_skip_clears_deferred
        , `Effect4.FrameFiber.resumeValue_deferred
        , `Effect4.FrameFiber.resumeCause_deferred
        , `Effect4.Machine.Witnesses.w13_completion_pop_sees_the_waiter_interrupt ] }
  , { id := "checkpoint.post-yield-cancel", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.interruptRecord_parked_applies
        , `Effect4.Prim.armE_asyncFinalizer_interrupt
        , `Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push
        , `Effect4.Machine.Witnesses.w14_join_cleanup_drops_the_observer
        , `Effect4.Machine.Witnesses.w3_host_interrupt_cancels_entrants ] }
  , { id := "checkpoint.exit-failcause-skip", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.popFrom_continue_answer
        , `Effect4.FrameFiber.getCont_skip_of_no_pending_cause
        , `Effect4.FrameFiber.interrupt_skips_every_handler ] }
  , { id := "checkpoint.set-fiber-interruptible", kind := "checkpoint", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.FrameFiber.setFiberInterruptible_flag
        , `Effect4.FrameFiber.setFiberInterruptible_pushes
        , `Effect4.FrameFiber.setFiberInterruptible_immediate_failure
        , `Effect4.FrameFiber.setFiberInterruptible_no_pending
        , `Effect4.FrameFiber.interruptibleRegion_already
        , `Effect4.FrameFiber.interruptibleRegion_masked ] }
  , { id := "checkpoint.set-interruptible-contall", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.ensure_setInterruptible_substitutes
        , `Effect4.Prim.answerOf_replacement
        , `Effect4.FrameFiber.resumeValue_replacement
        , `Effect4.FrameFiber.resumeCause_replacement ] }
  , { id := "interrupt.unsafe-entry", kind := "interrupt", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.interruptRecord_exited
        , `Effect4.Machine.interruptRecord_records
        , `Effect4.Machine.interruptRecord_running_defers
        , `Effect4.Machine.interruptRecord_idle_applies
        , `Effect4.Machine.interruptRecord_masked ] }
  , { id := "interrupt.accumulate", kind := "interrupt", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.interruptCause_eq
        , `Effect4.Machine.interruptRecord_accumulates
        , `Effect4.Machine.interruptRecord_idle_applies
        , `Effect4.Machine.interruptRecord_running_defers
        , `Effect4.Machine.runloopTop_deferred
        , `Effect4.FrameFiber.pendingCause_some ] }
  , { id := "fork.unsafe", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.MaskMode.cases_receipt
        , `Effect4.Machine.spawn_eq
        , `Effect4.Machine.spawnChild_fields
        , `Effect4.Machine.spawn_untracked
        , `Effect4.Machine.drive_trackChild_live
        , `Effect4.Machine.drive_trackChild_exited ] }
  , { id := "fork.child", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.exitFiber_eq
        , `Effect4.Machine.exitFiber_no_middleware
        , `Effect4.Machine.publish_fields
        , `Effect4.Machine.cleared_fields
        , `Effect4.Machine.exitStore_no_observers
        , `Effect4.Machine.exitStore_observers
        , `Effect4.Machine.drive_observe
        , `Effect4.Machine.drive_exitDone
        , `Effect4.Machine.fireObserver_resumeAwait
        , `Effect4.Machine.stepDecision_installMiddleware
        , `Effect4.Machine.withFiber_fork
        , `Effect4.Machine.Witnesses.w1_deferred_join_child
        , `Effect4.Machine.Witnesses.w1_deferred_start_is_a_task
        , `Effect4.Machine.Witnesses.w5_middleware_interrupts_children
        , `Effect4.Machine.drive_finish ] }
  , { id := "fork.detach", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.spawn_untracked
        , `Effect4.Machine.spawnChild_fields
        , `Effect4.Machine.start_eq
        , `Effect4.Machine.exitFiber_no_children
        , `Effect4.Machine.exitInterruptChildren_eq
        , `Effect4.Machine.exitInterruptChildren_reenters
        , `Effect4.Machine.Witnesses.w5_fork_latches_the_middleware
        , `Effect4.Machine.Witnesses.w5_daemon_child_survives_parent_exit ] }
  , { id := "fork.in", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.ScopeMode.cases_receipt
        , `Effect4.Machine.withFiber_forkIn
        , `Effect4.Machine.linkScope_open
        , `Effect4.Machine.linkScope_closed
        , `Effect4.Machine.fireObserver_dropScopeFinalizer
        , `Effect4.Machine.withFiber_closeScope
        , `Effect4.Machine.Witnesses.w6_link_then_close
        , `Effect4.Machine.Witnesses.w6_closed_scope_interrupts_now
        , `Effect4.Machine.Witnesses.w6_child_exit_drops_key
        , `Effect4.Machine.drive_link
        , `Effect4.Machine.Witnesses.w6_deferred_child_is_linked ] }
  , { id := "fork.scoped", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.withFiber_forkScoped_ambient
        , `Effect4.Machine.withFiber_forkScoped_none
        , `Effect4.Machine.withFiber_ambientScope
        , `Effect4.Machine.withFiber_ambientScope_none ] }
  , { id := "fork.race-all", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.RaceAllState.initial_eq
        , `Effect4.Supervision.raceComplete_unknown
        , `Effect4.Supervision.raceComplete_after_accepted
        , `Effect4.Supervision.raceComplete_success
        , `Effect4.Supervision.raceComplete_failure_last
        , `Effect4.Supervision.raceComplete_failure_pending
        , `Effect4.Machine.withFiber_raceAll
        , `Effect4.Machine.evaluatePrim_raceRegister
        , `Effect4.Machine.launchEntrant_eq
        , `Effect4.Machine.drive_launch_runs
        , `Effect4.Machine.drive_enrollRace_live
        , `Effect4.Machine.drive_enrollRace_exited
        , `Effect4.Machine.drive_registrationDone_answered
        , `Effect4.Machine.drive_registrationDone_parks
        , `Effect4.Machine.drive_launch_done
        , `Effect4.Machine.fireObserver_raceCallback_pending
        , `Effect4.Machine.fireObserver_raceCallback_settles
        , `Effect4.Machine.fireObserver_raceCallback_late
        , `Effect4.Machine.resumePrim_continueWith
        , `Effect4.Machine.Witnesses.w3_empty_is_a_frontier
        , `Effect4.Machine.Witnesses.w3_empty_until_interrupted
        , `Effect4.Machine.Witnesses.w3_immediate_success_stops_launch
        , `Effect4.Machine.Witnesses.w3_failure_allows_next_launch
        , `Effect4.Machine.Witnesses.w3_all_failures_retain_order
        , `Effect4.Machine.settleRace_eq
        , `Effect4.Machine.withFiber_cancelRace
        , `Effect4.Machine.drive_raceCancel_nil
        , `Effect4.Machine.drive_raceCancel_live
        , `Effect4.Machine.drive_raceCancel_gone
        , `Effect4.Machine.withFiber_cancelRace_unknown
        , `Effect4.Machine.Witnesses.w3_host_interrupt_cancels_entrants
        , `Effect4.Machine.Witnesses.w3_settle_interrupts_the_parked_loser
        , `Effect4.Machine.drive_launch_exhausted ] }
  , { id := "fork.await-all-children", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.withFiber_snapshotChildren
        , `Effect4.Machine.withFiber_awaitNewChildren
        , `Effect4.Machine.fireObserver_countdown_done
        , `Effect4.Machine.fireObserver_countdown_next
        , `Effect4.Machine.Witnesses.w5_await_all_children_awaits_only_new
        , `Effect4.Machine.Witnesses.w12_awaitAll_answers_the_exits
        , `Effect4.Machine.countdownWalk_nil
        , `Effect4.Machine.countdownWalk_exited
        , `Effect4.Machine.countdownWalk_live
        , `Effect4.Machine.countdownPark_none_live
        , `Effect4.Machine.countdownPark_parks
        , `Effect4.Machine.Witnesses.w12_awaitAll_input_order
        , `Effect4.Machine.Witnesses.w5_await_all_children_on_failure ] }
  , { id := "fork.fiber-run-in", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.ScopeMode.cases_receipt
        , `Effect4.Machine.withFiber_runIn
        , `Effect4.Machine.linkScope_closed
        , `Effect4.Machine.linkScope_unknown
        , `Effect4.Machine.linkScope_open
        , `Effect4.Machine.linkScope_open_exited
        , `Effect4.Machine.Witnesses.w6_runIn_closed_scope_uses_no_caller_annotations ] }
  , { id := "fork.join", kind := "fork", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.ObserverMode.cases_receipt
        , `Effect4.Machine.evaluatePrim_join_done
        , `Effect4.Machine.evaluatePrim_join_live
        , `Effect4.Machine.evaluatePrim_join_unknown
        , `Effect4.Machine.Witnesses.w14_join_cleanup_drops_the_observer ] }
  , { id := "fork.await", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.ObserverMode.cases_receipt
        , `Effect4.Machine.evaluatePrim_join_done
        , `Effect4.Machine.evaluatePrim_join_live
        , `Effect4.Machine.withFiber_dropObservers
        , `Effect4.Machine.Witnesses.w14_join_cleanup_drops_the_observer ] }
  , { id := "fork.interrupt", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Supervision.interruptCause_eq
        , `Effect4.Machine.withFiber_interrupt
        , `Effect4.Machine.withFiber_interruptAs
        , `Effect4.Machine.withFiber_interruptAs_unknown
        , `Effect4.Machine.drive_afterInterrupt
        , `Effect4.Machine.asVoidCode_eq
        , `Effect4.Machine.awaitCode_join_exited
        , `Effect4.Machine.awaitCode_join_live
        , `Effect4.Machine.withFiber_interruptScoped_self
        , `Effect4.Machine.withFiber_interruptScoped_other
        , `Effect4.Machine.Witnesses.w2_delivered_at_unmask
        , `Effect4.Machine.Witnesses.w2_recorded_once
        , `Effect4.Machine.Witnesses.w2_masked_interrupt_does_not_apply
        , `Effect4.Machine.Witnesses.w6_self_interruptor_skipped ] }
  , { id := "fork.interrupt-all", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.withFiber_interruptAll
        , `Effect4.Machine.drive_interruptTarget
        , `Effect4.Machine.drive_interruptTarget_unknown
        , `Effect4.Machine.awaitCode_awaitAll
        , `Effect4.Machine.evaluatePrim_awaitAllPark
        , `Effect4.Machine.interruptEach_nil
        , `Effect4.Machine.interruptEach_cons
        , `Effect4.Machine.interruptEach_known
        , `Effect4.Machine.fireObserver_countdown_done
        , `Effect4.Machine.fireObserver_countdown_next
        , `Effect4.Machine.countdownPark_parks ] }
  , { id := "scope.states", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.ScopeState.cases_receipt
        , `Effect4.ScopeState.entries_empty
        , `Effect4.ScopeState.entries_openEmpty
        , `Effect4.ScopeState.entries_openInline
        , `Effect4.ScopeState.entries_openMap
        , `Effect4.ScopeState.entries_closed
        , `Effect4.ScopeState.isOpen_empty
        , `Effect4.ScopeState.isOpen_openEmpty
        , `Effect4.ScopeState.isOpen_openInline
        , `Effect4.ScopeState.isOpen_openMap
        , `Effect4.ScopeState.isOpen_closed
        , `Effect4.ScopeState.isClosed_eq
        , `Effect4.ScopeState.closingExit_closed
        , `Effect4.ScopeState.closingExit_of_not_closed
        , `Effect4.ScopeState.openEmpty_ne_openMap_nil
        , `Effect4.Scope.finalizers_eq
        , `Effect4.Scope.finalizerKeys_eq
        , `Effect4.Scope.finalizerCount_eq
        , `Effect4.Scope.finalizerCount_not_open ] }
  , { id := "scope.make", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FinalizerStrategy.all_nodup
        , `Effect4.FinalizerStrategy.mem_all
        , `Effect4.Scope.make_strategy
        , `Effect4.Scope.make_state
        , `Effect4.Scope.make_finalizers
        , `Effect4.Scope.makeDefault_eq
        , `Effect4.Scope.makeDefault_strategy ] }
  , { id := "scope.add-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.key_freshness_refused
        , `Effect4.Scope.tableInsert_new
        , `Effect4.Scope.tableInsert_existing
        , `Effect4.Scope.tableInsert_keys_of_mem
        , `Effect4.Scope.tableInsert_nodup
        , `Effect4.Scope.addUnsafe_strategy
        , `Effect4.Scope.addUnsafe_empty
        , `Effect4.Scope.addUnsafe_openEmpty
        , `Effect4.Scope.addUnsafe_openInline
        , `Effect4.Scope.addUnsafe_openMap
        , `Effect4.Scope.addUnsafe_promotes
        , `Effect4.Scope.addUnsafe_finalizers
        , `Effect4.Scope.addUnsafe_keys_nodup ] }
  , { id := "scope.add-after-closed", kind := "scope", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.addUnsafe_closed
        , `Effect4.Scope.addExit_open
        , `Effect4.Scope.addExit_closed
        , `Effect4.Scope.addExit_closed_registers_nothing
        , `Effect4.Scope.closingExit_addUnsafe
        , `Effect4.Machine.syncOpStep_scopeAdd_closed ] }
  , { id := "scope.remove-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.tableRemove_eq
        , `Effect4.Scope.tableRemove_keys
        , `Effect4.Scope.tableRemove_nodup
        , `Effect4.Scope.removeUnsafe_strategy
        , `Effect4.Scope.removeUnsafe_inline_hit
        , `Effect4.Scope.removeUnsafe_inline_miss
        , `Effect4.Scope.removeUnsafe_openMap
        , `Effect4.Scope.removeUnsafe_not_open
        , `Effect4.Scope.removeUnsafe_keys
        , `Effect4.Scope.removeUnsafe_keys_nodup ] }
  , { id := "scope.close-state-first", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.close_eq
        , `Effect4.Scope.close_state_independent_of_run
        , `Effect4.Scope.closeState_state
        , `Effect4.Scope.closeState_strategy
        , `Effect4.Scope.closeState_finalizers
        , `Effect4.Scope.closeState_isClosed
        , `Effect4.Scope.closeState_idempotent
        , `Effect4.Scope.close_closingExit
        , `Effect4.Scope.close_idempotent
        , `Effect4.Scope.close_twice
        , `Effect4.Scope.close_reentrant_add
        , `Effect4.Scope.closeResult_closed ] }
  , { id := "scope.close-lifo", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.closeOrder_eq
        , `Effect4.Scope.closeOrder_last_first
        , `Effect4.Scope.closeExits_eq
        , `Effect4.Scope.closeExits_reverse
        , `Effect4.Scope.runScoped_lifo
        , `Effect4.Machine.closeWalk_sequential
        , `Effect4.Machine.closeSeq_step ] }
  , { id := "scope.close-sequential", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.closeExits_eq
        , `Effect4.Scope.closeExits_length
        , `Effect4.Scope.closeResult_reasons
        , `Effect4.Machine.closeWalk_sequential
        , `Effect4.Machine.closeSeq_step
        , `Effect4.Machine.closeSeq_captures
        , `Effect4.Machine.withFiber_closeScope
        , `Effect4.Machine.withFiber_closeScope_unknown
        , `Effect4.Machine.Witnesses.w6_sequential_captures_and_merges ] }
  , { id := "scope.close-parallel", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.FinalizerStrategy.cases_receipt
        , `Effect4.Scope.close_strategy_irrelevant
        , `Effect4.Machine.closeWalk_parallel
        , `Effect4.Machine.actionOf_closePar
        , `Effect4.Machine.withFiber_closePar
        , `Effect4.Machine.forkFinalizers_cons
        , `Effect4.Machine.withFiber_fork
        , `Effect4.Machine.spawnChild_fields
        , `Effect4.Machine.Witnesses.w6_parallel_forks_and_merges ] }
  , { id := "scope.close-merge", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.closeResult_nil
        , `Effect4.Scope.closeResult_single
        , `Effect4.Scope.closeResult_many
        , `Effect4.Scope.closeResult_reasons
        , `Effect4.Machine.closeSeq_merges
        , `Effect4.Machine.closeParDone_is_asVoidAll
        , `Effect4.Machine.drive_closeParAwait
        , `Effect4.Machine.fireObserver_countdown_done
        , `Effect4.Machine.fireObserver_countdown_next
        , `Effect4.Machine.Witnesses.w6_parallel_forks_and_merges
        , `Effect4.Machine.Witnesses.w12_awaitAll_answers_the_exits ] }
  , { id := "scope.exit-as-void-all", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Exit.asVoidAll_reasons
        , `Effect4.Exit.asVoidAll_failure
        , `Effect4.Exit.asVoidAll_all_success
        , `Effect4.Exit.void_eq ] }
  , { id := "scope.fork-linkage", kind := "scope", disposition := "separateCalculus", coverage := "green"
      -- missing clause: that the linked names are scopeClose(child, exit) and scopeRemoveFinalizerUnsafe(parent, key) needs a scope store
    , witnesses :=
        [ `Effect4.Scope.fork_closed_parent
        , `Effect4.Scope.fork_closed_parent_child_exit
        , `Effect4.Scope.fork_open_parent
        , `Effect4.Scope.fork_child_finalizers
        , `Effect4.Scope.fork_parent_finalizers
        , `Effect4.Scope.fork_child_strategy
        , `Effect4.Scope.fork_shared_key
        , `Effect4.Scope.fork_detach
        , `Effect4.Machine.scopeLinkFiber_name
        , `Effect4.Machine.scopeStore_forkChild_names ] }
  , { id := "scope.scoped", kind := "scope", disposition := "separateCalculus", coverage := "green"
      -- missing clauses: "installs a fresh scope in the fiber context" and "restoring the previous context first"
    , witnesses :=
        [ `Effect4.Scope.addAll_nil
        , `Effect4.Scope.addAll_cons
        , `Effect4.Scope.addAll_finalizers
        , `Effect4.Scope.make_addAll_finalizers
        , `Effect4.Scope.runScoped_eq
        , `Effect4.Scope.runScoped_fresh_scope
        , `Effect4.Scope.runScoped_state
        , `Effect4.Scope.runScoped_strategy
        , `Effect4.Scope.runScoped_empty
        , `Effect4.Scope.runScoped_lifo
        , `Effect4.Prim.scopedFrame_eq
        , `Effect4.Prim.scopedFrame_finalizer_masked
        , `Effect4.FrameFiber.step_scopedFrame
        , `Effect4.Program.Agreement.enterScoped_eq
        , `Effect4.Program.Agreement.exitScoped_restores ] }
  , { id := "scope.acquire-release", kind := "scope", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.acquireRelease_failure
        , `Effect4.Scope.acquireRelease_success
        , `Effect4.Scope.acquireRelease_registers
        , `Effect4.Scope.acquireRelease_closed_ambient
        , `Effect4.FrameFiber.uninterruptible_already_masked
        , `Effect4.FrameFiber.uninterruptible_masks
        , `Effect4.FrameFiber.uninterruptibleMask_eq
        , `Effect4.FrameFiber.interruptibleRegion_already
        , `Effect4.FrameFiber.interruptibleRegion_masked
        , `Effect4.FrameFiber.restoreAcquire_asked
        , `Effect4.FrameFiber.restoreAcquire_not_asked
        , `Effect4.Program.Sched.release_intro
        , `Effect4.Program.Sched.foreignRelease_intro
        , `Effect4.Program.Sched.acquireIn_intro ] }
  , { id := "scheduler.should-yield", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.yieldVerdict_default
        , `Effect4.Machine.yieldVerdict_override
        , `Effect4.Machine.injectYield_no_verdict ] }
  , { id := "scheduler.priority-buckets", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.Dispatcher.enqueue_same_bucket
        , `Effect4.Machine.Dispatcher.enqueue_lower_priority
        , `Effect4.Machine.Dispatcher.enqueue_empty ] }
  , { id := "scheduler.dispatcher-arming", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.Dispatcher.enqueue_arms
        , `Effect4.Machine.Dispatcher.drain_disarms
        , `Effect4.Machine.RunMachine.arm_new
        , `Effect4.Machine.RunMachine.arm_known
        , `Effect4.Machine.RunMachine.arm_fields
        , `Effect4.Machine.Witnesses.w15_flush_runs_callbacks_in_arming_order ] }
  , { id := "scheduler.run-tasks-drain-once", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.Dispatcher.drain_eq
        , `Effect4.Machine.Dispatcher.drain_disarms
        , `Effect4.Machine.fire_eq
        , `Effect4.Machine.RunMachine.disarm_eq ] }
  , { id := "scheduler.flush", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.flushAll_idle
        , `Effect4.Machine.flushAll_round
        , `Effect4.Machine.Witnesses.w15_flush_runs_callbacks_in_arming_order ] }
  , { id := "scheduler.yield-now-resume-guard", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.evaluatePrim_yieldNowWith
        , `Effect4.Machine.drive_resume_wrong_token
        , `Effect4.Machine.drive_resume_guard
        , `Effect4.Machine.drive_resume_not_parked ] }
  , { id := "scheduler.max-ops-default", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.Env.hooks_empty ] }
  , { id := "scheduler.prevent-yield-default", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.injectYield_prevented
        , `Effect4.Machine.Env.hooks_empty ] }
  , { id := "scheduler.host-loop", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "exit.success-failure", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Exit.cases_receipt
        , `Effect4.Exit.success_ne_failure
        , `Effect4.Exit.success_inj
        , `Effect4.Exit.failure_inj
        , `Effect4.Exit.cause_failure
        , `Effect4.Prim.ofExit_asExit?
        , `Effect4.Prim.asExit?_success
        , `Effect4.Prim.asExit?_failure
        , `Effect4.Prim.asExit?_eq_some
        , `Effect4.Prim.ofExit_isFrame
        , `Effect4.FrameFiber.step_ofExit_finishes
        , `Effect4.FrameFiber.run_zero
        , `Effect4.FrameFiber.run_succ_finished
        , `Effect4.FrameFiber.run_succ_running ] }
  , { id := "exit.reason-alphabet", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.ReasonTag.all_nodup
        , `Effect4.ReasonTag.mem_all
        , `Effect4.ReasonTag.cases_receipt
        , `Effect4.Reason.cases_receipt
        , `Effect4.Reason.tag_mem_all ] }
  , { id := "cause.flat-reasons", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.eq_iff
        , `Effect4.Cause.ext
        , `Effect4.Cause.eq_iff_pointwise
        , `Effect4.Cause.combine_no_new_reason ] }
  , { id := "cause.reason-fail", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Reason.error_fail
        , `Effect4.Reason.annotations_fail
        , `Effect4.Reason.fail_inj ] }
  , { id := "cause.reason-die", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Reason.defect_die
        , `Effect4.Reason.annotations_die
        , `Effect4.Reason.die_inj ] }
  , { id := "cause.reason-interrupt", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.interrupt_reasons
        , `Effect4.Reason.annotations_interrupt
        , `Effect4.Reason.interrupt_inj ] }
  , { id := "cause.combine-union", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.combine_empty_left
        , `Effect4.Cause.combine_empty_right
        , `Effect4.Cause.combine_reasons
        , `Effect4.Cause.mem_combine
        , `Effect4.Cause.combine_self ] }
  , { id := "cause.finalizer-merge", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Exit.mergeFinalizer_failure_failure
        , `Effect4.Exit.restoreAfterFinalizer_failure_failure
        , `Effect4.Exit.mergeFinalizer_success_failure
        , `Effect4.Exit.restoreAfterFinalizer_success_failure ] }
  , { id := "cause.squash", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.squash_error
        , `Effect4.Cause.squash_defect
        , `Effect4.Cause.squash_interrupted
        , `Effect4.Cause.squash_emptyCause_iff
        , `Effect4.Cause.squash_fail_over_die ] }
  , { id := "cause.union-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.combine_empty_left
        , `Effect4.Cause.combine_empty_right
        , `Effect4.Cause.combine_reasons
        , `Effect4.Cause.combine_order ] }
  , { id := "cause.dedupe-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.dedup_cons
        , `Effect4.Cause.mem_dedup
        , `Effect4.Cause.dedup_nodup
        , `Effect4.Cause.dedup_of_nodup ] }
  , { id := "cause.annotations", kind := "cause", disposition := "foreignBoundary", coverage := "green"
      -- the WeakMap host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ `Effect4.ReasonAnnotations.keys_nodup
        , `Effect4.Reason.annotate_annotations
        , `Effect4.Reason.host_memory_refused
        , `Effect4.ReasonAnnotations.annotate_entries
        , `Effect4.ReasonAnnotations.lookup_annotate_kept
        , `Effect4.ReasonAnnotations.lookup_annotate_overwrite ] }
  , { id := "entry.run-fork-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.runFork_eq ] }
  , { id := "entry.abort-signal", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.stepDecision_abort ] }
  , { id := "entry.run-callback-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.runCallback_eq
        , `Effect4.Machine.fireObserver_callback ] }
  , { id := "entry.run-promise-exit-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.promiseOutcome_eq ] }
  , { id := "entry.run-promise-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.promiseOutcome_failure ] }
  , { id := "entry.run-sync-exit-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.runSyncExit_exited
        , `Effect4.Machine.runSyncExit_survives
        , `Effect4.Machine.flushRoot_idle
        , `Effect4.Machine.flushRoot_round
        , `Effect4.Machine.Witnesses.w8_sync_child_yield_is_async ] }
  , { id := "entry.async-fiber-error", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.runSyncExit_survives
        , `Effect4.Machine.Witnesses.w8_sync_child_yield_is_async ] }
  , { id := "entry.with-error-reporting", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.frames-are-primitives", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Arm.all_nodup
        , `Effect4.Arm.mem_all
        , `Effect4.Arm.cases_receipt
        , `Effect4.Arm.demandable_eq
        , `Effect4.Arm.contAll_not_demandable
        , `Effect4.Prim.cases_receipt
        , `Effect4.FrameFiber.start_eq
        , `Effect4.FrameFiber.masked_eq
        , `Effect4.FrameFiber.interrupted_eq
        , `Effect4.FrameEvent.poppedFrames_nil
        , `Effect4.FrameEvent.poppedFrames_cons_popped
        , `Effect4.FrameEvent.finalizersRun_nil
        , `Effect4.FrameEvent.finalizersRun_cons_ran
        , `Effect4.FrameEvent.finalizersRun_cons_popped
        , `Effect4.Prim.hasArm_eq
        , `Effect4.Prim.isFrame_eq
        , `Effect4.Prim.isFrame_iff
        , `Effect4.Prim.non_frames_have_no_arms
        , `Effect4.Prim.answerOf_replacement
        , `Effect4.Prim.answerOf_arm
        , `Effect4.Prim.answerOf_missing
        , `Effect4.Prim.answerOf_frame_eq
        , `Effect4.Prim.armA_isSome
        , `Effect4.Prim.armE_isSome
        , `Effect4.FrameFiber.getCont_eq_popFrom
        , `Effect4.FrameFiber.getCont_empty_stack
        , `Effect4.FrameFiber.popFrom_nil
        , `Effect4.FrameFiber.popFrom_answer_answer
        , `Effect4.FrameFiber.popFrom_answer_popped
        , `Effect4.FrameFiber.popFrom_answer_events
        , `Effect4.FrameFiber.popFrom_answer_fiber
        , `Effect4.FrameFiber.popFrom_continue_answer
        , `Effect4.FrameFiber.popFrom_continue_popped
        , `Effect4.FrameFiber.popFrom_continue_events
        , `Effect4.FrameFiber.popFrom_continue_fiber
        , `Effect4.FrameFiber.popFrom_answer_hasArm
        , `Effect4.FrameFiber.getCont_answer_hasArm
        , `Effect4.FrameFiber.passEvents_ranContAll
        , `Effect4.FrameFiber.passEvents_poppedFrames
        , `Effect4.FrameFiber.popFrom_popped_eq_events
        , `Effect4.FrameFiber.popFrom_ranContAll
        , `Effect4.FrameFiber.getCont_ranContAll ] }
  , { id := "rule.interrupt-bypasses-handlers", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Prim.ensure_setInterruptible_flag
        , `Effect4.FrameFiber.interrupt_skips_every_handler
        , `Effect4.FrameFiber.getCont_mask_stops_skip
        , `Effect4.FrameFiber.step_failure ] }
  , { id := "rule.yield-is-overloaded", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.drive_loop_parked
        , `Effect4.Machine.drive_loop_parked_deferred
        , `Effect4.Machine.drive_loop_continues ] }
  , { id := "rule.only-fork-child-tracks", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.spawn_untracked
        , `Effect4.Machine.drive_trackChild_live
        , `Effect4.Machine.drive_trackChild_exited
        , `Effect4.Machine.spawnChild_fields
        , `Effect4.Machine.withFiber_fork
        , `Effect4.Machine.withFiber_forkIn
        , `Effect4.Machine.withFiber_forkScoped_ambient
        , `Effect4.Machine.launchEntrant_eq
        , `Effect4.Machine.fireObserver_untrackChild ] }
  , { id := "rule.children-interrupted-after-exit", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.exitFiber_eq
        , `Effect4.Machine.exitFiber_children
        , `Effect4.Machine.exitInterruptChildren_eq
        , `Effect4.Machine.exitInterruptChildren_reenters
        , `Effect4.Machine.resumePrim_continueWith
        , `Effect4.Machine.exitFiber_finalizing
        , `Effect4.Machine.Witnesses.w5_middleware_interrupts_children
        , `Effect4.Machine.settle_finished
        , `Effect4.Machine.drive_finish ] }
  , { id := "rule.scope-close-lifo-state-first", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Scope.close_state_independent_of_run
        , `Effect4.Scope.closeState_finalizers
        , `Effect4.Scope.close_reentrant_add
        , `Effect4.Scope.closeOrder_last_first
        , `Effect4.Scope.closeExits_reverse ] }
  , { id := "rule.cause-has-no-structure", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Cause.mem_combine
        , `Effect4.Cause.combine_order
        , `Effect4.Cause.combine_no_new_reason
        , `Effect4.Cause.ext ] }
  , { id := "rule.start-is-asymmetric", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.start_eq
        , `Effect4.Machine.runFork_eq ] }
  , { id := "rule.record-and-apply-separate", kind := "rule", disposition := "owned", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.interruptRecord_records
        , `Effect4.Machine.interruptRecord_running_defers
        , `Effect4.Machine.interruptRecord_idle_applies
        , `Effect4.Machine.interruptRecord_masked ] }
  , { id := "rule.budget-per-runloop-entry", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.countOp_count
        , `Effect4.Machine.drive_evaluate_enters
        , `Effect4.Machine.drive_evaluate_exited
        , `Effect4.Machine.drive_evaluate_running
        , `Effect4.Machine.injectYield_latched
        , `Effect4.Machine.injectYield_fires
        , `Effect4.Machine.iteration_injected ] }
    -- The Ref and Deferred rows are carried by the reference machine's stores
    -- (`src/Effect4/Machine/Stores.lean`) since 2026-09-04, and the Layer rows by the
    -- compile route (`src/Effect4/Program/{Compile,Agreement}.lean`, the store laws) since
    -- the join of 2026-09-07 retired the Layer model. The five `derivedExpansion`
    -- rows are the ones the pinned source itself defines in terms of another
    -- pinned operation; the rest are `separateCalculus`.
  , { id := "ref.make", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_make
        , `Effect4.Machine.refMake_twice_distinct ] }
  , { id := "ref.get", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_get
        , `Effect4.Machine.refStep_get_after_set ] }
  , { id := "ref.set-void-returns-cell", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_set
        , `Effect4.Machine.set_answer_ne_update_answer ] }
  , { id := "ref.cell-set-returns-self", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_set_answers_self ] }
  , { id := "ref.get-and-set", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_getAndSet ] }
  , { id := "ref.set-and-get-assignment", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_setAndGet ] }
  , { id := "ref.update", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_update
        , `Effect4.Machine.refStep_update_applies_once ] }
  , { id := "ref.modify", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_modify ] }
  , { id := "ref.modify-some-no-reread", kind := "ref", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_modifySome_eq_modify
        , `Effect4.Machine.refStep_modifySome_none ] }
  , { id := "ref.update-some-and-get-reread", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.refStep_updateSomeAndGet_some ] }
  , { id := "deferred.make", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_make ] }
  , { id := "deferred.is-done", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_isDone ] }
  , { id := "deferred.await", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.awaitDeferred_is_a_park
        , `Effect4.Machine.deferredStore_register_pending
        , `Effect4.Machine.deferredStore_register_done ] }
  , { id := "deferred.single-completion", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_complete_done ] }
  , { id := "deferred.completion-order", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_complete_pending
        , `Effect4.Machine.Witnesses.w13_completion_pop_sees_the_waiter_interrupt ] }
  , { id := "deferred.complete-with-stores-effect", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_complete_stores_argument
        , `Effect4.Machine.deferredStore_waiter_receives_stored ] }
  , { id := "deferred.done-is-complete-with", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.doneWith_shared
        , `Effect4.Machine.completionPrim_ofExit ] }
  , { id := "deferred.complete-runs-once", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredStore_complete_done ] }
  , { id := "deferred.into-uninterruptible", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.intoDeferred_spelling ] }
  , { id := "deferred.interrupt", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.interruptDeferred_delegates ] }
  , { id := "deferred.interrupt-with", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.interruptWith_is_completion ] }
  , { id := "deferred.poll", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.deferredPoll_no_write ] }
  , { id := "layer.from-build-unsafe", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileLayer_succeed ] }
  , { id := "layer.from-build-child-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileLayer_effect
        , `Effect4.Program.Agreement.contAOf_fromBuildThen_scope
        , `Effect4.Machine.finProgram_closeChildOnFailure_failure
        , `Effect4.Machine.finProgram_closeChildOnFailure_success ] }
  , { id := "layer.build-with-memo-map-service", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.contAOf_withMemoMapThen_memoMap
        , `Effect4.Program.Agreement.currentMemoMapOf_provideService
        , `Effect4.Program.Agreement.regionCode_buildAdding
        , `Effect4.Program.Agreement.contAOf_addCurrentMemoMap
        , `Effect4.Program.Agreement.addCurrentMemoMapK_context ] }
  , { id := "layer.memo-build-once", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.syncOpStep_memoBuild
        , `Effect4.Program.Agreement.contAOf_memoize_unit
        , `Effect4.Program.Agreement.contAOf_buildIntoLayerScope_scope
        , `Effect4.Program.Agreement.contAOf_thenBuildInto
        , `Effect4.Machine.finProgram_memoDone
        , `Effect4.Machine.syncOpStep_memoComplete_some
        , `Effect4.Program.Agreement.resolveLayerTerm_ref ] }
  , { id := "layer.memo-finalizer-last-observer", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.finProgram_memoEntry
        , `Effect4.Machine.syncOpStep_memoRelease_last
        , `Effect4.Machine.syncOpStep_memoRelease_dec
        , `Effect4.Machine.contAOf_closeIfLast_scope
        , `Effect4.Program.Sched.contAOf_closeIfLast_other
        , `Effect4.Program.Agreement.resolveLayerTerm_ref ] }
  , { id := "layer.memo-reuse-observer-count", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.syncOpStep_memoGet_some
        , `Effect4.Program.Agreement.contAOf_memoize_hit
        , `Effect4.Program.Agreement.resolveLayerTerm_ref ] }
  , { id := "layer.memo-map-parent-lookup", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Machine.MemoWorld.get_own
        , `Effect4.Machine.MemoWorld.get_parent ] }
  , { id := "layer.memo-get-or-else", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.innerLayerAt_effect
        , `Effect4.Program.Agreement.suspendBodyAt_memoLookup
        , `Effect4.Program.Agreement.contAOf_awaitPromise
        , `Effect4.Program.Agreement.contAOf_memoize_hit
        , `Effect4.Program.Agreement.contAOf_memoize_unit ] }
  , { id := "layer.current-memo-map-fork-or-create", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.currentMemoMapOf_addV
        , `Effect4.Program.Agreement.currentMemoMapOf_empty
        , `Effect4.Machine.syncOpStep_memoFork
        , `Effect4.Program.Agreement.buildWithScopeK_context ] }
  , { id := "layer.build-uses-ambient-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.contAOf_buildWithScopeFromContext
        , `Effect4.Program.Agreement.buildWithScopeK_context
        , `Effect4.Program.Agreement.contAOf_serviceLookup
        , `Effect4.Program.Agreement.serviceLookupK_found
        , `Effect4.Program.Agreement.serviceLookupK_missing ] }
  , { id := "layer.build-with-scope-still-forks-memo", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.provideLayerWithK_at
        , `Effect4.Program.Agreement.contAOf_buildWithScopeFromContext
        , `Effect4.Program.Agreement.buildWithScopeK_context ] }
  , { id := "layer.merge-parallel-scopes", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileLayer_merge
        , `Effect4.Program.Agreement.innerLayerAt_merge
        , `Effect4.Program.Agreement.contAOf_mergeChildren_scope
        , `Effect4.Program.Agreement.contAOf_mergeForkOne_scope
        , `Effect4.Program.Agreement.withFiberOf_forkLayer
        , `Effect4.Program.Agreement.contAOf_mergeForkNext_fiber
        , `Effect4.Program.Agreement.innerLayerAt_mergeAll
        , `Effect4.Program.Agreement.mergeAllCount_of_at
        , `Effect4.Program.Agreement.contAOf_mergeAllChildren_scope
        , `Effect4.Program.Agreement.contAOf_mergeAllForkOne_scope
        , `Effect4.Program.Agreement.contAOf_mergeAllForkNext_fiber
        , `Effect4.Program.Agreement.withFiberOf_awaitAllFailFast
        , `Effect4.Program.Agreement.contAOf_mergeContexts
        , `Effect4.Program.Agreement.mergeContextsK_contexts ] }
  , { id := "layer.provide-dependency-first", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileLayer_provide
        , `Effect4.Program.Agreement.compileLayer_provideMerge
        , `Effect4.Program.Agreement.innerLayerAt_provide
        , `Effect4.Program.Agreement.contAOf_provideThen
        , `Effect4.Program.Agreement.provideThenK_context
        , `Effect4.Program.Agreement.regionCode_build
        , `Effect4.Program.Agreement.contAOf_combineWith
        , `Effect4.Program.Agreement.combineWithK_provide
        , `Effect4.Program.Agreement.combineWithK_provideMerge ] }
  , { id := "layer.fresh-drops-memoization", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileLayer_fresh
        , `Effect4.Program.Agreement.contAOf_freshThen_memoMap ] }
  , { id := "layer.launch-holds-scope", kind := "layer", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "then runs never" — `Eff` has no `never`; only the `scopedWith`
      -- frame that holds the built layer's scope until its body exits is witnessed
    , witnesses :=
        [ `Effect4.Program.Agreement.provideLayerWithK_at
        , `Effect4.Program.Agreement.finalizerProgram_scopeClose ] }
  , { id := "layer.provide-effect-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ `Effect4.Program.Agreement.compileEff_provideLayer
        , `Effect4.Program.Agreement.suspendBodyAt_provideLayer
        , `Effect4.Program.Agreement.contAOf_provideLayerWith_scope
        , `Effect4.Program.Agreement.provideLayerWithK_at
        , `Effect4.Program.Agreement.contAOf_provideLayerBody
        , `Effect4.Program.Agreement.provideLayerBodyK_context
        , `Effect4.Program.Agreement.contAOf_updateThen
        , `Effect4.Program.Agreement.updateThenK_context
        , `Effect4.Program.Agreement.contAOf_bodyThen
        , `Effect4.Program.Agreement.finalizerProgram_scopeClose ] }
  ]

/-! ## Checks -/

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"runtime coverage mismatch: {detail}"

private def firstDuplicateString? : List String → Option String
  | [] => none
  | value :: values => if values.contains value then some value else firstDuplicateString? values

private def firstDuplicateName? : List Name → Option Name
  | [] => none
  | name :: names => if names.contains name then some name else firstDuplicateName? names

private def checkRowShape : CommandElabM Unit := do
  if let some duplicate := firstDuplicateString? (censusRows.map Row.id) then
    failJoin m!"duplicate census row id: {duplicate}"
  for row in censusRows do
    unless knownKinds.contains row.kind do
      failJoin m!"row {row.id} has unknown kind {row.kind}"
    unless knownDispositions.contains row.disposition do
      failJoin m!"row {row.id} has a disposition outside the PORT-MANIFEST vocabulary: {row.disposition}"
    unless knownCoverage.contains row.coverage do
      failJoin m!"row {row.id} has unknown coverage {row.coverage}"
    if let some duplicate := firstDuplicateName? row.witnesses then
      failJoin m!"row {row.id} lists witness {duplicate} twice"
    let hasWitness := !row.witnesses.isEmpty
    if row.coverage == "absent" && hasWitness then
      failJoin m!"row {row.id} is declared absent but carries witnesses"
    if row.coverage != "absent" && !hasWitness then
      failJoin m!"row {row.id} is declared {row.coverage} but carries no witness"
    if row.disposition == "owned" && !hasWitness then
      failJoin m!"row {row.id} is owned and must carry at least one witness"
    if excludedDispositions.contains row.disposition && hasWitness then
      failJoin m!"row {row.id} is {row.disposition}, is outside the coverage denominator, and must carry no witness"

/-- Every witness exists and is a theorem. The axiom ceiling is the gate's
(`Test/Audit/AxiomGate.lean`), which audits every declaration, witnesses included. -/
private def checkWitnesses : CommandElabM Unit := do
  let environment ← getEnv
  for row in censusRows do
    for name in row.witnesses do
      match environment.find? name with
      | none => failJoin m!"row {row.id}: missing witness declaration {name}"
      | some (.thmInfo _) => pure ()
      | some info =>
          let statementIsProp ← liftTermElabM <| Meta.isProp info.type
          let kind :=
            if statementIsProp then "a Prop-typed non-theorem declaration" else "not a theorem"
          failJoin m!"row {row.id}: witness {name} is {kind}; a witness must be a theorem"

private def denominatorRows : List Row :=
  censusRows.filter fun row => !excludedDispositions.contains row.disposition

private def checkRuntimeCoverage : CommandElabM Unit := do
  checkRowShape
  checkWitnesses
  let total := censusRows.length
  let denominator := denominatorRows.length
  let excluded := total - denominator
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  let partialIds := (denominatorRows.filter fun row => row.coverage == "partial").map Row.id
  let absentIds := (denominatorRows.filter fun row => row.coverage == "absent").map Row.id
  logInfo m!"Effect v4 runtime coverage: {total} census rows; {excluded} excluded by disposition; denominator {denominator}; owned-with-green {ownedGreen}/{denominator}; green {green}, partial {partial_}, absent {absent}"
  logInfo m!"partial rows: {partialIds}"
  logInfo m!"absent rows: {absentIds}"

private def emitRuntimeCoverage : CommandElabM Unit := do
  checkRuntimeCoverage
  for row in censusRows do
    liftIO <| IO.println
      s!"E4RTCOV\trow\t{row.id}\t{row.kind}\t{row.disposition}\t{row.coverage}\t{row.witnesses.length}"
  for row in censusRows do
    for name in row.witnesses do
      liftIO <| IO.println s!"E4RTCOV\twitness\t{row.id}\t{name}"
  let denominator := denominatorRows.length
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  liftIO <| IO.println
    s!"E4RTCOV\tcoverage\t{censusRows.length}\t{denominator}\t{ownedGreen}\t{green}\t{partial_}\t{absent}"

syntax (name := effect4CheckRuntimeCoverage)
  "#effect4_check_runtime_coverage" : command

syntax (name := effect4EmitRuntimeCoverage)
  "#effect4_emit_runtime_coverage" : command

elab_rules : command
  | `(#effect4_check_runtime_coverage) => checkRuntimeCoverage

elab_rules : command
  | `(#effect4_emit_runtime_coverage) => emitRuntimeCoverage

#effect4_check_runtime_coverage
#effect4_emit_runtime_coverage

end Test.Audit.RuntimeCoverage
