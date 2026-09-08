import Effect4.Laws.Machine.Approximation

/-!
# Approximation kernel dependency report

Every declaration of `src/Effect4/Laws/Machine/Approximation.lean` (review
`docs/research/2026-09-05-effects-papers-review.md` §3 G2, packet
`Test/contracts/machine-approximation.contract.md`) is listed exactly once, in module order.
The accepted ceiling is no dependency, `propext`, or `propext` with `Quot.sound`;
`Classical.choice` and project-local axioms are not admitted. The gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

/-! ## APPROX/loop — the loop with its residue -/

#print axioms Effect4.Machine.driveStep
#print axioms Effect4.Machine.driveState
#print axioms Effect4.Machine.drive_succ_cons
#print axioms Effect4.Machine.drive_zero
#print axioms Effect4.Machine.drive_nil
#print axioms Effect4.Machine.drive_stuck
#print axioms Effect4.Machine.driveState_zero
#print axioms Effect4.Machine.driveState_nil
#print axioms Effect4.Machine.driveState_succ_cons
#print axioms Effect4.Machine.driveState_stuck
#print axioms Effect4.Machine.drive_eq_driveState
#print axioms Effect4.Machine.driveState_add
#print axioms Effect4.Machine.drive_add
#print axioms Effect4.Machine.drive_stable_of_done
#print axioms Effect4.Machine.drive_stable_of_stuck
#print axioms Effect4.Machine.driveState_done_add

/-! ## APPROX/trace — the trace only grows -/

#print axioms Effect4.Machine.RunMachine.Extends
#print axioms Effect4.Machine.RunMachine.Extends.refl
#print axioms Effect4.Machine.RunMachine.Extends.trans
#print axioms Effect4.Machine.RunMachine.Extends.exists
#print axioms Effect4.Machine.RunMachine.emit_trace
#print axioms Effect4.Machine.RunMachine.update_trace
#print axioms Effect4.Machine.RunMachine.modify_trace
#print axioms Effect4.Machine.RunMachine.halt_trace
#print axioms Effect4.Machine.RunMachine.updateRace_trace
#print axioms Effect4.Machine.RunMachine.arm_trace
#print axioms Effect4.Machine.RunMachine.disarm_trace
#print axioms Effect4.Machine.RunMachine.Grows
#print axioms Effect4.Machine.RunMachine.Grows.refl
#print axioms Effect4.Machine.spawn_grows
#print axioms Effect4.Machine.start_grows
#print axioms Effect4.Machine.interruptEach_grows
#print axioms Effect4.Machine.countdownPark_grows
#print axioms Effect4.Machine.linkScope_grows
#print axioms Effect4.Machine.launchEntrant_grows
#print axioms Effect4.Machine.injectYield_extends
#print axioms Effect4.Machine.fireObserver_grows
#print axioms Effect4.Machine.fireObserver_fold_grows
#print axioms Effect4.Machine.exitFiber_grows
#print axioms Effect4.Machine.finishFrame_extends
#print axioms Effect4.Machine.stepFrame_extends
#print axioms Effect4.Machine.finalizerOr_extends
#print axioms Effect4.Machine.interruptAs_extends
#print axioms Effect4.Machine.withFiber_extends
#print axioms Effect4.Machine.evaluatePrim_extends
#print axioms Effect4.Machine.iteration_extends
#print axioms Effect4.Machine.settle_grows
#print axioms Effect4.Machine.driveStep_grows
#print axioms Effect4.Machine.drive_extends
#print axioms Effect4.Machine.drive_trace_extends
#print axioms Effect4.Machine.fire_extends
#print axioms Effect4.Machine.fireStep_extends
#print axioms Effect4.Machine.fireTasks_extends
#print axioms Effect4.Machine.fire_trace_extends
#print axioms Effect4.Machine.flushAll_extends
#print axioms Effect4.Machine.flushAll_trace_extends
#print axioms Effect4.Machine.flushRoot_extends
#print axioms Effect4.Machine.flushRoot_trace_extends
#print axioms Effect4.Machine.stepDecision_extends
#print axioms Effect4.Machine.stepDecision_trace_extends
#print axioms Effect4.Machine.ReplayResult.machine
#print axioms Effect4.Machine.replayEval_extends
#print axioms Effect4.Machine.replayEval_trace_extends
#print axioms Effect4.Machine.drive_trace_mono

/-! ## APPROX/order — the order on replay results -/

#print axioms Effect4.Machine.ReplayResult.le
#print axioms Effect4.Machine.ReplayResult.terminal
#print axioms Effect4.Machine.ReplayResult.le_refl
#print axioms Effect4.Machine.ReplayResult.le_trans
#print axioms Effect4.Machine.ReplayResult.le_antisymm_terminal
#print axioms Effect4.Machine.ReplayResult.frontier_le
#print axioms Effect4.Machine.replayEval_nil_machine
#print axioms Effect4.Machine.replayEval_single_machine

/-! ## APPROX/receipts — what a decision ran, and whether its fuel sufficed -/

#print axioms Effect4.Machine.settled
#print axioms Effect4.Machine.driveState_settled_add
#print axioms Effect4.Machine.drive_stable_of_settled
#print axioms Effect4.Machine.taskCmds
#print axioms Effect4.Machine.fireStep
#print axioms Effect4.Machine.fireState
#print axioms Effect4.Machine.fireTasks_stopped
#print axioms Effect4.Machine.fire_eq_fireState
#print axioms Effect4.Machine.fireTasks_false
#print axioms Effect4.Machine.fireTasks_stable
#print axioms Effect4.Machine.fireState_stable
#print axioms Effect4.Machine.fire_stable
#print axioms Effect4.Machine.fireTasks_trace_mono
#print axioms Effect4.Machine.fire_trace_mono
#print axioms Effect4.Machine.flushAll_trace_mono
#print axioms Effect4.Machine.flushAllState
#print axioms Effect4.Machine.flushAll_eq_flushAllState
#print axioms Effect4.Machine.flushAllState_stable
#print axioms Effect4.Machine.flushAll_stable
#print axioms Effect4.Machine.flushRootState
#print axioms Effect4.Machine.flushRoot_eq_flushRootState
#print axioms Effect4.Machine.flushRootState_stable
#print axioms Effect4.Machine.flushRoot_stable
#print axioms Effect4.Machine.stepDecisionState
#print axioms Effect4.Machine.stepDecisionState.loop
#print axioms Effect4.Machine.stepDecision_eq_state
#print axioms Effect4.Machine.stepDecisionState_stable
#print axioms Effect4.Machine.stepDecision_stable

/-! ## APPROX/laws — sufficiency, stability, monotonicity, the colimit -/

#print axioms Effect4.Machine.Suffices
#print axioms Effect4.Machine.Suffices_of_replay_terminal
#print axioms Effect4.Machine.replay_stable
#print axioms Effect4.Machine.Suffices_mono
#print axioms Effect4.Machine.Suffices_of_le
#print axioms Effect4.Machine.replay_obs_mono_of_suffices
#print axioms Effect4.Machine.SingleLoop
#print axioms Effect4.Machine.stepDecision_trace_mono
#print axioms Effect4.Machine.stepDecision_trace_mono_all
#print axioms Effect4.Machine.replay_obs_mono
#print axioms Effect4.Machine.stepDecision_stuck_stable
#print axioms Effect4.Machine.replay_frontier_mono_single
#print axioms Effect4.Machine.replay_stuck_mono_single
#print axioms Effect4.Machine.leastUpTo
#print axioms Effect4.Machine.leastUpTo_none
#print axioms Effect4.Machine.leastUpTo_sound
#print axioms Effect4.Machine.leastUpTo_le
#print axioms Effect4.Machine.leastUpTo_least
#print axioms Effect4.Machine.leastUpTo_isSome
#print axioms Effect4.Machine.leastUpTo_bound_mono
#print axioms Effect4.Machine.leastSufficient
#print axioms Effect4.Machine.leastSufficient_sound
#print axioms Effect4.Machine.leastSufficient_least
#print axioms Effect4.Machine.leastSufficient_le
#print axioms Effect4.Machine.leastSufficient_bound_mono
#print axioms Effect4.Machine.leastSufficient_isSome
#print axioms Effect4.Machine.replay_colimit
#print axioms Effect4.Machine.replay_colimit_eq_of_sufficient
