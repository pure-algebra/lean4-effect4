# Commit 3 theorem axiom receipt

The audit imports the final public fuel and guard law modules, identifies their
source modules (including private and compiler-generated declarations), and
elaborates `#print axioms` for every theorem declaration in those modules.
All 3,590 theorem declarations are within `[propext, Quot.sound]`.
The separate whole-library gate also checks definitions and instances.

Command: `LEAN_NUM_THREADS=2 lake env lean -j2 -M3072 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/c3-axiom-audit.lean`.
Exit: 0. Full output: `c3-axiom-audit-final.log`.

```text
'Effect4.Api.finished_mono_fuel' depends on axioms: [propext, Quot.sound]
'Effect4.Api.guard_persists' depends on axioms: [propext, Quot.sound]
'Effect4.Api.guard_persists_single' depends on axioms: [propext, Quot.sound]
'Effect4.Api.guard_persists_single_tape' depends on axioms: [propext, Quot.sound]
'Effect4.Api.load.eq_1' depends on axioms: [propext]
'Effect4.Api.replay.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.DeferredStore.drainDue.eq_1' does not depend on any axioms
'Effect4.Machine.DeferredStore.make.eq_1' does not depend on any axioms
'Effect4.Machine.Dispatcher.insert.eq_1' does not depend on any axioms
'Effect4.Machine.Dispatcher.insert.eq_2' does not depend on any axioms
'Effect4.Machine.Dispatcher.insert.eq_def' does not depend on any axioms
'Effect4.Machine.FiberAction.outcomeOf.eq_1' does not depend on any axioms
'Effect4.Machine.RunFiber.cleared.eq_1' does not depend on any axioms
'Effect4.Machine.RunFiber.interruptPending.eq_1' does not depend on any axioms
'Effect4.Machine.RunFiber.make.eq_1' does not depend on any axioms
'Effect4.Machine.RunFiber.park.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.emit.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.fiber?.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.modify.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.race?.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.update.eq_1' does not depend on any axioms
'Effect4.Machine.RunMachine.updateRace.eq_1' does not depend on any axioms
'Effect4.Machine.Stores.wakeList._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Machine.WakeList.empty.eq_1' does not depend on any axioms
'Effect4.Machine.WakeList.register.eq_1' does not depend on any axioms
'Effect4.Machine.WakeList.runBatch.eq_1' does not depend on any axioms
'Effect4.Machine.cancelProgram._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Machine.cancelProgram._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Machine.drainOwed.eq_1' does not depend on any axioms
'Effect4.Machine.drainOwed.eq_2' does not depend on any axioms
'Effect4.Machine.drainOwed.eq_def' does not depend on any axioms
'Effect4.Machine.driveStep.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_10' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_11' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_12' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_13' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_14' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_15' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_16' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_17' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_18' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_19' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_2' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_3' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_4' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_5' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_6' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_7' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_8' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveStep.eq_9' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.evaluatePrim.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.forkFinalizers.eq_1' does not depend on any axioms
'Effect4.Machine.forkFinalizers.eq_2' does not depend on any axioms
'Effect4.Machine.forkFinalizers.eq_def' does not depend on any axioms
'Effect4.Machine.interruptEach.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.interruptRecord.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.progOf.eq_def' does not depend on any axioms
'Effect4.Machine.settle.eq_1' does not depend on any axioms
'Effect4.Machine.spawn.eq_1' does not depend on any axioms
'Effect4.Machine.start.eq_1' does not depend on any axioms
'Effect4.Program.Guard.AnswerDecision.guardQueue_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.guardQueue_resume_from_tail' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.guardState_answerAsync' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.guardState_answerDrive' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.guardState_prepareAsyncAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.prepareAsyncAnswer_shape' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.prepareExternalAnswer_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.registrationQueue_resume_result' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.requestOrInterrupted_answerAsync' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.AnswerDecision.requestOrInterrupted_answerDrive' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.CommandAuthority.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_10' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_11' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_3' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_4' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_5' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_6' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_7' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_8' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandAuthority.eq_9' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.CommandControlsPreserved.active' does not depend on any axioms
'Effect4.Program.Guard.CommandControlsPreserved.exited' does not depend on any axioms
'Effect4.Program.Guard.ControlRemainder.interruptedAt_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.interruptedAt_update_mark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_drainOwed' depends on axioms: [propext]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_interruptTarget' depends on axioms: [propext,
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.registrationQueue_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOf_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOf_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOf_driveStep_resume_reserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOf_driveStep_resume_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOf_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOrInterrupted_driveStep_drainDue' depends on axioms: [propext,
'Effect4.Program.Guard.ControlRemainder.requestOrInterrupted_driveStep_evaluate' depends on axioms: [propext,
'Effect4.Program.Guard.ControlRemainder.requestOrInterrupted_driveStep_raceCancel' depends on axioms: [propext,
'Effect4.Program.Guard.ControlRemainder.requestOrInterrupted_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ControlRemainder.requestOrInterrupted_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DeferredCause.DeferredCause.eq_1' does not depend on any axioms
'Effect4.Program.Guard.DeferredCause.evaluateNative_deferredCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DeferredCause.evaluatePrim_deferredCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DeferredCause.exitScoped_deferredCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DeferredCause.finalizerOr_deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.frameExitState_deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.frame_step_deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.frame_step_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.getCont_deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.getCont_deferred_false' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.getCont_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.injectYield_deferredCause' does not depend on any axioms
'Effect4.Program.Guard.DeferredCause.iteration_deferredCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DeferredCause.resumeCause_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.resumeValue_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.runloopTop_deferredCause' does not depend on any axioms
'Effect4.Program.Guard.DeferredCause.stepFrame_deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.DeferredCause.withFiber_deferredCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DriverContract.interrupted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DriverContract.invariant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DriverContract.request' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.DriverContract.reserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FiberGuardState.below' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.codes' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.exited' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.idle' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.parkedBelow' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.pending' depends on axioms: [propext]
'Effect4.Program.Guard.FiberGuardState.tasks' depends on axioms: [propext]
'Effect4.Program.Guard.Finish.fiberGuardState_childExit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.fiberGuardState_publish' depends on axioms: [propext]
'Effect4.Program.Guard.Finish.guardState_childExit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.guardState_cleared' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.guardState_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.guardState_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.guardState_publish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.interruptedAt_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.interruptedAt_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.interruptedAt_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.nextToken_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.requestOf_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.requestOf_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.requestOf_update_unparked_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.reservedKeys_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Finish.reservedKeys_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.controlsAway_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.controlsAway_trans' does not depend on any axioms
'Effect4.Program.Guard.FinishQueue.exitFiber_noOwners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_cons_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_drainDue_single' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_exitDone_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_exitDone_drainDue._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.FinishQueue.guardQueue_exitDone_drainDue._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.FinishQueue.guardQueue_exitFiber_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_exitFiber_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.guardQueue_observe_list' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.observeList_noOwners' depends on axioms: [propext]
'Effect4.Program.Guard.FinishQueue.raceHostsPreserved_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.races_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.registrationQueue_driveStep_finish' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.registrationQueue_exitFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FinishQueue.registrationQueue_observe_list' depends on axioms: [propext]
'Effect4.Program.Guard.FrameCodeOwned.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameCodeOwned.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.answerOf_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.armA_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.armE_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_13' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_14' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_15' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_16' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_17' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_fst_sites._simp_1_18' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.ensure_snd_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.frameSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.frame_step_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_answer_frame_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_answer_frame_sites._simp_1_7' depends on axioms: [propext,
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_10' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_11' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_12' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_13' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_8' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.getCont_sites._simp_1_9' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_10' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_5' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_6' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_7' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.joinPushed_sites._simp_1_8' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_16' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_17' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_18' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_19' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_20' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.passPushed_sites._simp_1_21' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_16' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_17' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_18' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_19' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_20' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popFrom_sites._simp_1_21' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.popSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.raceSites_ofExit' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.resumeCause_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.resumeCause_sites._simp_1_22' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.resumeValue_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.resumeValue_sites._simp_1_22' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.stepSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.stepSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_17' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_18' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_19' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_20' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_21' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_22' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_23' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.FrameProof.step_sites._simp_1_24' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.RaceCodeOwned.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.RaceIdsBelow.eq_1' does not depend on any axioms
'Effect4.Program.Guard.FrameOwned.actionRaceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.actionRaceSites.eq_7' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.beginRace_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.closeScope_hook_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.countdownPark_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.deferredCodes_cellAt' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferredCodes_make' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferredCodes_make._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferredCodes_make._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferredCodes_register' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferredCodes_setCell' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.deferred_register_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_46' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_47' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_48' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_49' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_50' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned._simp_1_51' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_26' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_27' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_28' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_29' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_30' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.evaluatePrim_owned._simp_1_31' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.exitScoped_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.exitValue_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.finalizerOr_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.forkFinalizers_races' does not depend on any axioms
'Effect4.Program.Guard.FrameOwned.frameCodeOwned_of_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.frameCodeOwned_same_races' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.frameCodeOwned_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.frameSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.getCont_frameSites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.hooksNoRace_interpAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.hooksNoRace_interpOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.injectYield_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.iteration_frameOwned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.linkScope_races' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.modify_races' does not depend on any axioms
'Effect4.Program.Guard.FrameOwned.prepareExternalAnswer_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceCodeOwned_beginRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceCodeOwned_of_no_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceCodeOwned_transport' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceHostsPreserved_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceHostsPreserved_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites._sparseCasesOn_3.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_7' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_8' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_9' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites.eq_def' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_actionAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_actionEntrants' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_actionEntrants._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_actionOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_asyncRoute' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_cancelProgram' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_cancelProgramOf' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_closeDone' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_closeScope' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_closeScopeUnsafe' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_closeSeqStep' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_compileEff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_compileEff._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_compileLayer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_compileLayer._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_completion' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_contAOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_contEOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_embed_ofExit' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_finProgram' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_finalizerCode' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_finalizerProgram' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_forkScopedAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_innerLayerAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_ofExit' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_progOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_regionCode' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_resolve' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_resolveLayer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_runStmts' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_runStmts_yieldOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_store_contA' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_store_contE' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_store_iterNext' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.raceSites_suspendBodyAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.raceSites_withFiberOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.race_id_of_lookup' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.race_lookup_fresh' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.race_lookup_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.registerAsync_result_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.registerAsync_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.registerRace_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.replace_current_sites' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.runloopTop_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.stepFrame_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.stepRaceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.stepRaceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.stepRaceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_hook_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.withFiber_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_38' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_39' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_40' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_41' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_42' depends on axioms: [propext]
'Effect4.Program.Guard.FrameOwned.withFiber_owned._simp_1_43' depends on axioms: [propext]
'Effect4.Program.Guard.GuardQueue.authority' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.GuardQueue.codeSites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.GuardQueue.keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.GuardQueue.owners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.GuardState.deferredCause' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.exited' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.fiberIds' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.fibersBelow' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.frameCodes' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.internalCodes' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.keysBelow' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.parkedBelow' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.parkedIdle' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.pendingShape' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.raceHosts' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.raceIds' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.racesBelow' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.requestsBelow' depends on axioms: [propext]
'Effect4.Program.Guard.GuardState.requestsOwned' depends on axioms: [propext]
'Effect4.Program.Guard.Interrupted.eq_1' does not depend on any axioms
'Effect4.Program.Guard.InterruptedAt.eq_1' does not depend on any axioms
'Effect4.Program.Guard.Interruption.Interrupted.eq_1' does not depend on any axioms
'Effect4.Program.Guard.Interruption.evaluateNative_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluateNative_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluateNative_interrupted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluateNative_interruptedCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluatePrim_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluatePrim_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.evaluatePrim_interruptedCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.exitScoped_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.exitScoped_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.exitScoped_interruptedCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.finalizerOr_exit' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.finalizerOr_id' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.finalizerOr_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.frameExitState_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.frame_step_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.getCont_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.injectYield_exit' does not depend on any axioms
'Effect4.Program.Guard.Interruption.injectYield_id' does not depend on any axioms
'Effect4.Program.Guard.Interruption.injectYield_interruptedCause' does not depend on any axioms
'Effect4.Program.Guard.Interruption.interrupted_iff_recorded_or_exit' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.interrupted_of_recorded_or_exit' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.iteration_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.iteration_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.iteration_interrupted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.iteration_interruptedCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.resumeCause_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.resumeValue_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.runloopTop_exit' does not depend on any axioms
'Effect4.Program.Guard.Interruption.runloopTop_id' does not depend on any axioms
'Effect4.Program.Guard.Interruption.runloopTop_interruptedCause' does not depend on any axioms
'Effect4.Program.Guard.Interruption.stepFrame_exit' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.stepFrame_id' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.stepFrame_interruptedCause' depends on axioms: [propext]
'Effect4.Program.Guard.Interruption.withFiber_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.withFiber_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Interruption.withFiber_interruptedCause' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardQueue_evaluate_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_installMiddleware' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_interruptBeforeLoop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_interruptFrom' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_interrupted_emit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.guardState_yieldVerdict' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.interruptBeforeLoop.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.interruptFrom_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.requestOrInterrupted_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.requestOrInterrupted_interruptBeforeLoop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.requestOrInterrupted_interruptFrom' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.LocalDecision.requestOrInterrupted_interrupted_emit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.guardState_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.guardState_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.guardState_settle_iteration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.guardState_settle_native' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.interruptedAt_at_lookup' does not depend on any axioms
'Effect4.Program.Guard.NativeAssembly.interruptedAt_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.interruptedAt_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.interruptedAt_settle_iteration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.interruptedAt_settle_native' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.registrationQueue_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.registrationQueue_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.requestOrInterrupted_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.requestOrInterrupted_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.requestOrInterrupted_settle_iteration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.requestOrInterrupted_settle_native' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.request_other_unparked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.reservedKeys_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.reservedKeys_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.reservedKeys_settle_iteration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeAssembly.reservedKeys_settle_native' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueAssembly.guardQueue_driveStep_deliver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueAssembly.guardQueue_driveStep_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueAssembly.guardQueue_settle_iteration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueAssembly.guardQueue_settle_native' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.controlsAway_refl' does not depend on any axioms
'Effect4.Program.Guard.NativeQueueTail.guardQueue_evaluated_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.guardQueue_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.guardQueue_settle_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.guardQueue_transport_commands' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.iteration_settle_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.native_settle_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeQueueTail.queue_owners_transport' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.arm' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.beginRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.closeUnsafe' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.emit' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.filterObservers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.grow' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.joinPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.middleware' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.observer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.refl' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.registerRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.requests' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.reserved' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.StateStep.start' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.startAfter' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.state' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.store' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.storeFresh' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.tokens' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.StateStep.trans' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.closeScopeUnsafe_state' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.closeScope_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.enterScoped_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.evaluateNative_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.evaluatePrim_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.exitScoped_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.filtered_fiberKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.filtered_internalKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.filtered_lookup' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.filtered_request' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.finalizerOr_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.guardState_appendRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.guardState_appendRace._proof_1_5' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.guardState_appendRace._proof_1_6' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.guardState_appendRace._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.guardState_appendRace._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.guardState_appendRace._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.NativeState.guardState_appendRace._simp_1_4' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.interruptAs_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.iteration_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.registerAsync_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.stepFrame_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.syncState_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeState.withFiber_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.ExternalParkKeys.noExternal' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateExternal.ExternalParkKeys.unparked' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateExternal.async_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.countdown_external' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateExternal.evaluateNative_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.evaluatePrim_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.exitScoped_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.finalizerOr_external' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateExternal.iteration_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.parkOf_noExternal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateExternal.stepFrame_external' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateExternal.withFiber_external' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.arm' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.beginRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.controls' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.emit' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.filterObservers' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.interrupted' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.joinPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.modifyFields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.observer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.races' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.refl' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.registerRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.requests' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.same' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.sameTables' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.Links.start' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.startAfter' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.store' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.Links.trans' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.controls_of_full' does not depend on any axioms
'Effect4.Program.Guard.NativeStateLinks.evaluateNative_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.evaluatePrim_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.exitScoped_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.finalizerOr_links' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.interruptAs_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.iteration_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateLinks.stepFrame_links' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateLinks.withFiber_links' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.countdown_nextId' does not depend on any axioms
'Effect4.Program.Guard.NativeStateMotion.evaluateNative_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.evaluatePrim_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.exitScoped_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.finalizerOr_nextId' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateMotion.forkFinalizers_nextId' does not depend on any axioms
'Effect4.Program.Guard.NativeStateMotion.iteration_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.linkScope_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.NativeStateMotion.modify_nextId' does not depend on any axioms
'Effect4.Program.Guard.NativeStateMotion.stepFrame_nextId' depends on axioms: [propext]
'Effect4.Program.Guard.NativeStateMotion.withFiber_nextId' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.Preserved.disarm' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.drive' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.Preserved.emit' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.interrupted' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.of_eq_requests' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.refl' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.request' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.reserved' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.state' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.Preserved.trans' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.advanceState_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.advanceTick_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.clearDispatcher_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.clockStep_owed_facts' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.clockStep_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_keys._simp_1_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_keys._simp_1_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_keys._simp_1_3' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_sites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_sites._simp_1_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.dispatcher_sites._simp_1_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.fireFold_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.fireState_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.fireStep_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.flushAllState_preserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.guardState_advanceState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.guardState_fireState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.guardState_flushAllState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.interruptedAt_advanceState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.interruptedAt_fireState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.interruptedAt_flushAllState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.requestOrInterrupted_advanceState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.requestOrInterrupted_fireState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.requestOrInterrupted_flushAllState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.reservedKeys_advanceState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.reservedKeys_fireState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.reservedKeys_flushAllState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.taskCmds_guardQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.OuterDriver.taskCmds_guardQueue._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.taskCmds_guardQueue._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.taskCmds_registration' depends on axioms: [propext]
'Effect4.Program.Guard.OuterDriver.timer_clockStep_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.PendingShape.eq_1' does not depend on any axioms
'Effect4.Program.Guard.RaceCodeOwned.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.evaluateNative_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationNested.evaluatePrim_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationNested.exitScoped_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationNested.finalizerOr_registration' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.iteration_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationNested.registrationQueue_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationNested.registrationQueue_map' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.registrationQueue_registerRace' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.registrationQueue_settle' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.stepFrame_registration' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationNested.withFiber_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationQueue.ControlsAway.eq_1' does not depend on any axioms
'Effect4.Program.Guard.RegistrationQueue.RegistrationQueue.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationQueue.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationQueue.eq_def' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationTail._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationTail.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationTail.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.RegistrationTail.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.activeAt_transport_away' does not depend on any axioms
'Effect4.Program.Guard.RegistrationQueue.commandAuthority_transport_away' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationQueue.controlsAway_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationQueue.guardQueue_transport_away' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RegistrationQueue.registrationQueue_append' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.registrationQueue_member' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.registrationQueue_tail' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.registrationTail_mono' depends on axioms: [propext]
'Effect4.Program.Guard.RegistrationQueue.registration_owner_mem' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.RequestView.eq_1' does not depend on any axioms
'Effect4.Program.Guard.ReservedKeys.below' depends on axioms: [propext]
'Effect4.Program.Guard.ReservedKeys.disjoint' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.AllSimple.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.GeneratedQueue.owner' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.GeneratedQueue.queue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.Local._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Local.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.Simple.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.active_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.allSimple_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.allSimple_append._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.allSimple_append._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.allSimple_append._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.allSimple_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.allSimple_map' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.allSimple_nil' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.countdown_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluateNative_commandOwners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluateNative_generatedQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluateNative_guardQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluateNative_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluateNative_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluatePrim_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.evaluatePrim_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.exitScoped_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.exitScoped_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.finalizerOr_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.finalizerOr_present' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_append_one' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_registration' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_registration._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_registration._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_simple' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.generatedQueue_simple._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.injectYield_present' does not depend on any axioms
'Effect4.Program.Guard.ReturnCommands.iteration_commandOwners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.iteration_generatedQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.iteration_guardQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.iteration_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.iteration_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.local_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.lookup_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.present_append' does not depend on any axioms
'Effect4.Program.Guard.ReturnCommands.present_forkFinalizers' does not depend on any axioms
'Effect4.Program.Guard.ReturnCommands.present_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.present_lookup' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.present_map' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.present_modify' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.present_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.registerRace_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.settle_generatedQueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.simple_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.simple_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.simple_owners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.stepFrame_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.stepFrame_present' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnCommands.withFiber_nested' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnCommands.withFiber_present' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.ReadyOutcome.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.countdownPark_unparked' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.countdown_freshPark' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.countdown_ready' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.countdown_readyOf' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.evaluateNative_freshPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluateNative_pending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluateNative_ready' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluateNative_running' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluatePrim_freshPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluatePrim_pending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluatePrim_ready' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.evaluatePrim_running' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.exitScoped_freshPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.exitScoped_pending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.exitScoped_ready' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.exitScoped_running' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.finalizerOr_freshPark' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.finalizerOr_pending' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.finalizerOr_ready' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.finalizerOr_running' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.freshPark_minted' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.freshPark_unparked' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.injectYield_running' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.injectYield_waitFields' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.iteration_freshPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.iteration_pending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.iteration_ready' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.iteration_running' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.pendingShape_of_unparked' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.pendingShape_park' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.runloopTop_parked' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.runloopTop_pending_eq' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.runloopTop_running' does not depend on any axioms
'Effect4.Program.Guard.ReturnFields.stepFrame_freshPark' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.stepFrame_pending' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.stepFrame_ready' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.stepFrame_running' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnFields.withFiber_freshPark' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.withFiber_pending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.withFiber_ready' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnFields.withFiber_running' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.Returned.external' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.Returned.keys' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.Returned.tasks' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.TaskCodes.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.bucketKeys_insert_empty' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.countdown_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluateNative_external_fiberKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluateNative_fiberKeys_refined' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluateNative_fiberKeys_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluateNative_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluateNative_taskRaceSites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.evaluatePrim_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.exitScoped_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.finalizerOr_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.injectYield_dispatch' does not depend on any axioms
'Effect4.Program.Guard.ReturnTasks.iteration_external_fiberKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.iteration_fiberKeys_refined' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.iteration_fiberKeys_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.iteration_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.iteration_taskRaceSites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.returned_rebase' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.returned_same' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.returned_start' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.returned_yield' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.returned_yield._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.ReturnTasks.runloopTop_dispatch' does not depend on any axioms
'Effect4.Program.Guard.ReturnTasks.stepFrame_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.taskCodes_enqueue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.ReturnTasks.withFiber_returned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.active_noExit' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.frameDraft_deferred' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.frameDraft_deferred._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.frameDraft_owned_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.frameDraft_sites_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.guardState_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.interruptedAt_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.iteration_settledFiber_valid' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.native_settledFiber_valid' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.requestOf_settle_other' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.returnedFiber_guardSafe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.returnedFiber_reserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.settledFiber.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.settledFiber_guardSafe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.Settle.settledFiber_id' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.settledFiber_interrupted' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.settledFiber_keys' depends on axioms: [propext]
'Effect4.Program.Guard.Settle.settledFiber_valid' depends on axioms: [propext]
'Effect4.Program.Guard.SettleQueue.controlsAway_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.guardQueue_append_owned' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.guardQueue_fresh_transport' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.guardQueue_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.guardQueue_settle_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.guardQueue_transport_away_reserved' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.nextToken_settle' does not depend on any axioms
'Effect4.Program.Guard.SettleQueue.raceHostsPreserved_settle' does not depend on any axioms
'Effect4.Program.Guard.SettleQueue.races_settle' does not depend on any axioms
'Effect4.Program.Guard.SettleQueue.reservedKeys_settle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SettleQueue.settle_commands_rest' depends on axioms: [propext]
'Effect4.Program.Guard.SettleQueue.settle_machine_rest' depends on axioms: [propext]
'Effect4.Program.Guard.SettleQueue.settledFiber_park' depends on axioms: [propext]
'Effect4.Program.Guard.SettleQueue.updated_same_request' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.Held.key' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.Held.only' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.Held.request' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.NoCancel._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.NoCancel.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.NoCancel.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietCmd.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.QuietQueue.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.clockStep_owed_safe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.clockStep_owed_safe._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.clockStep_storeKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.evaluate_inert' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_advanceState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_disarm' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_drainOwed._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_driveState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_emit' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_executePrefix' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_fireFold' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_fireState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_fireStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_flushAllState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_of_singleton' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_prepareAsyncAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_same_fields' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_steppedBy' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_steppedBy._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_steppedBy._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_update_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.held_withState' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.held_yieldVerdict' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.noCancel_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.only_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.quiet_taskCmds' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.quiet_taskCmds._simp_1_15' depends on axioms: [propext]
'Effect4.Program.Guard.SingleGuard.requestOf_singleton_executePrefix' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.requestOf_singleton_steppedBy' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.requestOf_singleton_takePrefix' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.resume_inert' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.timer_clockStep_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.SingleGuard.timer_fireNext_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.actionRaceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.actionRaceSites.eq_7' depends on axioms: [propext]
'Effect4.Program.Guard.activeAt_transport' does not depend on any axioms
'Effect4.Program.Guard.bucketKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.bucketKeys_insert_mem' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.bucketKeys_insert_mem._simp_1_5' depends on axioms: [propext]
'Effect4.Program.Guard.bucketKeys_insert_mem._simp_1_6' depends on axioms: [propext]
'Effect4.Program.Guard.bucketKeys_insert_mem._simp_1_7' depends on axioms: [propext]
'Effect4.Program.Guard.bucketKeys_insert_mem._simp_1_8' depends on axioms: [propext]
'Effect4.Program.Guard.clock_resume_not_external_key' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.clock_resume_not_external_key._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.codeSites_dueResumes' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandAuthority_owner_active' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandAuthority_transport' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandAuthority_transport_commands' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandControls_activeAt' does not depend on any axioms
'Effect4.Program.Guard.commandControls_interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandControls_update_inactive' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandKeys._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.commandKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.commandKeys.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.commandKeys.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.commandKeys_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandOwner._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_7' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner.eq_8' depends on axioms: [propext]
'Effect4.Program.Guard.commandOwner_transport' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.commandRaceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.commandRaceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.commandRaceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.commandRaceSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.controlsPreserved_cleared' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.controlsPreserved_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.controlsPreserved_setRunning' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.controlsPreserved_spawnAppend' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.controlsPreserved_update_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.controlsPreserved_update_parked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredCodes_cancel' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_cellAt' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_complete' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredCodes_complete._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_complete._simp_1_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredCodes_drainDue' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_make' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_make._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_make._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_register' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_setCell' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_wakeBatch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredCodes_wakeBatch._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.deferredCodes_wakeBatch._simp_1_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredCodes_wakeList' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys.eq_1' does not depend on any axioms
'Effect4.Program.Guard.deferredKeys_cancel_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys_cell' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys_complete_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys_drain_partition' depends on axioms: [propext]
'Effect4.Program.Guard.deferredKeys_due_append' depends on axioms: [propext]
'Effect4.Program.Guard.deferredKeys_make' depends on axioms: [propext]
'Effect4.Program.Guard.deferredKeys_register_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys_setCell_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.deferredKeys_wakeBatch_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.dispatcher_insert_tasks' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.dispatcher_insert_tasks._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.dispatcher_insert_tasks._simp_1_5' depends on axioms: [propext]
'Effect4.Program.Guard.dispatcher_insert_tasks._simp_1_6' depends on axioms: [propext]
'Effect4.Program.Guard.dispatcher_insert_tasks._simp_1_7' depends on axioms: [propext]
'Effect4.Program.Guard.drainOwed_commandKeys' depends on axioms: [propext]
'Effect4.Program.Guard.drainOwed_commandKeys._simp_1_8' depends on axioms: [propext]
'Effect4.Program.Guard.drainOwed_commands' depends on axioms: [propext]
'Effect4.Program.Guard.drainOwed_commands._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.drainOwed_internalKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.driveState_invariants' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.driveStep_invariants' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.driveStep_resume_wrong_key' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.driverContract' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.dueResumes_keys_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.dueResumes_keys_iff._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.executePrefix.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.externalRequest._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.externalRequest._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.externalRequest.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.externalRequest.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.externalRequest_parkOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiberGuardState_children' depends on axioms: [propext]
'Effect4.Program.Guard.fiberGuardState_context' depends on axioms: [propext]
'Effect4.Program.Guard.fiberGuardState_freshChild' depends on axioms: [propext]
'Effect4.Program.Guard.fiberGuardState_interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiberGuardState_observers' depends on axioms: [propext]
'Effect4.Program.Guard.fiberGuardState_pendingMap' depends on axioms: [propext]
'Effect4.Program.Guard.fiberGuardState_reframe' depends on axioms: [propext]
'Effect4.Program.Guard.fiberIds_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiberKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.fiber_id_of_lookup' depends on axioms: [propext]
'Effect4.Program.Guard.fiber_lookup_addObserver_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_interruptRecord_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_nextId_none' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_nextId_none._proof_1_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_spawnAppend_old' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fiber_lookup_update_self' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.fireObserver_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.frameCodeOwned_answer' depends on axioms: [propext]
'Effect4.Program.Guard.frameCodeOwned_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.frameCodeOwned_finalizer' depends on axioms: [propext]
'Effect4.Program.Guard.frameCodeOwned_transport' depends on axioms: [propext]
'Effect4.Program.Guard.fresh_key_not_internal' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_append_noOwners' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_cons_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_cons_loop' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_continue_active' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_drainOwed_rest' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_evaluate._simp_1_22' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_evaluate._simp_1_23' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_evaluate._simp_1_24' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_evaluate._simp_1_25' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_interruptTarget' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_launch._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_launch._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_raceCancel._simp_1_23' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_raceCancel._simp_1_24' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_emit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_fireObserver_countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_halt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_head_fresh' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_launchEntrant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_modify_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_nil' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_observe_keys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_park_internal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_replaceHead' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_restorePending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_snoc_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_snoc_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_swap_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_swap_append._simp_1_1' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_swap_append._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.guardQueue_swap_append._simp_1_3' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_tail' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_trackedChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_transport' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_update_active' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_update_inactive' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_update_internal_active' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardQueue_withState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_addObserver._simp_1_2' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_addObserver._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_addObserver._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_addObserver._simp_1_5' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_arm' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_evaluate._simp_1_22' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_driveStep_evaluate._simp_1_23' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_driveStep_evaluate._simp_1_24' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_driveStep_evaluate._simp_1_25' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_interruptTarget' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_dueResumes' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_emit' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_executePrefix' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_fiber' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_fireObserver_countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_halt' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_increaseTokens' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_launchEntrant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_load' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_modify_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_park_internal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_reachable' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_restorePending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_scopeLinkFiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_setRunning' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_spawnAppend' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_spawnAppend._proof_1_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_spawnAppend._simp_1_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_steppedBy' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_storeFresh' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_trackedChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_update_noExternal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_update_preserved_request' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_update_unparked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_update_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.guardState_withState' depends on axioms: [propext]
'Effect4.Program.Guard.guardState_withStoreKeys' depends on axioms: [propext]
'Effect4.Program.Guard.hooksNoRace_interpAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.hooksNoRace_interpOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeysBelow_load' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeysBelow_prepareExternalAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeysBelow_state_subset' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_fiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_load' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_postTask_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_prepareExternalAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_spawnAppend' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_state_add' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_state_subset' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_store_decomposition' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_updateRace_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_update_add' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_update_add._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.internalKeys_update_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.internalKeys_update_subset._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.interruptEach_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptEach_context' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptEach_lookup_fields' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptRecord_id' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptRecord_interrupted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptRecord_running_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_cleared' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_interruptTarget' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_fireObserver_countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_launchEntrant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_modify_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_park_internal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_restorePending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_spawnAppend' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_trackedChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_update_interruptRecord' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_update_other' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.interruptedAt_update_reframe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.nextToken_drainOwed' does not depend on any axioms
'Effect4.Program.Guard.nextToken_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.nextToken_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.nextToken_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.nextToken_modify' does not depend on any axioms
'Effect4.Program.Guard.nextToken_postTask' does not depend on any axioms
'Effect4.Program.Guard.notKeyAnswer_answer_iff' does not depend on any axioms
'Effect4.Program.Guard.observerKeys._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.observerKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.observerKeys.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.observerKeys.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.pending_lookup_guard' depends on axioms: [propext]
'Effect4.Program.Guard.pending_reserved_noExternal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.prepareExternalAnswer_internal_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceCodeOwned_beginRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceCodeOwned_compileEff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceCodeOwned_of_no_sites' depends on axioms: [propext]
'Effect4.Program.Guard.raceCodeOwned_park_host' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceCodeOwned_transport' depends on axioms: [propext]
'Effect4.Program.Guard.raceHostsPreserved_append' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceHostsPreserved_postTask' does not depend on any axioms
'Effect4.Program.Guard.raceHostsPreserved_spawnAppend' does not depend on any axioms
'Effect4.Program.Guard.raceHostsPreserved_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceIdsBelow_load' depends on axioms: [propext]
'Effect4.Program.Guard.raceIds_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites._sparseCasesOn_3.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_3' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_4' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_5' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_6' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_7' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_8' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_9' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites.eq_def' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_actionAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_actionEntrants' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_actionEntrants._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_actionOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_asyncRoute' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_cancelProgram' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_cancelProgramOf' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_closeDone' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_closeSeqStep' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_compileEff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_compileEff._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_compileLayer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_compileLayer._unary' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_completion' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_contAOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_contEOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_countdownResume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_embed_ofExit' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_exitValue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_finProgram' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_forkScopedAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_innerLayerAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_ofExit' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_progOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_raceSettle' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_regionCode' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_resolve' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_resolveLayer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_runStmts' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_runStmts_yieldOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_store_contA' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_store_contE' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_store_iterNext' depends on axioms: [propext]
'Effect4.Program.Guard.raceSites_suspendBodyAt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.raceSites_withFiberOf' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.race_id_of_lookup' depends on axioms: [propext]
'Effect4.Program.Guard.race_lookup_fresh' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.race_lookup_updateRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reachable_load' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reachable_step' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registerExternal_internal_state' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.registrationQueue_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_advance_zero' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_answer_zero' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_eq_of_fiber_eq' depends on axioms: [propext]
'Effect4.Program.Guard.requestOf_evaluate_zero' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_fireObserver_countdown_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_fireObserver_raceCallback' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_fireObserver_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_installMiddleware' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_interruptEach_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_interruptRecord_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_launchEntrant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_load' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_lookup_internal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_lookup_unparked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_modify_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_of_shape' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_park_internal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_prepareExternalAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_shape' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_spawnAppend' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_trackedChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_internal_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_noExternal_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_other' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_unparked_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_unparked_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_update_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOf_yieldVerdict' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_driveState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_driveStep_interruptTarget' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_fireObserver_countdown' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_steppedBy' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestOrInterrupted_update_other' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsBelow_load' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_external_park' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_load' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_of_same_keys_and_fibers' depends on axioms: [propext]
'Effect4.Program.Guard.requestsOwned_prepareExternalAnswer' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_reachable' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_settle_parked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_state_subset' depends on axioms: [propext]
'Effect4.Program.Guard.requestsOwned_update_disjoint_guard' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_update_fresh_guard' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.requestsOwned_update_unparked' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_addObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_append' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_drainOwed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveState' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_afterInterrupt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_closeParAwait' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_drainDue' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_enrollRace' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_evaluate._simp_1_22' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_driveStep_exitDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_interruptTarget' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_launch' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_link' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_observe' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_raceCancel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_registrationDone' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_resume' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_trackChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_driveStep_wake' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_dueResumes' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_emit' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_fiber' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_fireObserver' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_forkFinalizers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_fresh' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_halt' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_internal' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_interruptEach' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_launchEntrant' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_linkScope' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_modify_view' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_nil' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_of_requests_subset' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_of_same_requests' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_postTask' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_race' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_spawn' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_subset' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_trackedChild' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.reservedKeys_updateRace' depends on axioms: [propext]
'Effect4.Program.Guard.reservedKeys_withState' depends on axioms: [propext]
'Effect4.Program.Guard.scopeLinkFiber_guardStores' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_child_below' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_child_fresh' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_child_lookup' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_child_raceSites' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_machine' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.spawn_parent_unchanged' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.stepRaceSites._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.stepRaceSites.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.stepRaceSites.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.storeKeys.eq_1' does not depend on any axioms
'Effect4.Program.Guard.storeKeys_mono' depends on axioms: [propext]
'Effect4.Program.Guard.syncOpStep_deferredCodes' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.syncOpStep_storeKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.syncOpStep_storeKeys._simp_1_6' depends on axioms: [propext]
'Effect4.Program.Guard.taskKeys._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.Guard.taskKeys.eq_1' depends on axioms: [propext]
'Effect4.Program.Guard.taskKeys.eq_2' depends on axioms: [propext]
'Effect4.Program.Guard.timer_clockStep_key' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.timer_fireNext_key' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.update_all' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.wakeKeys.eq_1' does not depend on any axioms
'Effect4.Program.Guard.wakeKeys_cancel_subset' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Guard.wakeKeys_register_mem' depends on axioms: [propext]
'Effect4.Program.Guard.wakeKeys_register_mem._simp_1_3' depends on axioms: [propext]
'Effect4.Program.Guard.wakeKeys_register_mem._simp_1_4' depends on axioms: [propext]
'Effect4.Program.Guard.wakeKeys_register_mem._simp_1_5' depends on axioms: [propext]
'Effect4.Program.Guard.wakeKeys_runBatch_partition' depends on axioms: [propext]
'Effect4.Program.Guard.wakeKeys_wakeAll_subset' does not depend on any axioms
'Effect4.Program.Guard.wakeList_storeKeys' depends on axioms: [propext, Quot.sound]
'Effect4.Program.actionAt._sparseCasesOn_21.else_eq' depends on axioms: [propext]
'Effect4.Program.actionAt.entrants.eq_1' depends on axioms: [propext]
'Effect4.Program.actionAt.entrants.eq_2' depends on axioms: [propext]
'Effect4.Program.actionAt.entrants.eq_def' depends on axioms: [propext]
'Effect4.Program.addCurrentMemoMapK.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.asyncRoute._sparseCasesOn_10.else_eq' depends on axioms: [propext]
'Effect4.Program.asyncRoute._sparseCasesOn_7.else_eq' depends on axioms: [propext]
'Effect4.Program.bindServiceK.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.bindServiceK.eq_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.buildWithScopeK.eq_1' depends on axioms: [propext]
'Effect4.Program.cancelProgramOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.cancelProgramOf._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.causeOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.causeOf._sparseCasesOn_5.else_eq' depends on axioms: [propext]
'Effect4.Program.combineWithK.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileEff._sparseCasesOn_14.else_eq' depends on axioms: [propext]
'Effect4.Program.compileEff._sparseCasesOn_7.else_eq' depends on axioms: [propext]
'Effect4.Program.compileEff.eq_def' depends on axioms: [propext]
'Effect4.Program.compileLayer._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.compileLayer.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileLayer.eq_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileLayer.eq_3' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileLayer.eq_4' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileLayer.eq_5' depends on axioms: [propext, Quot.sound]
'Effect4.Program.compileLayer.eq_def' depends on axioms: [propext, Quot.sound]
'Effect4.Program.constructionAt._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.constructionAt.eq_1' depends on axioms: [propext]
'Effect4.Program.contAOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.contAOf._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.contEOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.contEOf._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.contextsOfList._sparseCasesOn_3.else_eq' depends on axioms: [propext]
'Effect4.Program.enterScoped.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.evaluateNative._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.evaluateNative._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.evaluateNative._sparseCasesOn_5.else_eq' depends on axioms: [propext]
'Effect4.Program.evaluateNative.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.exitScoped._sparseCasesOn_7.else_eq' depends on axioms: [propext]
'Effect4.Program.exitScoped._sparseCasesOn_8.else_eq' depends on axioms: [propext]
'Effect4.Program.exitScoped._sparseCasesOn_9.else_eq' depends on axioms: [propext]
'Effect4.Program.exitScoped.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.exitScoped.eq_2' depends on axioms: [propext, Quot.sound]
'Effect4.Program.forkScopedAt._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.innerLayerAt._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.interpAt._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.interpAt._sparseCasesOn_10.else_eq' depends on axioms: [propext]
'Effect4.Program.interpAt._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.interpAt._sparseCasesOn_7.else_eq' depends on axioms: [propext]
'Effect4.Program.interpAt.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.interpOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_10.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_13.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_14.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_15.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_18.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_19.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_22.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_23.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_32.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_33.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_40.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf._sparseCasesOn_5.else_eq' depends on axioms: [propext]
'Effect4.Program.interpOf.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.mergeContextsK.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.prepareExternalAnswer._sparseCasesOn_5.else_eq' depends on axioms: [propext]
'Effect4.Program.prepareExternalAnswer._sparseCasesOn_6.else_eq' depends on axioms: [propext]
'Effect4.Program.prepareExternalAnswer._sparseCasesOn_7.else_eq' depends on axioms: [propext]
'Effect4.Program.provideLayerBodyK.eq_1' depends on axioms: [propext]
'Effect4.Program.provideLayerWithK._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.provideLayerWithK.eq_1' depends on axioms: [propext]
'Effect4.Program.provideThenK.eq_1' depends on axioms: [propext]
'Effect4.Program.requestOf._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.requestOf._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.requestOf.eq_1' depends on axioms: [propext]
'Effect4.Program.resolve._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.resolveLayer.resolveLayerTerm._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.resolveLayer.resolveLayerTerm._sparseCasesOn_2.else_eq' depends on axioms: [propext]
'Effect4.Program.runStmts.yieldOf.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.serviceLookupK.eq_1' depends on axioms: [propext]
'Effect4.Program.steppedBy.eq_1' depends on axioms: [propext, Quot.sound]
'Effect4.Program.suspendBodyAt._sparseCasesOn_1.else_eq' depends on axioms: [propext]
'Effect4.Program.suspendBodyAt._sparseCasesOn_4.else_eq' depends on axioms: [propext]
'Effect4.Program.suspendBodyAt._sparseCasesOn_5.else_eq' depends on axioms: [propext]
'Effect4.Program.updateThenK.eq_1' depends on axioms: [propext, Quot.sound]
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Machine.driveStep.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Machine.driveStep.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.AnswerDecision.0.Effect4.Program.prepareExternalAnswer.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Machine.awaitCode.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Machine.awaitCode.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Program.requestOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Continuation.0.Effect4.Program.requestOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.driveStep.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.driveStep.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Program.Guard.RegistrationQueue.RegistrationQueue.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Program.Guard.RegistrationQueue.RegistrationQueue.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Program.Guard.RegistrationQueue.RegistrationTail.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Program.Guard.RegistrationQueue.RegistrationTail.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ControlRemainder.0.Effect4.Program.Guard.RegistrationQueue.RegistrationTail.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.DeferredStore.register.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.DeferredStore.register.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.Dispatcher.insert.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.Dispatcher.insert.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.ScopeStore.addFinalizer.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.ScopeStore.addFinalizer.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.Stores.wakeList.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.Stores.wakeList.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.TimerStore.clockStep.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.TimerStore.clockStep.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.cancelProgram.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.cancelProgram.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.cancelProgram.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.cancelProgram.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.cancelProgram.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.contAOf.match_3.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.drainOwed.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.drainOwed.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.drainOwed.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.drainOwed.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_11.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.driveStep.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.finProgram.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.forkFinalizers.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.forkFinalizers.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.forkFinalizers.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.interruptRecord.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.interruptRecord.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.launchEntrant.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_25' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_26' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_27' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.progOf.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_9.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Machine.syncOpStep.match_9.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandKeys.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandKeys.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandKeys.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.commandOwner.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.externalRequest.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.externalRequest.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.observerKeys.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.observerKeys.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.observerKeys.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.raceSites.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.spawnedChild.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.spawnedChild.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.spawnedChild.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.stepRaceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.Guard.stepRaceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.entrants.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.entrants.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_11.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_11.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_13.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_13.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_15.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_15.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_17.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_17.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_19.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_21.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_9.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.actionAt.match_9.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_10.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.asyncRoute.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.bindServiceK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.bindServiceK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.cancelProgramOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.cancelProgramOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.cancelProgramOf.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.cancelProgramOf.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.causeOf.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.causeOf.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.combineWithK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.combineWithK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_12.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_12.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_21' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_22' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_23' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_24' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_25' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_26' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_27' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_28' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_14.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_5.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileEff.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileLayer.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileLayer.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileLayer.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileLayer.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.compileLayer.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.constructionAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.constructionAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.constructionAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_21' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_22' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_23' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_24' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_25' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_26' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_27' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_28' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_29' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_30' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_31' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_32' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_33' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_34' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_35' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_36' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_37' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_38' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_39' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_40' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_41' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_42' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_43' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_44' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_45' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_46' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_47' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_48' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_49' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_50' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_51' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_52' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_53' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_54' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_55' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_56' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_57' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_58' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_59' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contAOf.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.contEOf.match_4.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.forkScopedAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.forkScopedAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.innerLayerAt.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_13.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_13.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_13.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_18.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_22.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_22.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_22.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_30.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_30.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_32.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_32.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_32.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_32.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_32.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_40.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_40.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_40.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_40.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_40.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_43.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_43.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_45.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_45.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_47.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_47.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_5.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.interpOf.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.mergeContextsK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.mergeContextsK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.mergeContextsK.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.mergeContextsK.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.prepareExternalAnswer.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.provideLayerBodyK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.provideLayerBodyK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.provideLayerWithK.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.provideLayerWithK.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.requestOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.requestOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolve.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolve.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_3.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_6.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_6.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.runStmts.match_8.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.serviceLookupK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.serviceLookupK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.suspendBodyAt.match_4.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.updateThenK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Effect4.Program.updateThenK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.List.filter.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.List.filter.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.List.filterMap.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.List.filterMap.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Option.getD.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Core.0.Option.getD.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.pendingCause.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.pendingCause.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.resumeValue.match_3.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.FrameFiber.step.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.frameExitState.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.frameExitState.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.DeferredCause.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Finish.0.Effect4.Program.requestOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Finish.0.Effect4.Program.requestOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Finish.0.Option.bind.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Finish.0.Option.bind.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.joinPushed.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.joinPushed.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.passPushed.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.passPushed.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.passPushed.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.passPushed.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.pendingCause.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.pendingCause.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.resumeValue.match_3.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.FrameFiber.step.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.cancelProgram.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.cancelProgram.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.cancelProgram.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.cancelProgram.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.cancelProgram.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.contAOf.match_3.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.finProgram.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.frameExitState.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.frameExitState.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_25' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_26' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_27' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.progOf.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Prim.answerOf.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Prim.answerOf.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.answerSites.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.stepSites.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.FrameProof.stepSites.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.actionRaceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.stepRaceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.Guard.FrameOwned.stepRaceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.entrants.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.entrants.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_11.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_11.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_13.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_13.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_15.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_15.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_17.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_17.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_19.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_21.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_9.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.actionAt.match_9.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_10.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.asyncRoute.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.bindServiceK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.bindServiceK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.cancelProgramOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.cancelProgramOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.cancelProgramOf.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.cancelProgramOf.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.causeOf.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.causeOf.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.combineWithK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.combineWithK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_12.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_12.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_21' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_22' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_23' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_24' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_25' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_26' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_27' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_28' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_14.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_5.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileEff.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileLayer.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileLayer.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileLayer.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileLayer.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.compileLayer.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.constructionAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.constructionAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.constructionAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_12' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_13' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_14' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_15' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_16' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_17' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_18' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_19' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_20' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_21' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_22' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_23' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_24' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_25' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_26' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_27' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_28' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_29' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_30' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_31' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_32' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_33' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_34' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_35' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_36' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_37' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_38' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_39' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_40' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_41' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_42' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_43' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_44' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_45' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_46' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_47' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_48' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_49' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_50' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_51' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_52' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_53' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_54' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_55' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_56' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_57' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_58' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_59' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contAOf.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.contEOf.match_4.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.forkScopedAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.forkScopedAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.innerLayerAt.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_13.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_13.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_13.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_18.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_22.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_22.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_22.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_30.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_30.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_32.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_32.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_32.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_32.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_32.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_40.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_40.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_40.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_40.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_40.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_43.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_43.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_45.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_45.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_47.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_47.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_5.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.interpOf.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.mergeContextsK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.mergeContextsK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.mergeContextsK.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.mergeContextsK.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.prepareExternalAnswer.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.provideLayerBodyK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.provideLayerBodyK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.provideLayerWithK.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.provideLayerWithK.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolve.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolve.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.resolveLayer.resolveLayerTerm.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_3.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_6.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_6.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.runStmts.match_8.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.serviceLookupK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.serviceLookupK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.suspendBodyAt.match_4.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.updateThenK.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.FrameOwned.0.Effect4.Program.updateThenK.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.pendingCause.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.pendingCause.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.resumeValue.match_3.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.FrameFiber.step.match_1.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.frameExitState.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.frameExitState.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Interruption.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.LocalDecision.0.Effect4.Program.requestOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.LocalDecision.0.Effect4.Program.requestOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeQueueTail.0.List.filterMap.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeQueueTail.0.List.filterMap.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Machine.storesCloseScopeUnsafe.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.Guard.actionRaceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_13.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_13.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_13.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_18.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_22.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_22.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_22.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_30.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_30.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_32.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_32.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_32.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_32.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_32.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_40.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_40.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_40.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_40.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_40.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_43.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_43.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_45.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_45.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_47.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_47.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_5.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeState.0.Effect4.Program.interpOf.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpAt.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_13.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_13.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_13.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_18.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_22.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_22.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_22.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_30.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_30.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_32.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_32.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_32.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_32.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_32.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_40.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_40.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_40.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_40.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_40.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_43.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_43.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_45.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_45.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_47.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_47.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_5.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateExternal.0.Effect4.Program.interpOf.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateLinks.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.finishFrame.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.NativeStateMotion.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.fireObserver.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.interruptRecord.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.interruptRecord.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Program.Guard.guardQueue_fireObserver.match_1_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Program.Guard.guardQueue_fireObserver.match_1_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Program.Guard.guardState_fireObserver.match_1_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Observer.0.Effect4.Program.Guard.guardState_fireObserver.match_1_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.OuterDriver.0.Effect4.Machine.driveStep.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.OuterDriver.0.Effect4.Machine.driveStep.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.OuterDriver.0.Effect4.Program.Guard.taskKeys.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.OuterDriver.0.Effect4.Program.Guard.taskKeys.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.driveStep.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.driveStep.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.fireObserver.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.fireObserver.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.forkFinalizers.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.forkFinalizers.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Race.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_10.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_10.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_13.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_13.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_13.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_18.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_22.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_22.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_22.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_30.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_30.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_32.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_32.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_32.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_32.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_32.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_40.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_40.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_40.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_40.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_40.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_43.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_43.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_45.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_45.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_47.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_47.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_5.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_5.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_5.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_8.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationDone.0.Effect4.Program.interpOf.match_8.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.interruptEach.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationNested.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.RegistrationQueue.0.List.filterMap.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.RegistrationQueue.0.List.filterMap.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.linkScope.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.linkScope.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.linkScope.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.linkScope.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.linkScope.match_3.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_10' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_11' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.CommandAuthority.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Local.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Local.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Local.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Local.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Local.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.ReturnCommands.Simple.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.commandRaceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.commandRaceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.Guard.commandRaceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnCommands.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.FrameFiber.pendingCause.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.FrameFiber.pendingCause.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.RunMachine.modify.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.RunMachine.modify.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnFields.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.countdownPark.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.countdownPark.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.countdownWalk.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.countdownWalk.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.finalizerOr.match_3.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.interruptAs.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_10.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_10.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_10.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_10.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_10.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_12.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_12.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_12.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_7.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_7.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.match_7.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_17.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_21.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_24.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_10' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_11' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_12' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_13' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_14' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_15' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_16' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_17' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_18' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_19' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_20' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_21' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_22' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_23' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_24' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_4' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_5' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_6' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_7' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_8' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_26.eq_9' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.evaluatePrim.withFiber.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.registerRace.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.registerRace.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.spawn.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.spawn.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Machine.spawn.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_4.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_4.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_4.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.evaluateNative.match_4.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_3.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_3.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_5.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_5.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_7.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.ReturnTasks.0.Effect4.Program.exitScoped.match_7.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.FrameOwned.raceSites.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_6' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_7' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_8' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Settle.0.Effect4.Program.Guard.raceSites.match_1.eq_9' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.SettleQueue.0.List.filterMap.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.SettleQueue.0.List.filterMap.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.advanceState.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.advanceState.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.driveState.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.driveState.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.driveState.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.driveStep.match_7.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.driveStep.match_7.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.flushAllState.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.flushAllState.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.taskCmds.match_1.eq_1' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.taskCmds.match_1.eq_2' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Machine.taskCmds.match_1.eq_3' does not depend on any axioms
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.NoCancel.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.NoCancel.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.QuietCmd.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.QuietCmd.match_1.eq_2' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.QuietCmd.match_1.eq_3' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.QuietCmd.match_1.eq_4' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.SingleGuard.QuietCmd.match_1.eq_5' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.taskKeys.match_1.eq_1' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Guard.Single.0.Effect4.Program.Guard.taskKeys.match_1.eq_2' depends on axioms: [propext]
'guard.congr_simp' does not depend on any axioms
'guard.eq_1' does not depend on any axioms
```
