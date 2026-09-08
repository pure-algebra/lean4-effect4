import Effect4.Laws.Program.RuntimeR
import Test.Program.RuntimeRContract
import Test.Program.SimulationContract

#print axioms Test.Program.SimulationContract.ScopeRegistrationCollision.typed_one
#print axioms Test.Program.SimulationContract.ScopeRegistrationCollision.typed_two

/-! Dependency receipts for R3/R4 as restated by P2, the P1b shared actions and the
frame-arm identities, and (2026-09-07) the P3 relation, its introduction, the concrete
hook and evaluator agreements, the command driver, `run_eq_ref` and the P4 straight
corollary; the whole-tree gate also checks private and generated declarations.
Packet: `Test/contracts/program-runtime-r.contract.md`. -/

#print axioms Effect4.Program.Sched.termCore
#print axioms Effect4.Program.Sched.restoreR
#print axioms Effect4.Program.Sched.denoteAt
#print axioms Effect4.Program.Sched.denoteFin
#print axioms Effect4.Program.Sched.denoteCompletion
#print axioms Effect4.Program.Sched.denoteStored
#print axioms Effect4.Program.Sched.denoteStored_completion
#print axioms Effect4.Program.Sched.closeWalkR
#print axioms Effect4.Program.Sched.closeSeqStepR
#print axioms Effect4.Program.Sched.exitR
#print axioms Effect4.Program.Sched.closeScopeR
#print axioms Effect4.Program.Sched.denoteBody
#print axioms Effect4.Program.Sched.denoteRaceSettle
#print axioms Effect4.Program.Sched.denoteStoreCancel
#print axioms Effect4.Program.Sched.denoteCancel
#print axioms Effect4.Program.Sched.walkR
#print axioms Effect4.Program.Sched.interpR
#print axioms Effect4.Program.Sched.bodyR
#print axioms Effect4.Program.Sched.popR
#print axioms Effect4.Program.Sched.deliverR
#print axioms Effect4.Program.Sched.saveAnswerR
#print axioms Effect4.Program.Sched.answerWith
#print axioms Effect4.Program.Sched.evaluateFiberR
#print axioms Effect4.Program.Sched.evaluateR
#print axioms Effect4.Program.Sched.termEvaluator
#print axioms Effect4.Program.Sched.loadR
#print axioms Effect4.Program.Sched.obsR
#print axioms Effect4.Program.Sched.replayR
#print axioms Effect4.Program.Sched.SufficientR
#print axioms Effect4.Program.Sched.BehR
#print axioms Effect4.Program.Sched.loadR_current
#print axioms Effect4.Program.Sched.obsR_load
#print axioms Effect4.Program.Sched.interpR_answerCode
#print axioms Effect4.Program.Sched.interpR_body
#print axioms Effect4.Program.Sched.evaluateR_pure
#print axioms Effect4.Program.Sched.evaluateR_frontier
#print axioms Effect4.Program.Sched.evaluateR_store
#print axioms Effect4.Program.Sched.evaluateR_store_missing
#print axioms Effect4.Program.Sched.evaluateR_suspend
#print axioms Effect4.Program.enterScoped
#print axioms Effect4.Program.exitScoped
#print axioms Effect4.Program.evaluateNative
#print axioms Effect4.Program.Sched.prepareScopedExitR
#print axioms Effect4.Program.Sched.closeScopeUnsafeR
#print axioms Test.Program.RuntimeRContract.scopedTimingViews
#print axioms Test.Program.RuntimeRContract.scopedPrefixViews
#print axioms Test.Program.RuntimeRContract.scopedCompletionInterrupt
#print axioms Effect4.Program.Sched.evaluateR_sync
#print axioms Effect4.Program.Sched.BehR_fuel_irrelevant
#print axioms Effect4.Program.interpAt
#print axioms Effect4.Program.evaluatorFor
#print axioms Effect4.Program.Sched.interpRAt
#print axioms Effect4.Program.Sched.prepareIterR
#print axioms Effect4.Program.Sched.termEvaluatorFor
#print axioms Test.Program.RuntimeRContract.constructionViewsAgree
#print axioms Effect4.Machine.finalizerCode
#print axioms Test.Program.RuntimeRContract.finalizer_success_code
#print axioms Test.Program.RuntimeRContract.finalizer_failure_code
#print axioms Test.Program.RuntimeRContract.finalizerTimingViews
-- P1b (2026-09-06): the shared fiber actions and the frame-arm identities.
#print axioms Effect4.Machine.FiberAction.coreAnswer
#print axioms Effect4.Machine.FiberAction.getId
#print axioms Effect4.Machine.FiberAction.fork
#print axioms Effect4.Machine.FiberAction.forkScoped
#print axioms Effect4.Machine.FiberAction.closeScope
#print axioms Effect4.Machine.FiberAction.interrupt
#print axioms Effect4.Machine.FiberAction.interruptAs
#print axioms Effect4.Machine.FiberAction.interruptScoped
#print axioms Effect4.Machine.FiberAction.interruptAll
#print axioms Effect4.Machine.FiberAction.raceAll
#print axioms Effect4.Machine.FiberAction.yieldNow
#print axioms Effect4.Machine.FiberAction.join
#print axioms Test.Program.RuntimeRContract.frame_getId
#print axioms Test.Program.RuntimeRContract.frame_fork
#print axioms Test.Program.RuntimeRContract.frame_interruptScoped
#print axioms Test.Program.RuntimeRContract.frame_raceAll
#print axioms Test.Program.RuntimeRContract.frame_yieldNow
#print axioms Test.Program.RuntimeRContract.frame_join
#print axioms Test.Program.RuntimeRContract.term_join
-- P2 (2026-09-06): the scheduling witnesses and the first local relation clause.
#print axioms Test.Program.RuntimeRContract.store_step_rel
#print axioms Test.Program.RuntimeRContract.entry_is_counted

#print axioms Test.Program.RuntimeRContract.getIdSucc
#print axioms Test.Program.RuntimeRContract.native_id_value

#print axioms Test.Program.RuntimeRContract.numericInterruptor

-- P3 (2026-09-07): the generic book, the native relation and its introduction.
#print axioms Effect4.Machine.BookMeans
#print axioms Effect4.Machine.FiberMeans
#print axioms Effect4.Machine.CmdMeans
#print axioms Effect4.Machine.StepAgrees
#print axioms Effect4.Machine.HooksAgree
#print axioms Effect4.Machine.ReplayRel
#print axioms Effect4.Machine.book_driveState
#print axioms Effect4.Machine.book_stepDecisionState
#print axioms Effect4.Machine.book_replayEval
#print axioms Effect4.Machine.book_suffices
#print axioms Effect4.Machine.bookMeans_obs
#print axioms Effect4.Program.Sched.CodeMeans
#print axioms Effect4.Program.Sched.Means
#print axioms Effect4.Program.Sched.StackMeans
#print axioms Effect4.Program.Sched.code_intro
#print axioms Effect4.Program.Sched.resolve_intro
#print axioms Effect4.Program.Sched.compile_intro
#print axioms Effect4.Program.Sched.finalizer_intro
-- P3: the concrete agreements — the walk, delivery, every evaluator arm, the hooks, the
-- shared actions and the command driver — and the invariant.
#print axioms Effect4.Program.Sched.walk_rel
#print axioms Effect4.Program.Sched.deliver_rel
#print axioms Effect4.Program.Sched.evaluate_rel
#print axioms Effect4.Program.Sched.interruptRecord_rel
#print axioms Effect4.Program.Sched.hooksAgree_of
#print axioms Effect4.Program.Sched.spawn_rel
#print axioms Effect4.Program.Sched.linkScope_rel
#print axioms Effect4.Program.Sched.settle_rel
#print axioms Effect4.Program.Sched.iteration_rel
#print axioms Effect4.Program.Sched.fireObserver_rel
#print axioms Effect4.Program.Sched.exitFiber_rel
#print axioms Effect4.Program.Sched.evaluateNative_pendingOk
#print axioms Effect4.Program.Sched.iteration_pendingOk
#print axioms Effect4.Program.Sched.stepAgrees
-- P3: the judgment.
#print axioms Effect4.Program.Sched.load_ok
#print axioms Effect4.Program.Sched.load_rel
#print axioms Effect4.Program.Sched.replay_rel
#print axioms Effect4.Program.Sched.run_eq_ref
#print axioms Effect4.Program.Sched.run_eq_ref_exit
#print axioms Effect4.Program.Sched.suffices_eq_ref
#print axioms Effect4.Program.Sched.beh_eq_ref
#print axioms Test.Program.SimulationContract.ref_agrees
#print axioms Test.Program.SimulationContract.ref_suffices
#print axioms Test.Program.SimulationContract.ref_load_related
-- P4 (2026-09-07): the straight corollary at the fixed budget.
#print axioms Effect4.Program.Sched.straight_ref
#print axioms Effect4.Program.Sched.straight_sufficient
#print axioms Effect4.Program.Sched.straight_beh
#print axioms Test.Program.SimulationContract.straight_pOnExit
#print axioms Test.Program.SimulationContract.straight_pRefSet
#print axioms Test.Program.SimulationContract.straight_pOnExit_sufficient
