import Effect4.Program.RuntimeR
import Test.Program.RuntimeRContract

/-! Dependency receipts for R3/R4 as restated by P2, the P1b shared actions and the
frame-arm identities; the whole-tree gate also checks private and generated
declarations. Packet: `Test/contracts/program-runtime-r.contract.md`. -/

#print axioms Effect4.Program.Sched.termCore
#print axioms Effect4.Program.Sched.restoreR
#print axioms Effect4.Program.Sched.denoteAt
#print axioms Effect4.Program.Sched.denoteFin
#print axioms Effect4.Program.Sched.denoteCompletion
#print axioms Effect4.Program.Sched.denoteStored
#print axioms Effect4.Program.Sched.denoteStored_completion
#print axioms Effect4.Program.Sched.denoteCloseSeq
#print axioms Effect4.Program.Sched.denoteClosePar
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
#print axioms Effect4.Program.Sched.finishWith
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
#print axioms Effect4.Program.Sched.evaluateR_sync
#print axioms Effect4.Program.Sched.BehR_fuel_irrelevant
-- P1b (2026-09-06): the shared fiber actions and the frame-arm identities.
#print axioms Effect4.Machine.FiberAction.coreAnswer
#print axioms Effect4.Machine.FiberAction.getId
#print axioms Effect4.Machine.FiberAction.fork
#print axioms Effect4.Machine.FiberAction.forkScoped
#print axioms Effect4.Machine.FiberAction.closeScope
#print axioms Effect4.Machine.FiberAction.interruptThenJoin
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
