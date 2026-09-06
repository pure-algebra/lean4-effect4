import Effect4.Program.RuntimeR

/-! Dependency receipts for R3/R4; the whole-tree gate also checks private and
generated declarations. Packet: `Test/contracts/program-runtime-r.contract.md`. -/

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
#print axioms Effect4.Program.Sched.interpR
#print axioms Effect4.Program.Sched.bodyR
#print axioms Effect4.Program.Sched.popR
#print axioms Effect4.Program.Sched.deliverR
#print axioms Effect4.Program.Sched.interruptJoinR
#print axioms Effect4.Program.Sched.scopedR
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
#print axioms Effect4.Program.Sched.BehR_fuel_irrelevant
