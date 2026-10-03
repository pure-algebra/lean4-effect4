import Effect4.Laws.Program.Simulation.Hooks
import Effect4.Laws.Program.Typed.Commands.Clauses.StoreScope
#print axioms Effect4.Machine.syncOpStep_externals
#print axioms Effect4.Program.Sched.storesOk_syncOpStep
#print axioms Effect4.Program.Typed.Evaluating.store_restate
#print axioms Effect4.Program.Typed.clause_scopeMake
#print axioms Effect4.Program.Typed.clause_scopeAdd
#print axioms Effect4.Program.Typed.clause_scopeRemove
#print axioms Effect4.Program.Typed.clause_scopeFork
#print axioms Effect4.Program.Typed.clause_memoFork
#print axioms Effect4.Program.Typed.clause_memoGet
#print axioms Effect4.Program.Typed.clause_memoRelease
#check @Effect4.Machine.syncOpStep_externals
#check @Effect4.Program.Sched.storesOk_syncOpStep
#check @Effect4.Program.Typed.Evaluating.store_restate
