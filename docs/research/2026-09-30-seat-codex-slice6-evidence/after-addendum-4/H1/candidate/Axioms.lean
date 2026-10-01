import Effect4.Laws.Program.Typed.Assembly

#print axioms Effect4.Program.Typed.pending_below
#print axioms Effect4.Program.Typed.QueueOk.fresh
#print axioms Effect4.Program.Typed.reifyExitVal_fits
#print axioms Effect4.Program.Typed.observerDeliveredExit_fits
#print axioms Effect4.Program.Typed.observer_exitValue_typed
#print axioms Effect4.Program.Typed.observerCommand_resume_typed
#print axioms Effect4.Program.Typed.requestOfR_load_none
#print axioms Effect4.Program.Typed.schedulerState_load
#print axioms Effect4.Program.Typed.registrationState_load
#print axioms Effect4.Program.Typed.observerState_load

-- These remain obligation wrappers, not command-preservation proofs.
#check Effect4.Program.Typed.M6Ledger.step_evaluate
#check Effect4.Program.Typed.M6Ledger.step_observe
#check Effect4.Program.Typed.M6Ledger.step_wake
