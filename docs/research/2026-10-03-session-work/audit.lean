import Effect4.Laws.Run

#print axioms Effect4.Api.isRunnable
#print axioms Effect4.Api.runnableFibers
#print axioms Effect4.Api.mem_runnableFibers
#print axioms Effect4.Run.Work
#print axioms Effect4.Run.instDecidableEqWork
#print axioms Effect4.Run.work
#print axioms Effect4.Run.nextControl
#print axioms Effect4.Run.controlOnce
#print axioms Effect4.Run.work_runnable_mem
#print axioms Effect4.Run.work_queued
#print axioms Effect4.Run.work_waits
#print axioms Effect4.Run.nextControl_spec
#print axioms Effect4.Run.nextControl_none_iff
#print axioms Effect4.Run.nextControl_evaluate_mem
#print axioms Effect4.Run.controlOnce_none
#print axioms Effect4.Run.controlOnce_some
#print axioms Effect4.Run.controlOnce_journal

#check Effect4.Run.nextControl_spec
#check Effect4.Run.nextControl_none_iff
#check Effect4.Run.controlOnce_journal
