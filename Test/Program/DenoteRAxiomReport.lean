import Effect4.Laws.Program.DenoteR
import Test.Program.DenoteRContract

/-! Fresh dependency receipts for R2 as restated by P2; the whole-tree gate enforces the
ceiling. -/

#print axioms Effect4.Program.Sched.FrontierReason
#print axioms Effect4.Program.Sched.FiberOp.answer
#print axioms Effect4.Program.Sched.pending
#print axioms Effect4.Program.Sched.guardR
#print axioms Effect4.Program.Sched.onExitR
#print axioms Effect4.Program.Sched.suspendR
#print axioms Effect4.Program.Sched.storeR
#print axioms Effect4.Program.Sched.fiberValR
#print axioms Effect4.Program.Sched.controlErasure
#print axioms Effect4.Program.Sched.eraseControl
#print axioms Effect4.Program.Sched.eraseControl_pure
#print axioms Effect4.Program.Sched.eraseControl_bind
#print axioms Effect4.Program.Sched.eraseControl_guardR
#print axioms Effect4.Program.Sched.eraseControl_onExitR
#print axioms Effect4.Program.Sched.eraseControl_suspendR
#print axioms Effect4.Program.Sched.eraseControl_sync
#print axioms Effect4.Program.Sched.constructR
#print axioms Effect4.Program.Sched.prepareR
#print axioms Effect4.Program.Sched.eraseControl_constructR
#print axioms Effect4.Program.Sched.denoteAction
#print axioms Effect4.Program.Sched.denoteAsync
#print axioms Effect4.Program.Sched.inlineYield
#print axioms Effect4.Program.Sched.denoteR
#print axioms Effect4.Program.Sched.denoteR_zero
#print axioms Effect4.Program.Sched.denoteR_bind
#print axioms Effect4.Program.Sched.denoteR_suspend
#print axioms Effect4.Program.Sched.denoteR_branch
#print axioms Effect4.Program.Sched.denoteR_exit
#print axioms Effect4.Program.Sched.denoteR_choose
#print axioms Effect4.Program.Sched.denoteR_withFiber
#print axioms Effect4.Program.Sched.denoteR_gen
#print axioms Effect4.Program.Sched.denoteR_whileLoop
#print axioms Effect4.Program.Sched.headExit_eq_asExit?
#print axioms Effect4.Program.Sched.inlineYield_eq_headExit
#print axioms Effect4.Program.Sched.denote_of_inlineYield
#print axioms Effect4.Program.Sched.fuel_ne_zero_of_depth
#print axioms Effect4.Program.Sched.denoteR_straight
#print axioms Effect4.Program.Sched.meaning_denoteR_straight
#print axioms Test.Program.DenoteRContract.cleanup_boundary_distinct
