import Test.Machine.Runtime.SchedulingContract

/-! LIVE/fair dependency receipts. -/

#print axioms Effect4.Machine.Scheduling.QueueKeeps
#print axioms Effect4.Machine.Scheduling.evaluate_queue
#print axioms Effect4.Machine.Scheduling.driveStep_queue
#print axioms Effect4.Machine.Scheduling.drive_queue
#print axioms Effect4.Machine.Scheduling.fireTasks_queue
#print axioms Effect4.Machine.Scheduling.fire_keeps_tail
#print axioms Effect4.Machine.Scheduling.FlushReady
#print axioms Effect4.Machine.Scheduling.FiredWithin
#print axioms Effect4.Machine.Scheduling.firedWithin_more
#print axioms Effect4.Machine.Scheduling.flush_fair_prefix
#print axioms Effect4.Machine.Scheduling.flush_fair
#print axioms Effect4.Machine.Scheduling.FairTape
#print axioms Test.Runtime.SchedulingContract.both_serviced
#print axioms Test.Runtime.SchedulingContract.round_bound_alone_false
#print axioms Test.Runtime.SchedulingContract.empty_queue_empty_tape_fair
