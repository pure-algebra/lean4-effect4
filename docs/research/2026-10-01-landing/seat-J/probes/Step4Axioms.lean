import Effect4.Laws.Api.Supervision
import Effect4.Laws.Run
import Effect4.Laws.Program.ReasonsR
import Effect4.Laws.Api.Frontier

/-! Seat J, step 4: the axioms of every theorem whose statement or proof the `Await` record
touched, and of the laws over the definitions it changed (`awaits`, `awaitsR`, `hostReasons`,
`hostReasonsR`, `freshCall`, `driveFrom`). -/

#print axioms Effect4.Api.awaits_parked
#print axioms Effect4.Api.awaits_live
#print axioms Effect4.Run.awaits_ne_nil
#print axioms Effect4.Run.requestOf_of_mem_awaits
#print axioms Effect4.Run.freshCall_facts
#print axioms Effect4.Run.drive_envelope
#print axioms Effect4.Program.Sched.awaits_eq_ref
#print axioms Effect4.Program.Sched.hostReasons_eq_ref
#print axioms Effect4.Api.exists_awaitHost_iff
#print axioms Effect4.Api.observe_awaitingAsync_iff
