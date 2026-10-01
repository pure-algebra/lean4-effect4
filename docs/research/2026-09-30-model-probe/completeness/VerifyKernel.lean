import Effect4.Api

/-! Verifier's kernel attempt: is `Tape.Complete` provable for a tape that still owes a flush?
Read against HEAD `7cae243a`. -/

set_option autoImplicit false

namespace Probe.CompletenessVerify.Kernel

open Effect4 Effect4.Machine Effect4.Program

/-- The root yields, then answers 3. -/
def yielding : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat 3)))

/-- The tape `[evaluate]` leaves the yielded root parked behind its armed dispatcher, and the
frontier names no reason. -/
theorem yielding_reasons : (Api.replay yielding 20 [Api.evaluate]).reasons = [] := by
  decide +kernel

/-- So the tape counts as complete under `Api.Tape.Complete` (`src/Effect4/Api.lean:298-305`),
although one `flush` would still finish the run. -/
theorem yielding_tape_complete : Api.Tape.Complete yielding [] [Api.evaluate] 20 := by
  unfold Api.Tape.Complete
  simp only [yielding_reasons, List.not_mem_nil, not_false_eq_true, implies_true, and_self]

/-- And one `flush` finishes it. -/
theorem yielding_flush_finishes :
    (Api.replay yielding 20 [Api.evaluate, Api.flush]).outcome = Api.Outcome.finished := by
  decide +kernel

#print axioms yielding_reasons
#print axioms yielding_tape_complete
#print axioms yielding_flush_finishes

end Probe.CompletenessVerify.Kernel
