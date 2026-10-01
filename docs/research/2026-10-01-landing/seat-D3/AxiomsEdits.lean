import Effect4.Laws.Program.Typed.Edits

/-! Seat D3: `#print axioms` for every theorem of `src/Effect4/Laws/Program/Typed/Edits.lean` and the ledger lines it
closes (at the head). Run: `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-01-landing/seat-D3/AxiomsEdits.lean`. -/

#print axioms Effect4.Program.Typed.configTyped_nil
#print axioms Effect4.Program.Typed.configTyped_drainDue
#print axioms Effect4.Program.Typed.quiet_yield
#print axioms Effect4.Program.Typed.edit_yield
#print axioms Effect4.Program.Typed.edit_interrupt
#print axioms Effect4.Program.Typed.prepareAsyncAnswer_running
#print axioms Effect4.Program.Typed.edit_answer
#print axioms Effect4.Program.Typed.requestOfR_update_flags
#print axioms Effect4.Program.Typed.registrationQueue_of_tails
#print axioms Effect4.Program.Typed.mem_drain
#print axioms Effect4.Program.Typed.snapshotTyped_drain
#print axioms Effect4.Program.Typed.edit_drain
#print axioms Effect4.Program.Typed.wf_retime
#print axioms Effect4.Program.Typed.edit_clockNone
#print axioms Effect4.Program.Typed.decisionEdits_of_clockSome
#print axioms Effect4.Program.Typed.decisionKeeps_of_steps
#print axioms Effect4.Program.Typed.typedState_reachable_of_steps
#print axioms Effect4.Program.Typed.validIn_of_ok
#print axioms Effect4.Program.Typed.answersValid_of_noHostAnswer
#print axioms Effect4.Program.Typed.exitHandles_valid_of_registered
#print axioms Effect4.Program.Typed.M6Edits.drain.checked
#print axioms Effect4.Program.Typed.M6Edits.yield.checked
#print axioms Effect4.Program.Typed.M6Edits.interrupt.checked
#print axioms Effect4.Program.Typed.M6Edits.clockNone.checked
#print axioms Effect4.Program.Typed.M6Edits.answer.checked
