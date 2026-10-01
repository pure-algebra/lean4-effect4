import Effect4.Laws.Program.Typed.Commands.Finish

/-! Seat D3: `#print axioms` for every theorem of `src/Effect4/Laws/Program/Typed/Commands/Finish.lean` and the ledger lines it
closes (at the head). Run: `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-01-landing/seat-D3/AxiomsFinish.lean`. -/

#print axioms Effect4.Program.Typed.raceRegistrationR_typed
#print axioms Effect4.Program.Typed.not_readsCode_idle
#print axioms Effect4.Program.Typed.not_owner_idle
#print axioms Effect4.Program.Typed.evaluate_preserves
#print axioms Effect4.Program.Typed.pendingWeaker_filter
#print axioms Effect4.Program.Typed.resume_step
#print axioms Effect4.Program.Typed.resume_preserves
#print axioms Effect4.Program.Typed.M6Ledger.step_evaluate.checked
#print axioms Effect4.Program.Typed.M6Ledger.step_resume.checked
