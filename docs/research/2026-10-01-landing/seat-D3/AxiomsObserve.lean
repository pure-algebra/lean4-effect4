import Effect4.Laws.Program.Typed.Commands.Observe

/-! Seat D3: `#print axioms` for every theorem of `src/Effect4/Laws/Program/Typed/Commands/Observe.lean` and the ledger lines it
closes (at the head). Run: `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-01-landing/seat-D3/AxiomsObserve.lean`. -/

#print axioms Effect4.Program.Typed.ExceptView.obs_trans
#print axioms Effect4.Program.Typed.countdownAt_except
#print axioms Effect4.Program.Typed.storedObserverOk_except
#print axioms Effect4.Program.Typed.observerCommandOk_except
#print axioms Effect4.Program.Typed.enrollRaceOk_except
#print axioms Effect4.Program.Typed.fiberTyped_except
#print axioms Effect4.Program.Typed.exceptView_rupdate
#print axioms Effect4.Program.Typed.commandDelivery_idle
#print axioms Effect4.Program.Typed.configTyped_replace
#print axioms Effect4.Program.Typed.KeptFields.refl
#print axioms Effect4.Program.Typed.KeptFields.trans
#print axioms Effect4.Program.Typed.interruptRecord_fields
#print axioms Effect4.Program.Typed.InterruptView.refl
#print axioms Effect4.Program.Typed.InterruptView.trans
#print axioms Effect4.Program.Typed.InterruptView.emit
#print axioms Effect4.Program.Typed.interruptView_rupdate
#print axioms Effect4.Program.Typed.obsView_of_pending
#print axioms Effect4.Program.Typed.configTyped_interruptEach
#print axioms Effect4.Program.Typed.InterruptView.requests
#print axioms Effect4.Program.Typed.countdownWalk_view
#print axioms Effect4.Program.Typed.countdownWalk_spec
#print axioms Effect4.Program.Typed.countdownAt_found
#print axioms Effect4.Program.Typed.countdownAt_of_found
#print axioms Effect4.Program.Typed.countdownPayload_advance
#print axioms Effect4.Program.Typed.countdownPayload_unknown
#print axioms Effect4.Program.Typed.countdownPayload_pinned
#print axioms Effect4.Program.Typed.countdownAt_advance
#print axioms Effect4.Program.Typed.resumePrim_typed
#print axioms Effect4.Program.Typed.configTyped_evaluates
#print axioms Effect4.Program.Typed.fiberTyped_repend
#print axioms Effect4.Program.Typed.rfiber?_emit
#print axioms Effect4.Program.Typed.countdown_parked
#print axioms Effect4.Program.Typed.lookupBack_update
#print axioms Effect4.Program.Typed.countdown_of_not_offKey
#print axioms Effect4.Program.Typed.observe_countdown
#print axioms Effect4.Program.Typed.observe_preserves
#print axioms Effect4.Program.Typed.M6Ledger.step_observe.checked
