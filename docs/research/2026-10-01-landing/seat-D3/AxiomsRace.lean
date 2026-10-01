import Effect4.Laws.Program.Typed.Commands.Race

/-! Seat D3: `#print axioms` for every theorem of `src/Effect4/Laws/Program/Typed/Commands/Race.lean` and the ledger lines it
closes (at the head). Run: `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-01-landing/seat-D3/AxiomsRace.lean`. -/

#print axioms Effect4.Program.Typed.owner_free
#print axioms Effect4.Program.Typed.configTyped_cons_plain
#print axioms Effect4.Program.Typed.interruptTarget_preserves
#print axioms Effect4.Program.Typed.fiberListColumns_sub
#print axioms Effect4.Program.Typed.configTyped_cons_afterAwaitAll
#print axioms Effect4.Program.Typed.raceCancel_preserves
#print axioms Effect4.Program.Typed.rmodify_race?
#print axioms Effect4.Program.Typed.enrollRace_preserves
#print axioms Effect4.Program.Typed.commandAuthority_flags
#print axioms Effect4.Program.Typed.configTyped_cons_loop
#print axioms Effect4.Program.Typed.seq_typed_sameError
#print axioms Effect4.Program.Typed.afterInterruptCode_typed
#print axioms Effect4.Program.Typed.commandOwner_update
#print axioms Effect4.Program.Typed.afterInterrupt_preserves
#print axioms Effect4.Program.Typed.commandDelivery_owner
#print axioms Effect4.Program.Typed.configTyped_rupdate_owner
#print axioms Effect4.Program.Typed.sub_union_self_left
#print axioms Effect4.Program.Typed.sub_union_self_right
#print axioms Effect4.Program.Typed.sub_declaredUnion
#print axioms Effect4.Program.Typed.subN_declaredUnion
#print axioms Effect4.Program.Typed.subN_list_exitOf
#print axioms Effect4.Program.Typed.awaitAllPark_typed
#print axioms Effect4.Program.Typed.closeParAwait_preserves
#print axioms Effect4.Program.Typed.M6Ledger.step_interruptTarget.checked
#print axioms Effect4.Program.Typed.M6Ledger.step_raceCancel.checked
#print axioms Effect4.Program.Typed.M6Ledger.step_enrollRace.checked
#print axioms Effect4.Program.Typed.M6Ledger.step_afterInterrupt.checked
#print axioms Effect4.Program.Typed.M6Ledger.step_closeParAwait.checked
