import Effect4.Laws.Program.Denote

/-!
Fresh kernel dependency report for the straight-line denotation
(`src/Effect4/Laws/Program/Denote.lean`; packet `Test/contracts/program-denotation.contract.md`).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- The carrier.
#print axioms Effect4.Program.Denote.StoreSig
#print axioms Effect4.Program.Denote.Straight
#print axioms Effect4.Program.Denote.denote
#print axioms Effect4.Program.Denote.storeHandler
#print axioms Effect4.Program.Denote.meaning

-- The fragment is closed under subprograms.
#print axioms Effect4.Program.Denote.Straight.suspend
#print axioms Effect4.Program.Denote.Straight.bind
#print axioms Effect4.Program.Denote.Straight.branch
#print axioms Effect4.Program.Denote.Straight.exit
#print axioms Effect4.Program.Denote.Straight.catchCause
#print axioms Effect4.Program.Denote.Straight.matchCause
#print axioms Effect4.Program.Denote.Straight.onExit
#print axioms Effect4.Program.Denote.Straight.perform_sync

-- The equations of the meaning.
#print axioms Effect4.Program.Denote.meaning_succeed_some
#print axioms Effect4.Program.Denote.meaning_succeed_none
#print axioms Effect4.Program.Denote.meaning_fail_some
#print axioms Effect4.Program.Denote.meaning_fail_none
#print axioms Effect4.Program.Denote.meaning_failCause_some
#print axioms Effect4.Program.Denote.meaning_failCause_none
#print axioms Effect4.Program.Denote.meaning_yieldError_some
#print axioms Effect4.Program.Denote.meaning_yieldError_none
#print axioms Effect4.Program.Denote.meaning_sync
#print axioms Effect4.Program.Denote.meaning_suspend
#print axioms Effect4.Program.Denote.meaning_perform_sync
#print axioms Effect4.Program.Denote.meaning_perform_noEval
#print axioms Effect4.Program.Denote.meaning_perform_noDecode
#print axioms Effect4.Program.Denote.meaning_bind
#print axioms Effect4.Program.Denote.meaning_branch_true
#print axioms Effect4.Program.Denote.meaning_branch_false
#print axioms Effect4.Program.Denote.meaning_branch_bad
#print axioms Effect4.Program.Denote.meaning_exit
#print axioms Effect4.Program.Denote.meaning_catchCause
#print axioms Effect4.Program.Denote.meaning_matchCause
#print axioms Effect4.Program.Denote.meaning_onExit
