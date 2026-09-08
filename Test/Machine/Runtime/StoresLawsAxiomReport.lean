import Effect4.Laws.Machine.StoresLaws

/-!
# Stores laws kernel dependency report

Every declaration of `src/Effect4/Laws/Machine/StoresLaws.lean` (plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §3, packet
`Test/contracts/program-denotation.contract.md` ENSURES 10–17) is listed exactly once, in
module order. The accepted ceiling is no dependency, `propext`, or `propext` with
`Quot.sound`; `Classical.choice` and project-local axioms are not admitted. The gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

/-! ## STORES/order — the growth order -/

#print axioms Effect4.Machine.Stores.le
#print axioms Effect4.Machine.Stores.le_refl
#print axioms Effect4.Machine.Stores.le_trans

/-! ## STORES/valid — validity and well-formedness -/

#print axioms Effect4.Machine.Val.validIn
#print axioms Effect4.Machine.SyncOp.validIn
#print axioms Effect4.Machine.Stores.WF
#print axioms Effect4.Machine.Stores.empty_wf
#print axioms Effect4.Machine.SyncOp.isRead
#print axioms Effect4.Machine.Val.validIn_mono
#print axioms Effect4.Machine.SyncOp.validIn_mono

/-! ## The pure functions and the heap -/

#print axioms Effect4.Machine.FnName.total_validIn
#print axioms Effect4.Machine.FnName.partialUpdate_validIn
#print axioms Effect4.Machine.FnName.modify_validIn
#print axioms Effect4.Machine.FnName.modifySome_validIn
#print axioms Effect4.Machine.refPeek_eq_some_of_lt
#print axioms Effect4.Machine.lt_of_refPeek_eq_some
#print axioms Effect4.Machine.mem_of_refPeek_eq_some
#print axioms Effect4.Machine.refStep_length
#print axioms Effect4.Machine.refPoke_valid
#print axioms Effect4.Machine.refStep_valid

/-! ## The Deferred and Scope stores -/

#print axioms Effect4.Machine.DeferredStore.setCell_cells_length
#print axioms Effect4.Machine.DeferredStore.complete_cells_length
#print axioms Effect4.Machine.DeferredStore.cancel_cells_length
#print axioms Effect4.Machine.ScopeStore.entryAt_isSome_iff
#print axioms Effect4.Machine.ScopeStore.entryAt_make_isSome
#print axioms Effect4.Machine.ScopeStore.entryAt_make_self
#print axioms Effect4.Machine.ScopeStore.entryAt_setEntry_isSome
#print axioms Effect4.Machine.ScopeStore.entryAt_addFinalizer_isSome
#print axioms Effect4.Machine.ScopeStore.entryAt_removeFinalizer_isSome

/-! ## The store arms of `syncOpStep`, as equations -/

#print axioms Effect4.Machine.syncOpStep_deferredMake
#print axioms Effect4.Machine.syncOpStep_deferredIsDone
#print axioms Effect4.Machine.syncOpStep_deferredPoll
#print axioms Effect4.Machine.syncOpStep_deferredCompleteWith
#print axioms Effect4.Machine.syncOpStep_deferredInterruptWith
#print axioms Effect4.Machine.syncOpStep_deferredAwaitCleanup
#print axioms Effect4.Machine.syncOpStep_scopeMake
#print axioms Effect4.Machine.syncOpStep_scopeAdd
#print axioms Effect4.Machine.syncOpStep_scopeRemove
#print axioms Effect4.Machine.syncOpStep_scopeIsClosed

/-! ## The laws of `syncOpStep` -/

#print axioms Effect4.Machine.syncOpStep_le
#print axioms Effect4.Machine.syncOpStep_isSome_of_valid
#print axioms Effect4.Machine.syncOpStep_wf
#print axioms Effect4.Machine.syncOpStep_answer_valid
#print axioms Effect4.Machine.syncOpStep_read_unchanged
