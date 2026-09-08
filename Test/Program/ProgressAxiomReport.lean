import Effect4.Laws.Program.Progress

/-!
Fresh kernel dependency report for the first join of lanes 1 and 2
(`src/Effect4/Laws/Program/Progress.lean`; plan `docs/research/2026-09-05-slice-1-compile-ground.md`
§6, node `PROGRESS/answer`, packet `Test/contracts/program-denotation.contract.md`).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every
declaration below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- PROGRESS/heap: the typing half of the heap invariant.
#print axioms Effect4.Program.Stores.HeapNat
#print axioms Effect4.Program.instDecidableHeapNat
#print axioms Effect4.Program.Stores.empty_heapNat

-- PROGRESS/fn: the pure functions send numbers to numbers.
#print axioms Effect4.Program.FnName.total_hasTy_nat
#print axioms Effect4.Program.FnName.partialUpdate_hasTy_nat
#print axioms Effect4.Program.FnName.modify_hasTy_nat
#print axioms Effect4.Program.FnName.modifySome_hasTy_nat

-- PROGRESS/handle: the handles inhabit their spellings, by evaluation.
#print axioms Effect4.Program.Val.hasTy_cell_refTy
#print axioms Effect4.Program.Val.hasTy_promise_deferredTy
#print axioms Effect4.Program.Val.hasTy_scopeHandle_scope

-- PROGRESS/answer: the heap, the join, its two faces.
#print axioms Effect4.Program.refPoke_heapNat
#print axioms Effect4.Program.refStep_of_syncOpStep
#print axioms Effect4.Program.step_typed
#print axioms Effect4.Program.answer_typed
#print axioms Effect4.Program.step_heapNat

-- PROGRESS/progress: the two lanes read together.
#print axioms Effect4.Program.syncOpOf_validIn
#print axioms Effect4.Program.progress
