import Effect4.Laws.Program.Typed

/-!
Fresh kernel dependency report for the value typing of the native cut
(`src/Effect4/Laws/Program/Typed.lean`; plan `docs/research/2026-09-05-slice-1-compile-ground.md`
§2, packet `Test/contracts/program-denotation.contract.md` ENSURES 1–9).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every
declaration below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- TYPED/value: `hasTy`, its inversions, `Fits`.
#print axioms Effect4.Program.Val.hasTy
#print axioms Effect4.Program.Val.hasTy_unit_inv
#print axioms Effect4.Program.Val.hasTy_nat_inv
#print axioms Effect4.Program.Val.hasTy_bool_inv
#print axioms Effect4.Program.Val.hasTy_string_inv
#print axioms Effect4.Program.Val.hasTy_option_inv
#print axioms Effect4.Program.Val.hasTy_refTy_inv
#print axioms Effect4.Program.Val.hasTy_deferredTy_inv
#print axioms Effect4.Program.Val.hasTy_prod_inv
#print axioms Effect4.Program.Fits
#print axioms Effect4.Program.Fits.get?
#print axioms Effect4.Program.Fits.length
#print axioms Effect4.Program.Fits.append
#print axioms Effect4.Program.Fits.singleton_inv
#print axioms Effect4.Program.Fits.pair_inv

-- TYPED/term: literals, atoms, the mutual inductions.
#print axioms Effect4.Program.Lit.toVal_hasTy
#print axioms Effect4.Program.Lit.toVal_isSome
#print axioms Effect4.Program.nativeAtom_typed
#print axioms Effect4.Program.termTy_app
#print axioms Effect4.Program.termsTy_cons
#print axioms Effect4.Program.evalTerm_app
#print axioms Effect4.Program.evalTerms_cons
#print axioms Effect4.Program.evalTerm_hasTy
#print axioms Effect4.Program.evalTerms_hasTy
#print axioms Effect4.Program.evalTerm_isSome
#print axioms Effect4.Program.evalTerms_isSome

-- TYPED/row: the request shapes.
#print axioms Effect4.Program.syncOpOf_isSome
#print axioms Effect4.Program.syncOpOf_async_none
