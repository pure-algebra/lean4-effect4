import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.Admit

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

-- TYPED/allocation (DI-17, 2026-09-09): the table order and membership monotonicity.
#print axioms Effect4.Program.Extends
#print axioms Effect4.Program.extends_append
#print axioms Effect4.Program.hasTy_mono
#print axioms Effect4.Program.hasTy_append

-- TYPED/environment at an allocation state (DI-17): the generalisation of `Fits`.
#print axioms Effect4.Program.FitsWith
#print axioms Effect4.Program.FitsIn
#print axioms Effect4.Program.Fits_iff_FitsIn_nil
#print axioms Effect4.Program.FitsWith.append
#print axioms Effect4.Program.FitsIn.append
#print axioms Effect4.Program.FitsIn.mono
#print axioms Effect4.Program.fits_childWith

-- ERROR IMAGE (DI-62): the folds and the round trip (`src/Effect4/Program/ErrorImage.lean`).
#print axioms Effect4.Program.valOfErr
#print axioms Effect4.Program.reasonAdmits
#print axioms Effect4.Program.causeAdmits
#print axioms Effect4.Program.reasonAdmits_congr
#print axioms Effect4.Program.causeAdmits_congr
#print axioms Effect4.Program.errOf_valOfErr
#print axioms Effect4.Program.valOfErr_errOf
#print axioms Effect4.Program.errAdmits_eq_reasonAdmits
#print axioms Effect4.Program.reasonAdmits_hasTy
#print axioms Effect4.Program.causeAdmits_hasTy

-- ADMIT/failure branch (DI-26): the counterpart of the three success-only laws.
#print axioms Effect4.Program.hasTyCause
#print axioms Effect4.Program.hasTyCause_exitErr_fold
#print axioms Effect4.Program.hasTyCause_exitErr
#print axioms Effect4.Program.external_error_typed
#print axioms Effect4.Program.external_oracle_error_typed
