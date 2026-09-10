import Effect4.Laws.Program.Invocation
import Effect4.Api
import Test.Program.InvocationContract

/-!
Fresh kernel dependency report for the invocation slice (v2 §3 row S1a): the shared async
dispatcher and its routing theorems (`src/Effect4/Laws/Program/Invocation.lean`), the table check
(`src/Effect4/Program/Native.lean`) and the admission face (`src/Effect4/Api.lean`). The
contract is `Test/Program/InvocationContract.lean`.

Every declaration below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- INVOCATION/compile: the shared dispatcher and the unification.
#print axioms Effect4.Program.asyncRoute
#print axioms Effect4.Program.compileEff
#print axioms Effect4.Program.compile_zero_fuel
#print axioms Effect4.Program.compile_perform_eq_callback
#print axioms Effect4.Program.compileEff_callback_eq_asyncRoute
#print axioms Effect4.Program.compile_perform_eq_callback_await
#print axioms Effect4.Program.compile_perform_eq_callback_of_await

-- INVOCATION/table: the runnable-table decision and its bridge to the registration lookup.
#print axioms Effect4.Program.TableRefusal
#print axioms Effect4.Program.checkTable
#print axioms Effect4.Program.externalRow
#print axioms Effect4.Program.checkTable_none_externalRow

-- INVOCATION/typing: the two arms that now read `Signature.dom` (DI-54).
#print axioms Effect4.Program.effTy
#print axioms Effect4.Program.typeOfProgram

-- INVOCATION/api: admission, the separate image certificate, the checked entry points.
#print axioms Effect4.Api.AdmitRefusal
#print axioms Effect4.Api.AdmittedProgram
#print axioms Effect4.Api.admitProgram
#print axioms Effect4.Api.imageCertificate
#print axioms Effect4.Api.runAdmitted
#print axioms Effect4.Api.replayAdmitted

-- INVOCATION/contract: the two spellings print one call and replay the admitted fixture alike.
#print axioms Test.Program.InvocationContract.sleep_print_same

#print axioms Test.Program.InvocationContract.replay_perform_external_eq_callback
