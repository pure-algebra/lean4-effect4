import Effect4.Codegen.Read
import Effect4.Api

/-!
Fresh kernel dependency report for the reader (`Effect4/Codegen/Read.lean`; plan
`docs/research/2026-09-04-a4-reader-plan.md`). The reader's receipts are `read_print` and
`read_exact`, the round trips pinned in `Test/Codegen/ReadContract.lean`, and the native
lawfulness `nativeLawful`; this file is the axiom receipt. The binder injectivity goes
through the bytes of `Nat.repr` on purpose: the string layer's own injectivity lemmas reach
`Classical.choice` on this toolchain, and everything here is expected at the ceiling.
-/

#print axioms Effect4.Program.Var.read
#print axioms Effect4.Program.Var.name_inj
#print axioms Effect4.Program.Var.name_ne
#print axioms Effect4.Program.headOf
#print axioms Effect4.Program.readTerm
#print axioms Effect4.Program.readCause
#print axioms Effect4.Program.readForkOptions
#print axioms Effect4.Program.readRowCall
#print axioms Effect4.Program.readEff
#print axioms Effect4.Program.readHead
#print axioms Effect4.Program.readStmts
#print axioms Effect4.Program.readEffs
#print axioms Effect4.Program.readable
#print axioms Effect4.Program.LawfulSpelling
#print axioms Effect4.Program.readTerm_printTerm
#print axioms Effect4.Program.readTerm_exact
#print axioms Effect4.Program.print_not_cond
#print axioms Effect4.Program.read_print
#print axioms Effect4.Program.read_exact_all
#print axioms Effect4.Program.read_exact
#print axioms Effect4.Program.nativeSpell
#print axioms Effect4.Program.nativeLawful
#print axioms Effect4.Program.read_print_native
#print axioms Effect4.Program.read_exact_native
#print axioms Effect4.Program.roundTrip
#print axioms Effect4.Program.roundTrip_eq
#print axioms Effect4.Api.read
#print axioms Effect4.Api.roundTrip
#print axioms Effect4.Api.readable
