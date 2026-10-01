import Effect4
import Effect4.Laws.Auto.Exhaustive
import Test.Audit.ExhaustiveFixture

/-!
Seat G probe (step 3): the exhaustiveness inventory over the fixture and over the core root's
`Ty`, `Term` and `Store.Val` matches, run before and after the printer change
(`logs/exhaustive-before.log`, `logs/exhaustive-after.log`). The core root's one private holder is
`Effect4.Codegen.Types.ofNormalized` (a `Ty` match with no catch-all). The Laws root is not
imported here (its modules are rebuilt by step 6); `Test/Audit/TraversalCensus.lean` reads both.
-/

#exhaustive_gate Effect4.Program.Ty under Test.Audit.ExhaustiveFixture
#exhaustive_gate Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Term
#exhaustive_gate Effect4.Store.Val
