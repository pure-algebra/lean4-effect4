import Test
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive

/-! Probe U, question 1: `Ty` readers in the `Test` battery (fixtures, counterexamples, contracts),
by the tree's instruments with `under Test`. Prints only; log `U/logs/census-test.log`. -/

#traversal_census Effect4.Program.Ty under Test
#exhaustive_gate Effect4.Program.Ty under Test
