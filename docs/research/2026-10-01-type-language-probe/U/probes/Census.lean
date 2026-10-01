import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive

/-! Probe U, question 1: the census and the exhaustiveness inventory of `Ty` at `630e6c37`,
read by the tree's own instruments (`Laws/Auto/Traversals.lean`, `Laws/Auto/Exhaustive.lean`).
Nothing asserted; the output is the log `U/logs/census.log`. -/

#traversal_census Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Ty
