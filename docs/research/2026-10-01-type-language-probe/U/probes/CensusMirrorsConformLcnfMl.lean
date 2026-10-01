import Effect4
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Conform.Effect4.LcnfMl

/-! Probe U, question 1: `Ty` readers in Conform.Effect4.LcnfMl, by the tree's instruments with `under` (they scan `Effect4` by default). Prints only; log `U/logs/census-mirrors.log`. -/

#traversal_census Effect4.Program.Ty under Conform
#exhaustive_gate Effect4.Program.Ty under Conform
