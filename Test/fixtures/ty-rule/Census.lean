import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive

/-! The census and the exhaustiveness inventory of `Ty` over the whole tree, read by the tree's own
instruments, for `scripts/check-ty-rule.py` (probe U's `U/probes/Census.lean`). Nothing asserted:
the output is the log the checker reads. -/

#traversal_census Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Ty
