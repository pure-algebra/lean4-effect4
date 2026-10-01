import Effect4
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Conform.Effect4.LcnfSemantics

/-! The mirror census of `Ty` under `Conform` with Conform.Effect4.LcnfSemantics imported, for `scripts/check-ty-rule.py`
(probe U's `U/probes/CensusMirrors*.lean`). Nothing asserted. -/

#traversal_census Effect4.Program.Ty under Conform
#exhaustive_gate Effect4.Program.Ty under Conform
