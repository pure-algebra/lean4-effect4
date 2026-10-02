import Effect4
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Tools.TyVectors

/-! The mirror census of `Ty` under `Tools` with Tools.TyVectors imported, for `scripts/check-ty-rule.py`
(probe U's `U/probes/CensusMirrors*.lean`). Nothing asserted. -/

#traversal_census Effect4.Program.Ty under Tools
#exhaustive_gate Effect4.Program.Ty under Tools
