import Effect4
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import OCaml5.Eff.Goldens
import OCaml5.Eff.Emit
import OCaml5.Eff.Metadata

/-! The mirror census of `Ty` under `OCaml5` with `OCaml5.Eff.Goldens`, `OCaml5.Eff.Emit` and
`OCaml5.Eff.Metadata` imported, for `scripts/check-ty-rule.py` (probe U's
`U/probes/CensusMirrors*.lean`). Nothing asserted. -/

#traversal_census Effect4.Program.Ty under OCaml5
#exhaustive_gate Effect4.Program.Ty under OCaml5
