import OCaml5
import Tools.TyVectors
import Tools.ProfileJson
import Conform.Lcnf.Cases
import Conform.Effect4.LcnfMl
import Conform.Effect4.LcnfSemantics
import Effect4.Laws.Auto.Exhaustive

/-! Seat TREE, data probe (2026-10-01): the `Ty` matches outside `Effect4.*` that the tree's
`#exhaustive_gate` reports only when asked (its default scope is `Effect4`): the OCaml estate's
Lean half (`OCaml5`, which emits `eff_native.ml` from `Ty` values), the TypeScript and profile
drivers (`Tools.TyVectors`, `Tools.ProfileJson`) and the conformance tooling (`Conform`).
Printed, not asserted. Scratch, not in the tree. -/

#exhaustive_gate Effect4.Program.Ty under OCaml5
#exhaustive_gate Effect4.Program.Ty under Tools
#exhaustive_gate Effect4.Program.Ty under Conform
