import Effect4.Laws.Auto.TypedStateGen
import Effect4.Laws.Program.EvaluateR

/-!
# The typed-state skeleton, emitted

`lake build Test.Audit.TypedStateEmit` regenerates `src/Effect4/Laws/Program/Typed/State.lean`
from the position census of the reference state and the command residue and the source table
(`docs/research/2026-09-18-position-census-design.md` §2D). This module is not in `Test.All`:
a build of the battery never writes into `src`; regeneration is this one explicit build, and
`git diff` on the emitted file is the drift check.
-/

open Effect4.Laws.Auto.TypedStateGen in
#emit_typed_state Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  to "src/Effect4/Laws/Program/Typed/State.lean"
