import Effect4.Laws.Auto.TypedStateGen
import Effect4.Laws.Program.EvaluateR

/-!
# The typed-state skeleton, emitted

`lake env lean scripts/lean/TypedStateEmit.lean` regenerates
`src/Effect4/Laws/Program/Typed/State.lean` from the position census of the reference state and
the command residue and the source table (`docs/research/2026-09-18-position-census-design.md`
§2D). It lives outside every library root on purpose: a build of the battery never writes into
`src` (the module-closure gate of `Test/All.lean` refuses an unimported test module), regeneration
is this one explicit run, and `git diff` on the emitted file is the drift check. The review's R1
retires it: the skeleton is to be elaborated in place by quotations.
-/

open Effect4.Laws.Auto.TypedStateGen in
#emit_typed_state Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  to "src/Effect4/Laws/Program/Typed/State.lean"
