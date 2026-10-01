import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Verifier for seat PROGRAMS (2026-09-30), finding PROG-15: recount decisions row 61's
"22 of 51 for `Ty`" at HEAD with the tree's own instrument. The instrument reads definitions
only, never proofs (`Laws/Auto/Exhaustive.lean` header, "What it does not see"). Printed, not
asserted. Scratch, not in the tree. -/

#exhaustive_gate Effect4.Program.Ty
