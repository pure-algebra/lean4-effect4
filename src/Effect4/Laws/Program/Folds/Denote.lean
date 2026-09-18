import Effect4.Program.FoldOf
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Program.LoopSound

/-!
# The meaning and the agreement measures as folds

`denote` (`Laws/Program/Denote.lean`, the compositional meaning on `Straight`) and its budgeted
and parameterised forms `denoteB`, `denoteWith`, `denoteBWith`, each as an `EffAlgebra` whose
carrier at `.eff` is the meaning's function type (`List Val → …`; the budget and the wrong-shape
exit are the fixed parameters), with the connector `denote.eq_cata : ∀ e vs, denote e vs =
cata_eff denote.alg e vs`; and the four measures of the agreement proofs (`depth`, `steps`,
`depthB`, `boundB`) as `Nat`-valued folds. This is row 30's `denote` onto the fold.
-/

namespace Effect4.Program

fold_of Effect4.Program.Denote.denote
fold_of Effect4.Program.Denote.denoteB
fold_of Effect4.Program.Denote.denoteWith
fold_of Effect4.Program.Denote.denoteBWith
fold_of Effect4.Program.Agreement.depth
fold_of Effect4.Program.Agreement.steps
fold_of Effect4.Program.Agreement.depthB
fold_of Effect4.Program.Agreement.boundB

end Effect4.Program
