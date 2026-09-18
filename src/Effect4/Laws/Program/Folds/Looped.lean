import Effect4.Program.FoldOf
import Effect4.Program.Folds.Straight
import Effect4.Laws.Program.DenoteB

/-!
# The loop-bearing fragment as a fold

`Looped` (`Laws/Program/DenoteB.lean`) read as an algebra beside `Straight.alg`, with
`Looped.eq_cata : ∀ e, Looped e = cata_eff Looped.alg e`.
-/

namespace Effect4.Program.Denote

fold_of Effect4.Program.Denote.Looped

end Effect4.Program.Denote
