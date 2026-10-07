import Effect4.Program.FoldOf
import Effect4.Laws.Program.DenoteRows

/-!
# The fragment and the call tree over host rows as folds

`StraightRows` and `denoteRows` (`Laws/Program/DenoteRows.lean`, slice H1 of the host meaning),
each as an `EffAlgebra` with its connector to the fold (`StraightRows.eq_cata`,
`denoteRows.eq_cata`).
-/

namespace Effect4.Program
fold_of Effect4.Program.Denote.StraightRows (family := Effect4.Program.Eff)
fold_of Effect4.Program.Denote.denoteRows (family := Effect4.Program.Eff)
end Effect4.Program
