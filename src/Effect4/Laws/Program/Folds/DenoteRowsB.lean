import Effect4.Program.FoldOf
import Effect4.Laws.Program.DenoteRowsB

/-!
# The budgeted call tree over host rows as a fold

`denoteRowsB` (`Laws/Program/DenoteRowsB.lean`, host meaning on loops) as an `EffAlgebra` with
its connector to the fold (`denoteRowsB.eq_cata`), beside `denoteRows`'s
(`Laws/Program/Folds/DenoteRows.lean`). Concept `initial-algebras-folds`: every traversal is a fold
or generated from the signature, and this one was written by hand. Its consumer is the shared
control algebra of the meanings (cleanup C4). It holds at every table, budget, program and
environment, as an equation of call trees; it adds no machine, typing or host claim (Codex's review
of the loop meaning, finding R3).
-/

namespace Effect4.Program
fold_of Effect4.Program.Denote.denoteRowsB (family := Effect4.Program.Eff)
end Effect4.Program
