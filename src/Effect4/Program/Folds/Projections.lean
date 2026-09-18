import Effect4.Program.FoldOf
import Effect4.Program.Fold

/-!
# The list projections of the program families as folds

`Stmts.toList`, `Effs.toList`, `LayerTerms.toList` and `LayerTerms.length` (`Program/Eff.lean`)
read as algebras. Each keeps an untraversed child as a value (`a :: toList rest`), so the
converter pairs the value into the carrier — a paramorphism — and the connector is
`g e = (cata_<fam> g.alg e).2`.
-/

namespace Effect4.Program

fold_of Effect4.Program.Stmts.toList
fold_of Effect4.Program.Effs.toList
fold_of Effect4.Program.LayerTerms.toList
fold_of Effect4.Program.LayerTerms.length

end Effect4.Program
