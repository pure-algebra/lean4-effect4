import Effect4.Program.FoldOf
import Effect4.Program.Fragment
import Effect4.Program.Fold

/-!
# The straight-line fragment as a fold

`Straight` (`Program/Fragment.lean`) read as an algebra: `Straight.alg`, its homomorphism
witness `Straight.hom`, and `Straight.eq_cata : ∀ e, Straight e = cata_eff Straight.alg e`.
The algebra names every constructor (the `| _ => false` arm is one field per constructor here),
which is what `docs/core/decisions.md` row 35 asked of the fragment.
-/

namespace Effect4.Program.Denote

fold_of Effect4.Program.Denote.Straight

end Effect4.Program.Denote
