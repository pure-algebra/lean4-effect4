import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Provision

/-!
# The provision documentation traversal as a fold

`Provision.docsLayer` / `docsLayers` (`Program/Provision.lean`) read as one `EffAlgebra` over
`Provision.DocsOp`, with `docsLayer.eq_cata` and `docsLayers.eq_cata`. `Provision.build` and
`buildAll` thread an environment after the layer value — the fold-returning-a-function shape
`fold_of` does not handle yet.
-/

namespace Effect4.Program

fold_of Effect4.Program.Provision.docsLayer

end Effect4.Program
