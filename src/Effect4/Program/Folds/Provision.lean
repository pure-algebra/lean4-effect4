import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Provision

/-!
# The provision traversals as folds

`Provision.build` / `buildAll` (`Program/Provision.lean`; the leaf semantics fixed, the context
in the carrier — `R .layer := Ctx → Option Ctx`; `buildAll`'s `cons head .nil` arm inspects the
tail, so the carrier pairs the value in) and `Provision.docsLayer` / `docsLayers`, each block
as one `EffAlgebra` with its connectors.
-/

namespace Effect4.Program

fold_of Effect4.Program.Provision.build
fold_of Effect4.Program.Provision.docsLayer

end Effect4.Program
