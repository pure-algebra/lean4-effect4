import Effect4.Program.FoldOf
import Effect4.Store.Fold
import Effect4.Machine.Stores

/-!
# The hand traversals of `Store.Val` in the machine, as folds

`Machine.reasonsOfVal` (`Machine/Stores.lean`) with its sibling `reasonsOfList`, as one
`ValAlgebra`: a paramorphism over the container — its first arm is a case analysis on the
`ctor` child list (`Value.exitErr written` is `.ctor 1 [written]`) that reads the grandchild as
a value and never recurses on it, so the list child's value is read back from the paired results
and the arm stays as written.
-/

namespace Effect4.Machine

fold_of Effect4.Machine.reasonsOfVal

end Effect4.Machine
