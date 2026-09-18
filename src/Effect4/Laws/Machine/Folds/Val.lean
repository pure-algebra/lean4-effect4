import Effect4.Program.FoldOf
import Effect4.Store.Fold
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.StoresLaws

/-!
# The Laws-side traversals of `Val` as folds

`Val.keys` / `keysList` (`Laws/Machine/Handles.lean`) and `Val.validIn` / `validInList`
(`Laws/Machine/StoresLaws.lean`, the stores fixed), each as a `ValAlgebra` with its
connectors. Not here: `Witnesses.valCode`, whose `ctor` arm splits on the argument list's shape
(`| .ctor 9 [head] => 9 :: valCode head`) — a case analysis on a container child, not a fold
as written.
-/

namespace Effect4.Machine

fold_of Effect4.Machine.Val.keys
fold_of Effect4.Machine.Val.validIn

end Effect4.Machine
