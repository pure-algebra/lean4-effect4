import Effect4.Program.FoldOf
import Effect4.Store.Fold
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.StoresLaws

/-!
# The Laws-side traversals of `Val` as folds

`Val.keys` / `keysList` (`Laws/Machine/Handles.lean`) and `Val.validIn` / `validInList`
(`Laws/Machine/StoresLaws.lean`, the stores fixed), each as a `ValAlgebra` with its
connectors. Not here: `Witnesses.valCode`, which maps itself over the constructor's argument
list directly (`args.map valCode`) rather than through a sibling — the `map` idiom is the
next shape.
-/

namespace Effect4.Machine

fold_of Effect4.Machine.Val.keys
fold_of Effect4.Machine.Val.validIn

end Effect4.Machine
