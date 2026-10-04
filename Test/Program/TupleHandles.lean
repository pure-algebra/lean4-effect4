import Effect4.Laws.Program.Handles.Term
import Effect4.Laws.Program.MeaningSound

/-! Finite raw-handle controls and trust queries for tuple evaluation.
The universal subset laws are the register's evidence that terms mint no frames
(`E4-TYPED-CE-040`); they need no typed inputs. -/
namespace Effect4.Test.TupleHandles
open Program Machine

#guard (evalTerm [.handle 255 7, .handle 254 9] (.app "tuple"
  (.cons (.var 0) (.cons (.var 1) .nil)))).map Store.Val.handles = some [(255, 7), (254, 9)]
#guard (evalTerm [.list [.handle 255 7, .handle 254 9]]
  (.tupleAt (.var 0) 1)).map Store.Val.handles = some [(254, 9)]

#print axioms tupleAt_keys
#print axioms tupleAt_handles
#print axioms RawHandles.nativeAtom_handles
#print axioms RawHandles.evalTerm_handles
#print axioms Denote.meaning_typed
end Effect4.Test.TupleHandles
