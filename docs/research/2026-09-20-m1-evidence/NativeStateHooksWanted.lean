import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Obligations

/-! Pending statements captured before the bounded NativeState hook repair.
No Lean run or checked proof is claimed by this snapshot. -/
namespace Effect4.Program.Guard.NativeState.M1
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

def storeKeys_registerDeferred (stores : Stores) (cell : DeferredKey)
    (fiber : FiberId) (token : Nat) : ProofGraph.Obligation
    (storeKeys {stores with deferreds := (stores.deferreds.register cell fiber token).1} ⊆
      storeKeys stores ++ [(fiber, token)]) := ⟨⟩
#proof_wanted storeKeys_registerDeferred

def storeKeys_sleep (stores : Stores) (fiber : FiberId) (token : Nat)
    (millis : ClockMillis) : ProofGraph.Obligation
    (storeKeys {stores with timers := stores.timers.sleep fiber token millis} ⊆
      storeKeys stores ++ [(fiber, token)]) := ⟨⟩
#proof_wanted storeKeys_sleep

def registerExternal_storeKeys (p : NativeEff) (table : RowTable)
    (op : NativeOp) (request : Val) (fiber : FiberId) (token : Nat) (stores : Stores) :
    ProofGraph.Obligation
    (storeKeys ((interpOf p table).registerAsync (.external op request) fiber token stores).1 =
      storeKeys stores) := ⟨⟩
#proof_wanted registerExternal_storeKeys

end Effect4.Program.Guard.NativeState.M1
