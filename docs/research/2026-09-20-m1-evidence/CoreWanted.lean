import Effect4.Machine.Stores
import Effect4.Laws.Auto.Obligations

/-! M1: obligations recorded before the completion-data proof migration. -/

namespace Effect4.Machine.M1.Core
open Effect4 Effect4.Machine

def deferredStore_register_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat)
    (_h : self.cellAt cell = some c) (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.register cell waiter token = (self, some e)) := ⟨⟩
#proof_wanted deferredStore_register_done

def deferredStore_complete_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e e' : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.complete cell e' = (self, false)) := ⟨⟩
#proof_wanted deferredStore_complete_done

def deferredStore_complete_pending (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    self.complete cell e =
      ({ self.setCell cell ⟨some e, (c.wake.wakeAll).2⟩ with
          due := self.due ++ (c.wake.wakeAll).1.map fun w =>
            ⟨w.fiber, w.token, e, WakeMode.now⟩ }, true)) := ⟨⟩
#proof_wanted deferredStore_complete_pending

def deferredStore_complete_stores_argument (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    ((self.complete cell e).1.cellAt cell).map DeferredCell.completion = some (some e)) := ⟨⟩
#proof_wanted deferredStore_complete_stores_argument

def deferredStore_waiter_receives_stored (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat) (phase : WakePhase)
    (_h : self.cellAt cell = some c) (_hc : c.completion = none)
    (_hw : c.wake.waiters = [⟨waiter, token, phase, ()⟩]) : ProofGraph.Obligation (
    (self.complete cell e).1.due = self.due ++ [⟨waiter, token, e, WakeMode.now⟩]) := ⟨⟩
#proof_wanted deferredStore_waiter_receives_stored

#typed_state_obligations Effect4.Machine.M1.Core ceiling 5 using aesop

end Effect4.Machine.M1.Core
