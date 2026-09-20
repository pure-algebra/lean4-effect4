import Effect4.Machine.Stores
import Effect4.Laws.Machine.Refinement
import Effect4.Laws.Auto.Obligations

/-! M1: obligations recorded before the completion-data proof migration. -/

namespace Effect4.Machine

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  DeferredStore.make DeferredStore.cellAt DeferredStore.setCell DeferredStore.isDone
  DeferredStore.poll DeferredStore.register DeferredStore.complete DeferredStore.drainDue
  Owed.mapCode_waiter Owed.mapCode_token Owed.mapCode_mode

/-- A successful list lookup supplies the bound needed by the store write/read law. -/
theorem store_lookup_lt {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h
  exact bound

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] store_lookup_lt

end Effect4.Machine

namespace Effect4.Machine.M1.Core
open Effect4 Effect4.Machine

def deferredStore_register_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat)
    (_h : self.cellAt cell = some c) (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.register cell waiter token = (self, some e)) := ⟨⟩

def deferredStore_complete_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e e' : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.complete cell e' = (self, false)) := ⟨⟩

def deferredStore_complete_pending (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    self.complete cell e =
      ({ self.setCell cell ⟨some e, (c.wake.wakeAll).2⟩ with
          due := self.due ++ (c.wake.wakeAll).1.map fun w =>
            ⟨w.fiber, w.token, e, WakeMode.now⟩ }, true)) := ⟨⟩

def deferredStore_complete_stores_argument (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    ((self.complete cell e).1.cellAt cell).map DeferredCell.completion = some (some e)) := ⟨⟩

def deferredStore_waiter_receives_stored (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat) (phase : WakePhase)
    (_h : self.cellAt cell = some c) (_hc : c.completion = none)
    (_hw : c.wake.waiters = [⟨waiter, token, phase, ()⟩]) : ProofGraph.Obligation (
    (self.complete cell e).1.due = self.due ++ [⟨waiter, token, e, WakeMode.now⟩]) := ⟨⟩

#typed_state_obligations Effect4.Machine.M1.Core ceiling 0 using aesop (rule_sets := [Effect4.Stores])

end Effect4.Machine.M1.Core

namespace Effect4.Machine
/-- The store bank control: a successful cell lookup determines the poll result. -/
theorem poll_reads_cell (s : DeferredStore) (k : DeferredKey) (c : DeferredCell)
    (h : s.cellAt k = some c) : s.poll k = some c.completion := by
  aesop (rule_sets := [Effect4.Stores])
end Effect4.Machine
