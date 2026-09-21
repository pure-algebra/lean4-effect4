import Effect4.Machine.Stores
import Effect4.Laws.Auto.Obligations

/-! M1: obligations recorded before the completion-data proof migration. -/

namespace Effect4.Machine

attribute [aesop norm simp (rule_sets := [Effect4.StoreKernel])]
  DeferredStore.make DeferredStore.cellAt DeferredStore.setCell DeferredStore.isDone
  DeferredStore.poll DeferredStore.register DeferredStore.cancel DeferredStore.complete
  DeferredStore.drainDue DeferredStore.wakeBatch Owed.mapCode

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  Owed.mapCode_waiter Owed.mapCode_token Owed.mapCode_mode

theorem M1.CompletionSupport.store_lookup_lt {α : Type} {xs : List α} {i : Nat} {a : α}
    (_h : xs[i]? = some a) : ProofGraph.Obligation (
    i < xs.length) := ⟨⟩

/-- A successful list lookup supplies the bound needed by the store write/read law. -/
theorem store_lookup_lt {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h
  exact bound

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] store_lookup_lt

section OwedMap
universe u v w
variable {κ : Type u} {κ' : Type v} {κ'' : Type w}

theorem M1.OwedMapWanted.code (f : κ → κ') (d : Owed κ) : ProofGraph.Obligation
    ((d.mapCode f).code = f d.code) := ⟨⟩

theorem M1.OwedMapWanted.id (d : Owed κ) : ProofGraph.Obligation
    (d.mapCode id = d) := ⟨⟩

theorem M1.OwedMapWanted.comp (f : κ → κ') (g : κ' → κ'') (d : Owed κ) : ProofGraph.Obligation
    ((d.mapCode f).mapCode g = d.mapCode (g ∘ f)) := ⟨⟩

theorem M1.OwedMapWanted.id_fun : ProofGraph.Obligation
    (Owed.mapCode (_root_.id : κ → κ) = _root_.id) := ⟨⟩

theorem Owed.mapCode_code (f : κ → κ') (d : Owed κ) :
    (d.mapCode f).code = f d.code := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

theorem Owed.mapCode_id (d : Owed κ) : d.mapCode id = d := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

theorem Owed.mapCode_comp (f : κ → κ') (g : κ' → κ'') (d : Owed κ) :
    (d.mapCode f).mapCode g = d.mapCode (g ∘ f) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

theorem Owed.mapCode_id_fun : Owed.mapCode (id : κ → κ) = id := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  Owed.mapCode_code Owed.mapCode_id Owed.mapCode_comp Owed.mapCode_id_fun

#typed_state_obligations Effect4.Machine.M1.OwedMapWanted ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
end OwedMap

end Effect4.Machine

namespace Effect4.Machine.M1.Core
open Effect4 Effect4.Machine

theorem deferredStore_register_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat)
    (_h : self.cellAt cell = some c) (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.register cell waiter token = (self, some e)) := ⟨⟩

theorem deferredStore_complete_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e e' : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = some e) : ProofGraph.Obligation (
    self.complete cell e' = (self, false)) := ⟨⟩

theorem deferredStore_complete_pending (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    self.complete cell e =
      ({ self.setCell cell ⟨some e, (c.wake.wakeAll).2⟩ with
          due := self.due ++ (c.wake.wakeAll).1.map fun w =>
            ⟨w.fiber, w.token, e, WakeMode.now⟩ }, true)) := ⟨⟩

theorem deferredStore_complete_stores_argument (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (_h : self.cellAt cell = some c)
    (_hc : c.completion = none) : ProofGraph.Obligation (
    ((self.complete cell e).1.cellAt cell).map DeferredCell.completion = some (some e)) := ⟨⟩

theorem deferredStore_waiter_receives_stored (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Completion Val Err Defect FiberId Ann) (waiter : FiberId) (token : Nat) (phase : WakePhase)
    (_h : self.cellAt cell = some c) (_hc : c.completion = none)
    (_hw : c.wake.waiters = [⟨waiter, token, phase, ()⟩]) : ProofGraph.Obligation (
    (self.complete cell e).1.due = self.due ++ [⟨waiter, token, e, WakeMode.now⟩]) := ⟨⟩

#typed_state_obligations Effect4.Machine.M1.Core ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

end Effect4.Machine.M1.Core

namespace Effect4.Machine
theorem M1.CompletionSupport.poll_reads_cell (s : DeferredStore) (k : DeferredKey) (c : DeferredCell)
    (_h : s.cellAt k = some c) : ProofGraph.Obligation (
    s.poll k = some c.completion) := ⟨⟩

/-- The store bank control: a successful cell lookup determines the poll result. -/
theorem poll_reads_cell (s : DeferredStore) (k : DeferredKey) (c : DeferredCell)
    (h : s.cellAt k = some c) : s.poll k = some c.completion := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
end Effect4.Machine

#typed_state_obligations Effect4.Machine.M1.CompletionSupport ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
