import Effect4.Laws.Machine.Handles
import Effect4.Laws.Auto.Obligations

/-! M1 Handles statement snapshot, recorded before proof attempts. -/
namespace Effect4.Machine.M1.HandlesWanted
open Effect4 Effect4.Machine

def register_keys (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ProofGraph.Obligation (
    (self.register cell waiter token).1.keys ⊆ self.keys ∧
      (∀ p, (self.register cell waiter token).2 = some p → p.keys ⊆ self.keys) ∧
      self.cells.length ≤ (self.register cell waiter token).1.cells.length) := ⟨⟩
#proof_wanted register_keys

def flatMap_resumes_const (ws : List (Waiter Unit)) (e : Completion Val Err Defect FiberId Ann) :
    ProofGraph.Obligation (
    (ws.map fun w => (⟨w.fiber, w.token, e, WakeMode.now⟩ : Owed (Completion Val Err Defect FiberId Ann))).flatMap
        (Owed.keys Completion.keys) ⊆ e.keys) := ⟨⟩
#proof_wanted flatMap_resumes_const

def complete_keys (self : DeferredStore) (cell : DeferredKey) (e : Completion Val Err Defect FiberId Ann) :
    ProofGraph.Obligation (
    (self.complete cell e).1.keys ⊆ self.keys ++ e.keys ∧
      self.cells.length ≤ (self.complete cell e).1.cells.length) := ⟨⟩
#proof_wanted complete_keys

def drainDue_keys (self : DeferredStore) : ProofGraph.Obligation (
    (self.drainDue).2.keys ⊆ self.keys ∧
      (self.drainDue).1.flatMap (Owed.keys Completion.keys) ⊆ self.keys) := ⟨⟩
#proof_wanted drainDue_keys

def owed_mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (_h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (d : Owed κ) : ProofGraph.Obligation (
    (d.mapCode f).keys targetKeys ⊆ d.keys sourceKeys) := ⟨⟩
#proof_wanted owed_mapCode_keys_subset

def owed_flatMap_mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (_h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (ds : List (Owed κ)) : ProofGraph.Obligation (
    (ds.map (Owed.mapCode f)).flatMap (Owed.keys targetKeys) ⊆ ds.flatMap (Owed.keys sourceKeys)) := ⟨⟩
#proof_wanted owed_flatMap_mapCode_keys_subset

def cellAt_keys_subset {self : DeferredStore} {cell : DeferredKey} {c : DeferredCell}
    (_h : self.cellAt cell = some c) : ProofGraph.Obligation (c.keys ⊆ self.keys) := ⟨⟩
#proof_wanted cellAt_keys_subset

def setCell_keys_of_subset (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell)
    (_h : c.keys ⊆ self.keys) : ProofGraph.Obligation ((self.setCell cell c).keys ⊆ self.keys) := ⟨⟩
#proof_wanted setCell_keys_of_subset

def setCell_appendDue_keys (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell)
    (due : List (Owed (Completion Val Err Defect FiberId Ann))) (extra : List Handle)
    (_hc : c.keys ⊆ extra) (_hd : due.flatMap (Owed.keys Completion.keys) ⊆ extra) :
    ProofGraph.Obligation (
    ({ self.setCell cell c with due := self.due ++ due } : DeferredStore).keys ⊆ self.keys ++ extra) := ⟨⟩
#proof_wanted setCell_appendDue_keys

end Effect4.Machine.M1.HandlesWanted
