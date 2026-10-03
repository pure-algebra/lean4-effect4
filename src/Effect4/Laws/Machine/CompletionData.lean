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

/-- A successful list lookup supplies the bound needed by the store write/read law. -/
theorem store_lookup_lt {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h
  exact bound

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] store_lookup_lt

section OwedMap
universe u v w
variable {κ : Type u} {κ' : Type v} {κ'' : Type w}

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

end OwedMap

end Effect4.Machine

namespace Effect4.Machine.M1.Core
open Effect4 Effect4.Machine

end Effect4.Machine.M1.Core

namespace Effect4.Machine
/-- The store bank control: a successful cell lookup determines the poll result. -/
theorem poll_reads_cell (s : DeferredStore) (k : DeferredKey) (c : DeferredCell)
    (h : s.cellAt k = some c) : s.poll k = some c.completion := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
end Effect4.Machine
