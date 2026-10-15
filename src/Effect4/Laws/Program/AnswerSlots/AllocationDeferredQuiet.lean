import Effect4.Laws.Program.AnswerSlots.AllocationRecorded

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared pending configuration and Atomic's actual entry heap.
Pending initialization has no owed deferred answers and no captured wake batch.
The existing native and administrative producers carry this relative store assertion.
This assertion does not restrict application deferred operations after entry.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Pending deferred cells owe no answer and capture no scheduled wake batch. -/
def DeferredQuiet (store : DeferredStore) : Prop :=
  store.due = [] ∧ ∀ cell ∈ store.cells, cell.wake.batch = none

/-- A wake list without a captured batch returns its unchanged empty batch result. -/
theorem runBatch_no_batch (wake : WakeList Unit) (empty : wake.batch = none) :
    wake.runBatch = ([], wake) := by
  cases wake with
  | mk waiters batch phase =>
    dsimp only at empty
    cases empty
    rfl

/-- The actual wake of a pending deferred cell cannot manufacture an owed answer. -/
theorem DeferredQuiet.wake (store : DeferredStore) (key : DeferredKey) (quiet : DeferredQuiet store) :
    store.wakeBatch key = store := by
  unfold DeferredStore.wakeBatch
  cases found : store.cellAt key with
  | none => rfl
  | some cell =>
    have member : cell ∈ store.cells := List.mem_of_getElem? found
    have run := runBatch_no_batch cell.wake (quiet.2 cell member)
    have same : store.setCell key cell = store := by
      obtain ⟨bound, equal⟩ := List.getElem_of_getElem? found
      unfold DeferredStore.setCell
      rw [← equal, List.set_getElem_self bound]
    cases cell with
    | mk completion wake =>
      cases completion <;>
        simpa only [run, List.map_nil, List.append_nil, DeferredStore.setCell] using same

end Effect4.Program.AnswerSlots.AllocationAdapter
