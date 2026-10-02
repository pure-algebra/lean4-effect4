import Effect4.Machine.Wake

/-!
# Laws.Machine.WakeKeys — the keys a wake list holds, and how its operations move them

One view of the shape every waiting family shares (`Machine/Wake.lean`'s `WakeList`: the timer
store's sleeps, each Deferred cell's waiters): the `(fiber, token)` keys it holds, pending or in a
captured batch. The guard's key bookkeeping (`Guard.internalKeys`) and the typed state's wake
columns (`Typed/Validity.lean`'s `WakeTyped`, decisions row 134 (a), (b)) both read it, so each
operation's effect on the keys is stated once, here: a registration adds its key, a cancel or a
broadcast wake removes keys, running a batch partitions them.
-/

set_option autoImplicit false

namespace Effect4.Program.Guard

open Effect4 Effect4.Machine

abbrev GuardKey := FiberId × Nat

/-- The keys a wake list holds: its pending waiters', then its captured batch's. -/
def wakeKeys {α : Type} (w : WakeList α) : List GuardKey :=
  w.waiters.map (fun a => (a.fiber, a.token)) ++
    w.batch.toList.flatMap (fun b => b.map fun a => (a.fiber, a.token))

/-- A registration adds its own key and keeps every other. -/
theorem wakeKeys_register_mem {α : Type} (wake : WakeList α) (fiber : FiberId)
    (token : Nat) (payload : α) (key : GuardKey) :
    key ∈ wakeKeys (wake.register fiber token payload) ↔
      key ∈ wakeKeys wake ∨ key = (fiber, token) := by
  simp only [wakeKeys, WakeList.register, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

/-- A cancel removes keys. -/
theorem wakeKeys_cancel_subset {α : Type} (wake : WakeList α) (fiber : FiberId) (token : Nat) :
    wakeKeys (wake.cancel fiber token).1 ⊆ wakeKeys wake := by
  unfold WakeList.cancel
  split
  · intro key hk
    rcases List.mem_append.mp hk with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_left _ (List.mem_map.mpr ⟨w, (List.mem_filter.mp hw).1, rfl⟩)
    · exact List.mem_append_right _ h
  · exact List.Subset.refl _

/-- A broadcast wake removes keys. -/
theorem wakeKeys_wakeAll_subset {α : Type} (wake : WakeList α) :
    wakeKeys wake.wakeAll.2 ⊆ wakeKeys wake := by
  intro key hk
  exact List.mem_append_right _ hk

/-- Running a batch partitions the keys: the list's after the run, then the batch's. -/
theorem wakeKeys_runBatch_partition {α : Type} (wake : WakeList α) :
    wakeKeys wake = wakeKeys wake.runBatch.2 ++
      wake.runBatch.1.map (fun w => (w.fiber, w.token)) := by
  cases hb : wake.batch with
  | none =>
    simp only [wakeKeys, WakeList.runBatch, hb, Option.toList, List.flatMap_nil, Option.getD,
      List.map_nil, List.append_nil]
  | some b =>
    simp only [wakeKeys, WakeList.runBatch, hb, Option.toList, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Option.getD]

end Effect4.Program.Guard
