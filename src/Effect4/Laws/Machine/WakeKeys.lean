import Effect4.Machine.Wake

/-!
# Laws.Machine.WakeKeys — the keys a wake list holds, and how its operations move them

One view of the shape every waiting family shares (`Machine/Wake.lean`'s `WakeList`: the timer
store's sleeps, each Deferred cell's waiters): the `(fiber, token)` keys it holds, pending or in a
captured batch. The guard's key bookkeeping (`Guard.internalKeys`) and the typed state's wake
columns (`Typed/Validity.lean`'s `WakeTyped`, decisions row 134 (a), (b)) both read it, so each
operation's effect on the keys is stated once, here: a registration adds its key; a cancel, a
chosen wake (the timer's fire) or a broadcast wake removes keys; running a batch partitions them.
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

/-- A pending waiter's key is its list's. -/
theorem wakeKeys_waiter_mem {α : Type} {wake : WakeList α} {w : Waiter α} (h : w ∈ wake.waiters) :
    (w.fiber, w.token) ∈ wakeKeys wake :=
  List.mem_append_left _ (List.mem_map.mpr ⟨w, h, rfl⟩)

/-- A chosen wake (`WakeList.wakeBy`, the timer store's fire) removes keys. -/
theorem wakeKeys_wakeBy_subset {α : Type} [DecidableEq α] (wake : WakeList α)
    (choose : List (Waiter α) → Option (Waiter α)) :
    wakeKeys (wake.wakeBy choose).2 ⊆ wakeKeys wake := by
  unfold WakeList.wakeBy
  split
  · exact List.Subset.refl _
  · intro key hk
    rcases List.mem_append.mp hk with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      exact wakeKeys_waiter_mem (List.mem_of_mem_erase hx)
    · exact List.mem_append_right _ h

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

/-- After a run, the list holds a subset of its keys. -/
theorem wakeKeys_runBatch_subset {α : Type} (wake : WakeList α) :
    wakeKeys wake.runBatch.2 ⊆ wakeKeys wake := by
  rw [wakeKeys_runBatch_partition wake]
  exact List.subset_append_left _ _

/-- A batch with nothing to deliver rejoins the pending list: the keys are kept. -/
theorem wakeKeys_rejoin_subset {α : Type} (wake : WakeList α) :
    wakeKeys { wake.runBatch.2 with waiters := wake.runBatch.2.waiters ++ wake.runBatch.1 } ⊆
      wakeKeys wake := by
  intro key hk
  rw [wakeKeys_runBatch_partition wake]
  rcases List.mem_append.mp hk with h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (wakeKeys_waiter_mem ha)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · cases h

end Effect4.Program.Guard
