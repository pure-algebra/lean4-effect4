import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Auto.RuleSets

/-!
# Scope entry identities through native store steps

Concept: scope-lifetime-finalization, R11; helper of registration custody.
Consumer: `Program.ReleaseCustody.Execution.command_custody` and its native evaluator clauses.
The invariant reads distinct scope-entry keys and their bound by the fresh-name supply.
Registration keys remain the separate `Stores.ScopeKeysFresh` predicate.
Reach: actual native store steps, with the invariant as premise.
No completed-run, cleanup multiplicity, progress or host claim follows from this helper alone.
-/

set_option autoImplicit false
namespace Effect4.Machine.ScopeIdentity
open Effect4

/-- Every allocated scope has one distinct identity below the supply. -/
def Allocated (scopes : ScopeStore) (next : Nat) : Prop :=
  (scopes.entries.map ScopeEntry.key).Nodup ∧
    ∀ entry ∈ scopes.entries, entry.key < next

theorem Allocated.mono {scopes : ScopeStore} {n m : Nat} (h : Allocated scopes n)
    (le : n ≤ m) : Allocated scopes m :=
  ⟨h.1, fun e he => Nat.lt_of_lt_of_le (h.2 e he) le⟩

theorem keys_setEntry (s : ScopeStore) (entry : ScopeEntry) :
    ((s.setEntry entry).entries.map ScopeEntry.key) = s.entries.map ScopeEntry.key := by
  simp only [ScopeStore.setEntry, List.map_map]
  apply List.map_congr_left
  intro e _
  dsimp only [Function.comp_apply]
  split
  · next h => exact h.symm
  · rfl

theorem Allocated.of_keys {s t : ScopeStore} {n : Nat} (h : Allocated s n)
    (same : t.entries.map ScopeEntry.key = s.entries.map ScopeEntry.key) : Allocated t n := by
  refine ⟨same ▸ h.1, ?_⟩
  intro e he
  have member : e.key ∈ s.entries.map ScopeEntry.key := by
    rw [← same]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨old, member, key⟩ := List.mem_map.mp member
  rw [← key]
  exact h.2 old member

theorem Allocated.setEntry {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (entry : ScopeEntry) : Allocated (s.setEntry entry) n :=
  h.of_keys (keys_setEntry s entry)

theorem Allocated.append {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (scope : ScopeV) : Allocated ⟨s.entries ++ [⟨n, scope⟩]⟩ (n + 1) := by
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨h.1, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb eq
    obtain ⟨entry, member, key⟩ := List.mem_map.mp ha
    have fresh := h.2 entry member
    have bkey := List.mem_singleton.mp hb
    omega
  · intro entry member
    rcases List.mem_append.mp member with old | fresh
    · exact Nat.lt_trans (h.2 entry old) (Nat.lt_succ_self n)
    · cases List.mem_singleton.mp fresh
      exact Nat.lt_succ_self n

theorem Allocated.make {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (strategy : FinalizerStrategy) : Allocated (s.make n strategy) (n + 1) :=
  h.append (Scope.make strategy)

theorem Allocated.removeFinalizer {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (scope key : Nat) : Allocated (s.removeFinalizer scope key) n := by
  unfold ScopeStore.removeFinalizer
  split
  · exact h
  · exact h.setEntry _

theorem Allocated.closeState {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (scope : Nat) (exit : ExitV) : Allocated (s.closeState scope exit) n := by
  unfold ScopeStore.closeState
  split
  · exact h
  · exact h.setEntry _

theorem Allocated.forkChild {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (parent shared : Nat) (strategy : FinalizerStrategy) :
    Allocated (s.forkChild parent n shared strategy) (n + 1) := by
  unfold ScopeStore.forkChild
  split
  · exact h.mono (Nat.le_succ n)
  · exact (h.setEntry _).append _

/-- The empty store owns no scope identities. -/
theorem empty : Allocated Stores.empty.scopes Stores.empty.nextName :=
  ⟨List.nodup_nil, fun _ member => nomatch member⟩

theorem syncOpStep_allocated {s s' : Stores} {o : SyncOp} {v : Val} (hs : Allocated s.scopes s.nextName)
    (h : syncOpStep o s = some (s', v)) : Allocated s'.scopes s'.nextName := by
  cases o with
  | deferredMake =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredIsDone cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredPoll cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredCompleteWith cell completion =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredInterruptWith cell interruptor =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredAwaitCleanup cell waiter token =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | clockNow =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | sleepCancel waiter token =>
    -- the invariant reads nothing of the timer store
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | scopeMake strategy =>
    -- The new scope takes the current supply as its distinct identity.
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact hs.make _
  | scopeAdd scope finalizer =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope finalizer hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        -- a closed scope answers its exit and keeps the store
        rw [syncOpStep_scopeAdd_closed s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      | none =>
        -- Registration keeps scope identities and advances the supply.
        rw [syncOpStep_scopeAdd_open s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]
        exact (hs.setEntry _).mono (Nat.le_succ _)
  | scopeRemove scope key =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact hs.removeFinalizer _ _
  | scopeIsClosed scope =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      -- The child takes the current supply; both allocated names remain below the new supply.
      exact (hs.forkChild _ _ _).mono (Nat.le_succ _)
  | memoFork parent =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact hs.mono (Nat.le_succ _)
  | memoGet layer memoMap =>
    obtain ⟨_, _, hsc, hn, _⟩ := syncOpStep_memoGet_families s s' layer memoMap v h
    change Allocated s'.scopes s'.nextName
    rw [hsc, hn]
    exact hs
  | memoBuild layer memoMap =>
    -- A layer scope takes a fresh identity and advances the supply.
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact hs.make _
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      exact hs
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
  | _ =>
    -- every remaining operation is a `refStep`: only the heap changes
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs

/-- Native store steps keep every finalizer registration key below the actual supply.
Consumer: `Program.Sched.storesOk_syncOpStep` and `ReleaseCustody.Execution.command_custody`.
The proof is the existing store-freshness census, shared without its independent external-store premise. -/
theorem syncOpStep_keysFresh {s s' : Stores} {o : SyncOp} {v : Val} (hs : s.ScopeKeysFresh)
    (h : syncOpStep o s = some (s', v)) : s'.ScopeKeysFresh := by
  cases o with
  | deferredMake =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredIsDone cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredPoll cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredCompleteWith cell completion =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredInterruptWith cell interruptor =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | deferredAwaitCleanup cell waiter token =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | clockNow =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | sleepCancel waiter token =>
    -- the invariant reads nothing of the timer store
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | scopeMake strategy =>
    -- a new scope holds no registrations, and the supply advances past its handle
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact (ScopeStore.keysBelow_make hs).mono (Nat.le_succ _)
  | scopeAdd scope finalizer =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope finalizer hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        -- a closed scope answers its exit and keeps the store
        rw [syncOpStep_scopeAdd_closed s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      | none =>
        -- the registration key is the supply's own value, and the supply advances past it
        rw [syncOpStep_scopeAdd_open s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]
        exact ScopeStore.keysBelow_addUnsafe_entry hs hentry
  | scopeRemove scope key =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact ScopeStore.keysBelow_removeFinalizer hs
  | scopeIsClosed scope =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      -- the shared key is the supply's successor, and the supply advances past both keys
      exact ScopeStore.keysBelow_forkChild (m := s.nextName + 2) (shared := s.nextName + 1)
        hs (Nat.le_add_right _ _) (Nat.lt_succ_self _)
  | memoFork parent =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact hs.mono (Nat.le_succ _)
  | memoGet layer memoMap =>
    obtain ⟨_, _, hsc, hn, _⟩ := syncOpStep_memoGet_families s s' layer memoMap v h
    change ScopeStore.KeysBelow s'.scopes s'.nextName
    rw [hsc, hn]
    exact hs
  | memoBuild layer memoMap =>
    -- a layer scope holds no registrations; the Deferred is fresh; the supply advances
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact (ScopeStore.keysBelow_make hs).mono (Nat.le_succ _)
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      exact hs
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
  | _ =>
    -- every remaining operation is a `refStep`: only the heap changes
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs

/-- Administrative registration retains the allocated scope identities. -/
theorem Allocated.addFinalizer {s : ScopeStore} {n : Nat} (h : Allocated s n)
    (scope key : Nat) (fin : FinName) : Allocated (s.addFinalizer scope key fin).1 n := by
  unfold ScopeStore.addFinalizer
  split
  · exact h
  · exact h.setEntry _

/-- Linking a fiber retains scope identities and advances the actual allocation supply.
Consumer: `ReleaseCustody.Execution.command_custody`, at its native `link` command. -/
theorem scopeLinkFiber_allocated (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {s next : Stores} {key : Nat} (held : Allocated s.scopes s.nextName)
    (step : stores.scopeLinkFiber mode scope fiber s = some (next, key)) :
    Allocated next.scopes next.nextName := by
  dsimp only [stores] at step
  cases found : s.scopes.entryAt scope with
  | none => rw [found] at step; cases step
  | some entry =>
    rw [found] at step
    dsimp only at step
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact (held.addFinalizer scope s.nextName _).mono (Nat.le_succ _)

end Effect4.Machine.ScopeIdentity
