import Effect4.Laws.Program.NativeStoreScope

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The scope store retains the source-bearing captures of its actual finalizer entries.
The laws follow registration, removal and state-first close without a key-freshness premise.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- Registered finalizers retain their actual captured release scopes. -/
def ScopeAt (root : NativeEff) (scope : ScopeV) : Prop :=
  ∀ entry ∈ scope.finalizers, FinAt root entry.2

/-- Every scope row retains the captures it can later close. -/
def ScopesAt (root : NativeEff) (store : ScopeStore) : Prop :=
  ∀ entry ∈ store.entries, ScopeAt root entry.scope

/-- Replacing a keyed slot retains the new capture and all old surviving captures. -/
theorem table_insert_at (root : NativeEff) (table : List (Nat × FinName)) (key : Nat) (fin : FinName)
    (owned : ∀ entry ∈ table, FinAt root entry.2) (capture : FinAt root fin) :
    ∀ entry ∈ Scope.tableInsert table key fin, FinAt root entry.2 := by
  unfold Scope.tableInsert
  split
  · intro entry member
    obtain ⟨old, present, eq⟩ := List.mem_map.mp member
    rw [← eq]
    split
    · exact capture
    · exact owned old present
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · exact owned entry old
    · rw [List.mem_singleton.mp new]
      exact capture

/-- Registration retains its capture even when a key replaces an existing slot. -/
theorem scope_add_at (root : NativeEff) (scope : ScopeV) (key : Nat) (fin : FinName)
    (owned : ScopeAt root scope) (capture : FinAt root fin) :
    ScopeAt root (scope.addUnsafe key fin) := by
  unfold ScopeAt
  change ∀ entry ∈ (scope.addUnsafe key fin).state.entries, FinAt root entry.2
  cases h : scope.state
  case empty =>
    rw [Scope.addUnsafe_empty scope key fin h]
    intro entry member
    rw [List.mem_singleton.mp member]
    exact capture
  case openEmpty =>
    rw [Scope.addUnsafe_openEmpty scope key fin h]
    intro entry member
    rw [List.mem_singleton.mp member]
    exact capture
  case openInline oldKey old =>
    rw [Scope.addUnsafe_openInline scope oldKey key old fin h]
    apply table_insert_at root _ key fin _ capture
    intro entry member
    apply owned entry
    change entry ∈ scope.state.entries
    rw [h]
    exact member
  case openMap table =>
    rw [Scope.addUnsafe_openMap scope table key fin h]
    apply table_insert_at root table key fin _ capture
    intro entry member
    apply owned entry
    change entry ∈ scope.state.entries
    rw [h]
    exact member
  case closed exit =>
    rw [Scope.addUnsafe_closed scope key fin (by change scope.state.isClosed = true; rw [h]; rfl)]
    intro entry member
    change entry ∈ scope.state.entries at member
    rw [h] at member
    cases member

/-- Replacing a store row retains all surviving rows and the new row's captures. -/
theorem scope_set_at (root : NativeEff) (store : ScopeStore) (entry : ScopeEntry)
    (owned : ScopesAt root store) (new : ScopeAt root entry.scope) : ScopesAt root (store.setEntry entry) := by
  intro other member
  rcases ScopeStore.mem_setEntry member with same | old
  · rw [same]; exact new
  · exact owned other old

/-- The actual lookup returns a scope row already owned by the store. -/
theorem scope_lookup_at (root : NativeEff) (store : ScopeStore) (key : Nat) (entry : ScopeEntry)
    (owned : ScopesAt root store) (found : store.entryAt key = some entry) : ScopeAt root entry.scope :=
  owned entry (List.mem_of_find?_eq_some found)

/-- A newly allocated scope has no source-bearing finalizer. -/
theorem scope_make_at (root : NativeEff) (store : ScopeStore) (key : Nat) (strategy : FinalizerStrategy)
    (owned : ScopesAt root store) : ScopesAt root (store.make key strategy) := by
  intro entry member
  rcases List.mem_append.mp member with old | new
  · exact owned entry old
  · rw [List.mem_singleton.mp new]
    intro fin present
    cases present

/-- Registering into an actual store keeps its captured release points. -/
theorem scope_register_at (root : NativeEff) (store : ScopeStore) (scope key : Nat) (fin : FinName)
    (owned : ScopesAt root store) (capture : FinAt root fin) :
    ScopesAt root (store.addFinalizer scope key fin).1 := by
  unfold ScopeStore.addFinalizer
  split
  · exact owned
  · rename_i entry found
    have old := scope_lookup_at root store scope entry owned found
    change ScopesAt root (store.setEntry {entry with scope := (Scope.addExit finExit entry.scope key fin).1})
    unfold Scope.addExit
    split
    · exact scope_set_at root store _ owned old
    · exact scope_set_at root store _ owned (scope_add_at root entry.scope key fin old capture)

/-- Removing a registration retains only previously owned captures. -/
theorem scope_remove_at (root : NativeEff) (store : ScopeStore) (scope key : Nat)
    (owned : ScopesAt root store) : ScopesAt root (store.removeFinalizer scope key) := by
  unfold ScopeStore.removeFinalizer
  split
  · exact owned
  · rename_i entry found
    apply scope_set_at root store _ owned
    intro fin member
    apply scope_lookup_at root store scope entry owned found fin
    exact (Scope.removeUnsafe_finalizers_sublist entry.scope key).subset member

/-- Closing removes registered captures from the state before running them. -/
theorem scope_close_at (root : NativeEff) (store : ScopeStore) (scope : Nat) (exit : ExitV)
    (owned : ScopesAt root store) : ScopesAt root (store.closeState scope exit) := by
  unfold ScopeStore.closeState
  split
  · exact owned
  · apply scope_set_at root store _ owned
    intro fin member
    rw [Scope.closeState_finalizers] at member
    cases member

/-- Forked scopes add only administrative close and detach finalizers. -/
theorem scope_fork_at (root : NativeEff) (store : ScopeStore) (parent child shared : Nat)
    (strategy : FinalizerStrategy) (owned : ScopesAt root store) :
    ScopesAt root (store.forkChild parent child shared strategy) := by
  unfold ScopeStore.forkChild
  split
  · exact owned
  · rename_i entry found
    have old := scope_lookup_at root store parent entry owned found
    change ScopesAt root {entries := (store.setEntry {entry with scope := (Scope.fork entry.scope strategy shared (.closeChildScope child) (.detachFromParent parent shared)).1}).entries ++ [⟨child, (Scope.fork entry.scope strategy shared (.closeChildScope child) (.detachFromParent parent shared)).2⟩]}
    unfold Scope.fork
    split
    · intro other member
      rcases List.mem_append.mp member with before | fresh
      · exact scope_set_at root store _ owned old other before
      · rw [List.mem_singleton.mp fresh]
        intro fin present
        cases present
    · intro other member
      rcases List.mem_append.mp member with before | fresh
      · exact scope_set_at root store _ owned (scope_add_at root entry.scope shared (.closeChildScope child) old trivial) other before
      · rw [List.mem_singleton.mp fresh]
        apply scope_add_at root (Scope.make strategy) shared (.detachFromParent parent shared) _ trivial
        intro fin present
        cases present

/-- A close order contains only registered source captures. -/
theorem close_order_at (root : NativeEff) (scope : ScopeV) (owned : ScopeAt root scope) :
    ∀ fin ∈ scope.closeOrder, FinAt root fin := by
  rw [Scope.closeOrder_eq]
  intro fin member
  obtain ⟨entry, present, eq⟩ := List.mem_map.mp (List.mem_reverse.mp member)
  rw [← eq]
  exact owned entry present

/-- The native synchronous store command retains every saved finalizer capture. -/
theorem sync_scopes_at (root : NativeEff) (op : SyncOp) (state next : Stores) (answer : Val)
    (owned : ScopesAt root state.scopes) (operation : OpAt root op)
    (found : syncOpStep op state = some (next, answer)) : ScopesAt root next.scopes := by
  cases op
  all_goals unfold syncOpStep at found
  all_goals repeat' split at found
  all_goals aesop (add norm simp [OpAt]) (add norm unfold [syncOpStep, refStep]) (add safe apply [scope_set_at, scope_make_at, scope_add_at, scope_remove_at, scope_fork_at]) (add safe forward [scope_lookup_at])

/-- State-first close retains the store and the actual captured close order. -/
theorem close_snapshot_at (root : NativeEff) (scope : Nat) (exit : ExitV) (state next : Stores)
    (strategy : FinalizerStrategy) (order : List FinName) (owned : ScopesAt root state.scopes)
    (found : scopeCloseSnapshot scope exit state = some (next, strategy, order)) :
    ScopesAt root next.scopes ∧ ∀ fin ∈ order, FinAt root fin := by
  unfold scopeCloseSnapshot at found
  cases h : state.scopes.entryAt scope with
  | none => rw [h] at found; cases found
  | some entry =>
    simp only [h, Option.pure_def] at found
    rcases found with ⟨rfl, rfl, rfl⟩
    exact ⟨scope_close_at root state.scopes scope exit owned,
      close_order_at root entry.scope (scope_lookup_at root state.scopes scope entry owned h)⟩

/-- Unsafe close returns only programs from the captured finalizer order. -/
theorem close_unsafe_at (root : NativeEff) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (owned : ScopesAt root state.scopes)
    (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    ScopesAt root next.scopes ∧ ∀ code ∈ program, CodeAt root (embed code) := by
  unfold storesCloseScopeUnsafe at found
  cases h : scopeCloseSnapshot scope exit state with
  | none => rw [h] at found; cases found
  | some snapshot =>
    rcases snapshot with ⟨after, strategy, order⟩
    have slots := close_snapshot_at root scope exit state after strategy order owned h
    simp only [h, Option.pure_def] at found
    cases order with
    | nil =>
      cases found
      exact ⟨slots.1, by intro code member; cases member⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        exact ⟨slots.1, fun code member => by
          rw [Option.mem_def] at member
          cases member
          exact finProgram_at root fin exit (slots.2 fin (.head _))⟩
      | cons second tail =>
        cases found
        exact ⟨slots.1, fun code member => by
          rw [Option.mem_def] at member
          cases member
          exact slots.2⟩

/-- Public close returns the same owned finalizers and its administrative void continuation. -/
theorem close_public_at (root : NativeEff) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Program) (owned : ScopesAt root state.scopes)
    (found : storesCloseScope scope exit flag state = some (next, program)) :
    ScopesAt root next.scopes ∧ CodeAt root (embed program) := by
  unfold storesCloseScope at found
  cases h : scopeCloseSnapshot scope exit state with
  | none => rw [h] at found; cases found
  | some snapshot =>
    rcases snapshot with ⟨after, strategy, order⟩
    have slots := close_snapshot_at root scope exit state after strategy order owned h
    simp only [h, Option.pure_def] at found
    cases order with
    | nil => cases found; exact ⟨slots.1, trivial⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        exact ⟨slots.1, finProgram_at root fin exit (slots.2 fin (.head _)), trivial⟩
      | cons second tail => cases found; exact ⟨slots.1, slots.2⟩

end Effect4.Program.SourceScope
