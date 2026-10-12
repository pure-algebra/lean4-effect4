import Effect4.Laws.Program.NativeStoreScope
import Effect4.Laws.Machine.ScopeFields

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The scope store retains the source-bearing captures of its actual finalizer entries.
The laws follow registration, removal and state-first close without a key-freshness premise.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The existing source predicates instantiate the shared scope-field transport. -/
def scopeFieldsModel (root : NativeEff) : ScopeFields.Model where
  finalizer := FinAt root
  strategy := StrategyAt root
  sequential := Or.inl rfl
  closeChild := fun _ => trivial
  detach := fun _ _ => trivial

/-- Registered finalizers retain their actual captured release scopes. -/
def ScopeAt (root : NativeEff) (scope : ScopeV) : Prop :=
  ScopeFields.ScopeAt (scopeFieldsModel root) scope

/-- Every scope row retains the captures it can later close. -/
def ScopesAt (root : NativeEff) (store : ScopeStore) : Prop :=
  ScopeFields.ScopesAt (scopeFieldsModel root) store

/-- Replacing a keyed slot retains the new capture and all old surviving captures. -/
theorem table_insert_at (root : NativeEff) (table : List (Nat × FinName)) (key : Nat) (fin : FinName)
    (owned : ∀ entry ∈ table, FinAt root entry.2) (capture : FinAt root fin) :
    ∀ entry ∈ Scope.tableInsert table key fin, FinAt root entry.2 := by
  exact ScopeFields.table_insert_at (scopeFieldsModel root) table key fin owned capture

/-- Registration retains its capture even when a key replaces an existing slot. -/
theorem scope_add_at (root : NativeEff) (scope : ScopeV) (key : Nat) (fin : FinName)
    (owned : ScopeAt root scope) (capture : FinAt root fin) :
    ScopeAt root (scope.addUnsafe key fin) := by
  exact ScopeFields.scope_add_at (scopeFieldsModel root) scope key fin owned capture

/-- Replacing a store row retains all surviving rows and the new row's captures. -/
theorem scope_set_at (root : NativeEff) (store : ScopeStore) (entry : ScopeEntry)
    (owned : ScopesAt root store) (new : ScopeAt root entry.scope) : ScopesAt root (store.setEntry entry) := by
  exact ScopeFields.scope_set_at (scopeFieldsModel root) store entry owned new

/-- The actual lookup returns a scope row already owned by the store. -/
theorem scope_lookup_at (root : NativeEff) (store : ScopeStore) (key : Nat) (entry : ScopeEntry)
    (owned : ScopesAt root store) (found : store.entryAt key = some entry) : ScopeAt root entry.scope := by
  exact ScopeFields.scope_lookup_at (scopeFieldsModel root) store key entry owned found

/-- A newly allocated scope has no source-bearing finalizer. -/
theorem scope_make_at (root : NativeEff) (store : ScopeStore) (key : Nat) (strategy : FinalizerStrategy)
    (owned : ScopesAt root store) (strategyOwned : StrategyAt root strategy) : ScopesAt root (store.make key strategy) := by
  exact ScopeFields.scope_make_at (scopeFieldsModel root) store key strategy owned strategyOwned

/-- Registering into an actual store keeps its captured release points. -/
theorem scope_register_at (root : NativeEff) (store : ScopeStore) (scope key : Nat) (fin : FinName)
    (owned : ScopesAt root store) (capture : FinAt root fin) :
    ScopesAt root (store.addFinalizer scope key fin).1 := by
  exact ScopeFields.scope_register_at (scopeFieldsModel root) store scope key fin owned capture

/-- Removing a registration retains only previously owned captures. -/
theorem scope_remove_at (root : NativeEff) (store : ScopeStore) (scope key : Nat)
    (owned : ScopesAt root store) : ScopesAt root (store.removeFinalizer scope key) := by
  exact ScopeFields.scope_remove_at (scopeFieldsModel root) store scope key owned

/-- Closing removes registered captures from the state before running them. -/
theorem scope_close_at (root : NativeEff) (store : ScopeStore) (scope : Nat) (exit : ExitV)
    (owned : ScopesAt root store) : ScopesAt root (store.closeState scope exit) := by
  exact ScopeFields.scope_close_at (scopeFieldsModel root) store scope exit owned

/-- Forked scopes add only administrative close and detach finalizers. -/
theorem scope_fork_at (root : NativeEff) (store : ScopeStore) (parent child shared : Nat)
    (strategy : FinalizerStrategy) (owned : ScopesAt root store) (strategyOwned : StrategyAt root strategy) :
    ScopesAt root (store.forkChild parent child shared strategy) := by
  exact ScopeFields.scope_fork_at (scopeFieldsModel root) store parent child shared strategy owned strategyOwned

/-- A close order contains only registered source captures. -/
theorem close_order_at (root : NativeEff) (scope : ScopeV) (owned : ScopeAt root scope) :
    ∀ fin ∈ scope.closeOrder, FinAt root fin := by
  exact ScopeFields.close_order_at (scopeFieldsModel root) scope owned

/-- The native synchronous store command retains every saved finalizer capture. -/
theorem sync_scopes_at (root : NativeEff) (op : SyncOp) (state next : Stores) (answer : Val)
    (owned : ScopesAt root state.scopes) (operation : OpAt root op)
    (found : syncOpStep op state = some (next, answer)) : ScopesAt root next.scopes := by
  apply ScopeFields.sync_scopes_at (scopeFieldsModel root) op state next answer owned _ found
  cases op <;> aesop (add norm unfold [ScopeFields.OperationAt, scopeFieldsModel, OpAt])

/-- State-first close retains the store and the actual captured close order. -/
theorem close_snapshot_at (root : NativeEff) (scope : Nat) (exit : ExitV) (state next : Stores)
    (strategy : FinalizerStrategy) (order : List FinName) (owned : ScopesAt root state.scopes)
    (found : scopeCloseSnapshot scope exit state = some (next, strategy, order)) :
    ScopesAt root next.scopes ∧ (∀ fin ∈ order, FinAt root fin) ∧ StrategyAt root strategy := by
  exact ScopeFields.close_snapshot_at (scopeFieldsModel root) scope exit state next strategy order owned found

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
          exact finProgram_at root fin exit (slots.2.1 fin (.head _))⟩
      | cons second tail =>
        cases found
        exact ⟨slots.1, fun code member => by
          rw [Option.mem_def] at member
          cases member
          exact slots.2⟩

/-- Public close returns the same owned finalizers and its administrative void continuation. -/
theorem close_public_at (root : NativeEff) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (owned : ScopesAt root state.scopes)
    (found : storesCloseScope scope exit flag state = some (next, program)) :
    ScopesAt root next.scopes ∧ ∀ code, program = some code → CodeAt root (embed code) := by
  unfold storesCloseScope at found
  cases h : scopeCloseSnapshot scope exit state with
  | none => rw [h] at found; cases found
  | some snapshot =>
    rcases snapshot with ⟨after, strategy, order⟩
    have slots := close_snapshot_at root scope exit state after strategy order owned h
    simp only [h, Option.pure_def] at found
    cases order with
    | nil => cases found; exact ⟨slots.1, fun _ none => by cases none⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        exact ⟨slots.1, fun _ same => by
          cases same
          exact ⟨finProgram_at root fin exit (slots.2.1 fin (.head _)), trivial⟩⟩
      | cons second tail => cases found; exact ⟨slots.1, fun _ same => by cases same; exact slots.2⟩

end Effect4.Program.SourceScope
