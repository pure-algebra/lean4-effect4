import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Auto.RuleSets

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: scope-field transport serves HeapSites.heap_sites_keep and Workers.Assertions.logs_step.
Reach: predicates over existing scope finalizers and strategies, actual sync operations and state-first closes.
Limit: the operation producer must supply the predicate for every newly registered finalizer.
Consumers: existing native source ownership and actual Workers captured connection slots.
-/
set_option autoImplicit false
namespace Effect4.Machine.ScopeFields
open Effect4 Effect4.Machine

/-- Administrative fork finalizers and sequential allocation satisfy the supplied field predicate. -/
structure Model where
  finalizer : FinName → Prop
  strategy : FinalizerStrategy → Prop
  sequential : strategy .sequential
  closeChild : ∀ child, finalizer (.closeChildScope child)
  detach : ∀ parent key, finalizer (.detachFromParent parent key)

/-- Only registration and allocation operations introduce these scope fields. -/
def OperationAt (model : Model) : SyncOp → Prop
  | .scopeAdd _ fin => model.finalizer fin
  | .scopeMake strategy | .scopeFork _ strategy => model.strategy strategy
  | _ => True

/-- Registered finalizers retain their actual captured release scopes. -/
def ScopeAt (model : Model) (scope : ScopeV) : Prop :=
  (∀ entry ∈ scope.finalizers, model.finalizer entry.2) ∧ model.strategy scope.strategy

/-- Every scope row retains the captures it can later close. -/
def ScopesAt (model : Model) (store : ScopeStore) : Prop :=
  ∀ entry ∈ store.entries, ScopeAt model entry.scope

/-- Replacing a keyed slot retains the new capture and all old surviving captures. -/
theorem table_insert_at (model : Model) (table : List (Nat × FinName)) (key : Nat) (fin : FinName)
    (owned : ∀ entry ∈ table, model.finalizer entry.2) (capture : model.finalizer fin) :
    ∀ entry ∈ Scope.tableInsert table key fin, model.finalizer entry.2 := by
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
theorem scope_add_at (model : Model) (scope : ScopeV) (key : Nat) (fin : FinName)
    (owned : ScopeAt model scope) (capture : model.finalizer fin) :
    ScopeAt model (scope.addUnsafe key fin) := by
  refine ⟨?_, owned.2⟩
  change ∀ entry ∈ (scope.addUnsafe key fin).state.entries, model.finalizer entry.2
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
    apply table_insert_at model _ key fin _ capture
    intro entry member
    apply owned.1 entry
    change entry ∈ scope.state.entries
    rw [h]
    exact member
  case openMap table =>
    rw [Scope.addUnsafe_openMap scope table key fin h]
    apply table_insert_at model table key fin _ capture
    intro entry member
    apply owned.1 entry
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
theorem scope_set_at (model : Model) (store : ScopeStore) (entry : ScopeEntry)
    (owned : ScopesAt model store) (new : ScopeAt model entry.scope) : ScopesAt model (store.setEntry entry) := by
  intro other member
  rcases ScopeStore.mem_setEntry member with same | old
  · rw [same]; exact new
  · exact owned other old

/-- The actual lookup returns a scope row already owned by the store. -/
theorem scope_lookup_at (model : Model) (store : ScopeStore) (key : Nat) (entry : ScopeEntry)
    (owned : ScopesAt model store) (found : store.entryAt key = some entry) : ScopeAt model entry.scope :=
  owned entry (List.mem_of_find?_eq_some found)

/-- A newly allocated scope has no source-bearing finalizer. -/
theorem scope_make_at (model : Model) (store : ScopeStore) (key : Nat) (strategy : FinalizerStrategy)
    (owned : ScopesAt model store) (strategyOwned : model.strategy strategy) : ScopesAt model (store.make key strategy) := by
  intro entry member
  rcases List.mem_append.mp member with old | new
  · exact owned entry old
  · rw [List.mem_singleton.mp new]
    exact ⟨fun _ present => False.elim (List.not_mem_nil present), strategyOwned⟩

/-- Registering into an actual store keeps its captured release points. -/
theorem scope_register_at (model : Model) (store : ScopeStore) (scope key : Nat) (fin : FinName)
    (owned : ScopesAt model store) (capture : model.finalizer fin) :
    ScopesAt model (store.addFinalizer scope key fin).1 := by
  unfold ScopeStore.addFinalizer
  split
  · exact owned
  · rename_i entry found
    have old := scope_lookup_at model store scope entry owned found
    change ScopesAt model (store.setEntry {entry with scope := (Scope.addExit finExit entry.scope key fin).1})
    unfold Scope.addExit
    split
    · exact scope_set_at model store _ owned old
    · exact scope_set_at model store _ owned (scope_add_at model entry.scope key fin old capture)

/-- Removing a registration retains only previously owned captures. -/
theorem scope_remove_at (model : Model) (store : ScopeStore) (scope key : Nat)
    (owned : ScopesAt model store) : ScopesAt model (store.removeFinalizer scope key) := by
  unfold ScopeStore.removeFinalizer
  split
  · exact owned
  · rename_i entry found
    apply scope_set_at model store _ owned
    refine ⟨?_, (scope_lookup_at model store scope entry owned found).2⟩
    intro fin member
    apply (scope_lookup_at model store scope entry owned found).1 fin
    exact (Scope.removeUnsafe_finalizers_sublist entry.scope key).subset member

/-- Closing removes registered captures from the state before running them. -/
theorem scope_close_at (model : Model) (store : ScopeStore) (scope : Nat) (exit : ExitV)
    (owned : ScopesAt model store) : ScopesAt model (store.closeState scope exit) := by
  unfold ScopeStore.closeState
  split
  · exact owned
  · rename_i entry found
    apply scope_set_at model store _ owned
    refine ⟨?_, ?_⟩
    · intro fin member
      rw [Scope.closeState_finalizers] at member
      cases member
    · simpa only [Scope.closeState_strategy] using (scope_lookup_at model store scope entry owned found).2


/-- Forked scopes add only administrative close and detach finalizers. -/
theorem scope_fork_at (model : Model) (store : ScopeStore) (parent child shared : Nat)
    (strategy : FinalizerStrategy) (owned : ScopesAt model store) (strategyOwned : model.strategy strategy) :
    ScopesAt model (store.forkChild parent child shared strategy) := by
  unfold ScopeStore.forkChild
  split
  · exact owned
  · rename_i entry found
    have old := scope_lookup_at model store parent entry owned found
    change ScopesAt model {entries := (store.setEntry {entry with scope := (Scope.fork entry.scope strategy shared (.closeChildScope child) (.detachFromParent parent shared)).1}).entries ++ [⟨child, (Scope.fork entry.scope strategy shared (.closeChildScope child) (.detachFromParent parent shared)).2⟩]}
    unfold Scope.fork
    split
    · intro other member
      rcases List.mem_append.mp member with before | fresh
      · exact scope_set_at model store _ owned old other before
      · rw [List.mem_singleton.mp fresh]
        exact ⟨fun _ present => False.elim (List.not_mem_nil present), strategyOwned⟩
    · intro other member
      rcases List.mem_append.mp member with before | fresh
      · exact scope_set_at model store _ owned (scope_add_at model entry.scope shared (.closeChildScope child) old (model.closeChild child)) other before
      · rw [List.mem_singleton.mp fresh]
        apply scope_add_at model (Scope.make strategy) shared (.detachFromParent parent shared) _ (model.detach parent shared)
        exact ⟨fun _ present => False.elim (List.not_mem_nil present), strategyOwned⟩

/-- A close order contains only registered source captures. -/
theorem close_order_at (model : Model) (scope : ScopeV) (owned : ScopeAt model scope) :
    ∀ fin ∈ scope.closeOrder, model.finalizer fin := by
  rw [Scope.closeOrder_eq]
  intro fin member
  obtain ⟨entry, present, eq⟩ := List.mem_map.mp (List.mem_reverse.mp member)
  rw [← eq]
  exact owned.1 entry present

/-- The native synchronous store command retains every saved finalizer capture. -/
theorem sync_scopes_at (model : Model) (op : SyncOp) (state next : Stores) (answer : Val)
    (owned : ScopesAt model state.scopes) (operation : OperationAt model op)
    (found : syncOpStep op state = some (next, answer)) : ScopesAt model next.scopes := by
  cases op
  all_goals unfold syncOpStep at found
  all_goals repeat' split at found
  all_goals aesop (add norm simp [OperationAt]) (add norm unfold [syncOpStep, refStep]) (add safe apply [scope_set_at, scope_make_at, scope_add_at, scope_remove_at, scope_fork_at]) (add safe forward [scope_lookup_at]) (add safe apply [model.sequential])

/-- State-first close retains the store and the actual captured close order. -/
theorem close_snapshot_at (model : Model) (scope : Nat) (exit : ExitV) (state next : Stores)
    (strategy : FinalizerStrategy) (order : List FinName) (owned : ScopesAt model state.scopes)
    (found : scopeCloseSnapshot scope exit state = some (next, strategy, order)) :
    ScopesAt model next.scopes ∧ (∀ fin ∈ order, model.finalizer fin) ∧ model.strategy strategy := by
  unfold scopeCloseSnapshot at found
  cases h : state.scopes.entryAt scope with
  | none => rw [h] at found; cases found
  | some entry =>
    simp only [h, Option.pure_def] at found
    rcases found with ⟨rfl, rfl, rfl⟩
    exact ⟨scope_close_at model state.scopes scope exit owned,
      close_order_at model entry.scope (scope_lookup_at model state.scopes scope entry owned h),
      (scope_lookup_at model state.scopes scope entry owned h).2⟩

end Effect4.Machine.ScopeFields
