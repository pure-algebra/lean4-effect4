import Effect4.Laws.Machine.ScopeIdentity

/-!
Concept: scope-lifetime-finalization R11, serving the actual Workers release-history obligation.
Consumer: the sequential-scope fragment of native release custody.
The assertion reads the existing scope strategy and assumes sequential allocation or fork steps.
Source provenance must discharge that premise; this module proves no such source fact or history closure.
-/
set_option autoImplicit false
namespace Effect4.Machine.ScopeSequential
open Effect4

/-- Every existing scope closes its finalizers sequentially. -/
def Held (s : ScopeStore) : Prop := ∀ entry ∈ s.entries, entry.scope.strategy = .sequential

/-- Only allocation and scope fork choose a new physical scope strategy. -/
def AllocatesSequential : SyncOp → Prop
  | .scopeMake strategy | .scopeFork _ strategy => strategy = .sequential
  | _ => True

theorem empty : Held Stores.empty.scopes := fun _ member => nomatch member

theorem Held.setEntry {s : ScopeStore} (held : Held s) (entry : ScopeEntry)
    (sequential : entry.scope.strategy = .sequential) : Held (s.setEntry entry) := by
  intro row member
  obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
  rw [← equal]
  split
  · exact sequential
  · exact held old oldMember

theorem Held.append {s : ScopeStore} (held : Held s) (key : Nat) (scope : ScopeV)
    (sequential : scope.strategy = .sequential) : Held ⟨s.entries ++ [⟨key, scope⟩]⟩ := by
  intro row member
  rcases List.mem_append.mp member with old | added
  · exact held row old
  · cases List.mem_singleton.mp added
    exact sequential

theorem Held.make {s : ScopeStore} (held : Held s) (key : Nat) :
    Held (s.make key .sequential) := held.append key _ rfl

theorem Held.remove {s : ScopeStore} (held : Held s) (scope key : Nat) :
    Held (s.removeFinalizer scope key) := by
  unfold ScopeStore.removeFinalizer
  split
  · exact held
  · rename_i entry found
    exact held.setEntry _ (held entry (List.mem_of_find?_eq_some found))

theorem Held.close {s : ScopeStore} (held : Held s) (scope : Nat) (exit : ExitV) :
    Held (s.closeState scope exit) := by
  unfold ScopeStore.closeState
  split
  · exact held
  · rename_i entry found
    apply held.setEntry
    exact (Scope.closeState_strategy entry.scope exit).trans (held entry (List.mem_of_find?_eq_some found))

theorem Held.add {s : ScopeStore} (held : Held s) (scope key : Nat) (fin : FinName) :
    Held (s.addFinalizer scope key fin).1 := by
  unfold ScopeStore.addFinalizer
  split
  · exact held
  · rename_i entry found
    have strategy := held entry (List.mem_of_find?_eq_some found)
    cases closing : entry.scope.closingExit? <;>
      simp only [Scope.addExit, closing] <;> exact held.setEntry _ strategy

theorem Held.fork {s : ScopeStore} (held : Held s) (parent child shared : Nat) :
    Held (s.forkChild parent child shared .sequential) := by
  unfold ScopeStore.forkChild
  split
  · exact held
  · rename_i entry found
    have parentStrategy :
        (Scope.fork entry.scope .sequential shared (.closeChildScope child)
          (.detachFromParent parent shared)).1.strategy = .sequential := by
      unfold Scope.fork
      split <;> exact held entry (List.mem_of_find?_eq_some found)
    exact (held.setEntry _ parentStrategy).append child _ (Scope.fork_child_strategy ..)

/-- Every actual native store operation retains sequential scopes when its allocation does. -/
theorem sync_step {s next : Stores} {op : SyncOp} {value : Val}
    (held : Held s.scopes) (allocation : AllocatesSequential op)
    (step : syncOpStep op s = some (next, value)) : Held next.scopes := by
  cases op with
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | clockNow | sleepCancel _ _ | memoFork _ =>
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact held
  | deferredIsDone _ | deferredPoll _ | scopeIsClosed _ =>
    simp only [syncOpStep, Option.map_eq_some_iff] at step
    obtain ⟨_, _, result⟩ := step
    rw [← (Prod.mk.inj result).1]
    exact held
  | scopeMake strategy =>
    change strategy = .sequential at allocation
    subst strategy
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact held.make _
  | scopeAdd scope fin =>
    cases found : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin found] at step; cases step
    | some entry =>
      cases closing : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin found closing] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact held
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin found closing] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact held.setEntry _ (held entry (List.mem_of_find?_eq_some found))
  | scopeRemove scope key =>
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact held.remove scope key
  | scopeFork parent strategy =>
    change strategy = .sequential at allocation
    subst strategy
    cases found : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent .sequential found] at step; cases step
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent .sequential found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact held.fork _ _ _
  | memoGet layer memoMap =>
    obtain ⟨_, _, scopes, _, _⟩ := syncOpStep_memoGet_families s next layer memoMap value step
    rw [scopes]
    exact held
  | memoBuild layer memoMap =>
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact held.make _
  | memoComplete layer memoMap exit =>
    cases found : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact held
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact held
  | memoRelease layer memoMap =>
    cases found : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact held
    | some entry =>
      by_cases last : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap found last] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact held
      · rw [syncOpStep_memoRelease_dec s layer memoMap found last] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact held
  | _ =>
    simp only [syncOpStep, Option.map_eq_some_iff] at step
    obtain ⟨_, _, result⟩ := step
    rw [← (Prod.mk.inj result).1]
    exact held

/-- Actual scope linking keeps every existing physical strategy. -/
theorem link {s next : Stores} {mode : Supervision.ScopeMode} {scope : Nat} {fiber : FiberId} {key : Nat}
    (held : Held s.scopes) (step : stores.scopeLinkFiber mode scope fiber s = some (next, key)) :
    Held next.scopes := by
  dsimp only [stores] at step
  cases found : s.scopes.entryAt scope with
  | none => rw [found] at step; cases step
  | some entry =>
    rw [found] at step
    dsimp only at step
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact held.add _ _ _

/-- State-first close returns the existing sequential strategy and retains it in the store. -/
theorem snapshot {s next : Stores} {scope : Nat} {exit : ExitV}
    {strategy : FinalizerStrategy} {order : List FinName}
    (held : Held s.scopes) (step : scopeCloseSnapshot scope exit s = some (next, strategy, order)) :
    Held next.scopes ∧ strategy = .sequential := by
  unfold scopeCloseSnapshot at step
  cases found : s.scopes.entryAt scope with
  | none => simp only [found] at step; cases step
  | some entry =>
    simp only [found, Option.pure_def] at step
    obtain ⟨rfl, rfl, rfl⟩ := step
    exact ⟨held.close scope exit, held entry (List.mem_of_find?_eq_some found)⟩

/-- The unsafe native close retains the physical scope strategy. -/
theorem close_unsafe {s next : Stores} {scope : Nat} {exit : ExitV} {masked : Bool}
    {program : Option Program} (held : Held s.scopes)
    (step : storesCloseScopeUnsafe scope exit masked s = some (next, program)) : Held next.scopes := by
  unfold storesCloseScopeUnsafe at step
  cases found : scopeCloseSnapshot scope exit s with
  | none => simp only [found] at step; cases step
  | some result =>
    obtain ⟨state, strategy, order⟩ := result
    simp only [found, Option.pure_def] at step
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact (snapshot held found).1

/-- The voiding native close retains the physical scope strategy. -/
theorem close {s next : Stores} {scope : Nat} {exit : ExitV} {masked : Bool}
    {program : Program} (held : Held s.scopes)
    (step : storesCloseScope scope exit masked s = some (next, program)) : Held next.scopes := by
  obtain ⟨_, unsafeClose⟩ := storesCloseScope_unsafe step
  exact close_unsafe held unsafeClose

end Effect4.Machine.ScopeSequential
