import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Machine.ScopeIdentity

/-!
Concept: scope-lifetime-finalization, R11, at most one release per registration.
Question: scope-store accounting consumed by `ReleaseCustody.Execution.command_custody`.
Reach: every native store operation, with distinct scope identities and fresh registration keys.
The returned value remains the actual operation result, including the closed-scope response.
These local transfers establish no source-use bound, execution progress or host behavior.
The measure reads the existing scope store and adds no execution representation.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.ScopeTransfer
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

/-- Total foreign cleanup credit held by the existing scope entries. -/
def storedCredits (q : List Nat) (s : ScopeStore) : Nat :=
  (s.entries.map fun e => scopeCredits q e.scope).sum

/-- Replacing one distinct entry changes exactly that entry's credit. -/
theorem replace (q : List Nat) (s : ScopeStore) (entry : ScopeEntry) (next : ScopeV)
    (unique : (s.entries.map ScopeEntry.key).Nodup) (member : entry ∈ s.entries) :
    storedCredits q (s.setEntry {entry with scope := next}) + scopeCredits q entry.scope =
      storedCredits q s + scopeCredits q next :=
  ControlWeights.replace_sum ScopeEntry.key (fun e => scopeCredits q e.scope)
    entry {entry with scope := next} rfl s.entries unique member

/-- Allocating an empty scope introduces no foreign cleanup credit. -/
theorem make (q : List Nat) (s : ScopeStore) (key : Nat) (strategy : FinalizerStrategy) :
    storedCredits q (s.make key strategy) = storedCredits q s := by
  simp only [storedCredits, ScopeStore.make, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- A missing closing exit means the scope is open for registration. -/
theorem opened (scope : ScopeV) (h : scope.closingExit? = none) : scope.isClosed = false := by
  cases state : scope.state with
  | empty | openEmpty | openInline _ _ | openMap _ =>
    change scope.state.isClosed = false
    rw [state]
    rfl
  | closed exit => change scope.state.closingExit? = none at h; rw [state] at h; cases h

/-- Removing a registration can only discard foreign cleanup credit. -/
theorem remove (q : List Nat) (s : ScopeStore) (scope key : Nat)
    (unique : (s.entries.map ScopeEntry.key).Nodup) :
    storedCredits q (s.removeFinalizer scope key) ≤ storedCredits q s := by
  unfold ScopeStore.removeFinalizer
  split
  · exact Nat.le_refl _
  · rename_i entry found
    have changed := replace q s entry (entry.scope.removeUnsafe key) unique
      (List.mem_of_find?_eq_some found)
    have smaller : scopeCredits q (entry.scope.removeUnsafe key) ≤ scopeCredits q entry.scope :=
      ((Scope.removeUnsafe_finalizers_sublist entry.scope key).map Prod.snd).countP_le
    omega

/-- Administrative fork finalizers carry no foreign cleanup credit on either side. -/
theorem fork_scope (q : List Nat) (parent : ScopeV) (strategy : FinalizerStrategy)
    (shared child owner : Nat) (fresh : shared ∉ parent.finalizerKeys) :
    scopeCredits q (Scope.fork parent strategy shared (.closeChildScope child)
      (.detachFromParent owner shared)).1 = scopeCredits q parent ∧
    scopeCredits q (Scope.fork parent strategy shared (.closeChildScope child)
      (.detachFromParent owner shared)).2 = 0 := by
  cases closing : parent.closingExit? with
  | some exit =>
    simp only [Scope.fork, closing]
    exact ⟨True.intro, rfl⟩
  | none =>
    have isOpen := opened parent closing
    constructor
    · unfold scopeCredits orderCredits
      rw [Scope.fork_parent_finalizers parent strategy shared _ _ isOpen fresh]
      simp only [List.map_append, List.countP_append, List.map_cons, List.map_nil,
        List.countP_cons, List.countP_nil, foreignAt, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
    · unfold scopeCredits orderCredits
      rw [Scope.fork_child_finalizers parent strategy shared _ _ isOpen]
      rfl

/-- Scope fork adds only administrative finalizers and retains every foreign cleanup credit. -/
theorem fork (q : List Nat) (s : ScopeStore) (parent child shared supply : Nat)
    (strategy : FinalizerStrategy) (unique : (s.entries.map ScopeEntry.key).Nodup)
    (fresh : s.KeysBelow supply) (bound : supply ≤ shared) :
    storedCredits q (s.forkChild parent child shared strategy) = storedCredits q s := by
  unfold ScopeStore.forkChild
  split
  · rfl
  · rename_i entry found
    have member := List.mem_of_find?_eq_some found
    have absent : shared ∉ entry.scope.finalizerKeys := by
      intro present
      have less := fresh entry member shared present
      omega
    have weights := fork_scope q entry.scope strategy shared child parent absent
    have changed := replace q s entry
      (Scope.fork entry.scope strategy shared (.closeChildScope child)
        (.detachFromParent parent shared)).1 unique member
    change storedCredits q
      ⟨(s.setEntry {entry with scope := (Scope.fork entry.scope strategy shared
        (.closeChildScope child) (.detachFromParent parent shared)).1}).entries ++
      [⟨child, (Scope.fork entry.scope strategy shared (.closeChildScope child)
        (.detachFromParent parent shared)).2⟩]⟩ = _
    simp only [storedCredits, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, weights.2, Nat.add_zero]
    rw [weights.1] at changed
    exact Nat.add_right_cancel changed

/-- Registration transfers its one credit into the scope or the immediate closing response.
The same credit never appears in both places. -/
theorem add (q : List Nat) (s next : Stores) (scope : Nat) (fin : FinName) (value : Val)
    (unique : (s.scopes.entries.map ScopeEntry.key).Nodup) (fresh : s.ScopeKeysFresh)
    (step : syncOpStep (.scopeAdd scope fin) s = some (next, value)) :
    storedCredits q next.scopes + afterAddCredits q fin value =
      storedCredits q s.scopes + credit q fin := by
  cases found : s.scopes.entryAt scope with
  | none => rw [syncOpStep_scopeAdd_none s scope fin found] at step; cases step
  | some entry =>
    cases closing : entry.scope.closingExit? with
    | some exit =>
      rw [syncOpStep_scopeAdd_closed s scope fin found closing] at step
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj step)
      rw [after_add_exit_credit]
    | none =>
      rw [syncOpStep_scopeAdd_open s scope fin found closing] at step
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj step)
      rw [after_add_unit_credit, Nat.add_zero]
      have member := List.mem_of_find?_eq_some found
      have changed := replace q s.scopes entry (entry.scope.addUnsafe s.nextName fin) unique member
      have added := add_open q entry.scope s.nextName fin (opened entry.scope closing)
        (fresh.fresh entry member)
      rw [added] at changed
      change storedCredits q (s.scopes.setEntry {entry with scope := entry.scope.addUnsafe s.nextName fin}) = _
      omega

/-- Any native synchronous operation adds at most its explicitly carried finalizer credit.
Consumer: the native evaluator clause of `Execution.command_custody`.
The stronger `add` equation accounts for the response-sensitive continuation separately. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem syncOp (q : List Nat) {s next : Stores} {op : SyncOp} {value : Val}
    (unique : (s.scopes.entries.map ScopeEntry.key).Nodup) (fresh : s.ScopeKeysFresh)
    (step : syncOpStep op s = some (next, value)) :
    storedCredits q next.scopes ≤ storedCredits q s.scopes + opCredits q op := by
  cases op with
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | clockNow | sleepCancel _ _ | memoFork _ =>
    have states := Prod.mk.inj (Option.some.inj step)
    rw [← states.1]
    exact Nat.le_refl _
  | deferredIsDone _ | deferredPoll _ | scopeIsClosed _ =>
    simp only [syncOpStep, Option.map_eq_some_iff] at step
    obtain ⟨_, _, result⟩ := step
    rw [← (Prod.mk.inj result).1]
    exact Nat.le_refl _
  | scopeMake strategy =>
    have states := Prod.mk.inj (Option.some.inj step)
    rw [← states.1]
    exact Nat.le_of_eq (make q s.scopes s.nextName strategy)
  | scopeAdd scope fin =>
    have transferred := add q s next scope fin value unique fresh step
    change storedCredits q next.scopes ≤ storedCredits q s.scopes + credit q fin
    omega
  | scopeRemove scope key =>
    have states := Prod.mk.inj (Option.some.inj step)
    rw [← states.1]
    exact remove q s.scopes scope key unique
  | scopeFork parent strategy =>
    cases found : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy found] at step; cases step
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact Nat.le_of_eq (fork q s.scopes parent s.nextName (s.nextName + 1) s.nextName
        strategy unique fresh (Nat.le_succ _))
  | memoGet layer memoMap =>
    obtain ⟨_, _, scopes, _, _⟩ := syncOpStep_memoGet_families s next layer memoMap value step
    rw [scopes]
    exact Nat.le_refl _
  | memoBuild layer memoMap =>
    have states := Prod.mk.inj (Option.some.inj step)
    rw [← states.1]
    exact Nat.le_of_eq (make q s.scopes s.nextName .sequential)
  | memoComplete layer memoMap exit =>
    cases found : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact Nat.le_refl _
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact Nat.le_refl _
  | memoRelease layer memoMap =>
    cases found : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap found] at step
      rw [← (Prod.mk.inj (Option.some.inj step)).1]
      exact Nat.le_refl _
    | some entry =>
      by_cases last : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap found last] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact Nat.le_refl _
      · rw [syncOpStep_memoRelease_dec s layer memoMap found last] at step
        rw [← (Prod.mk.inj (Option.some.inj step)).1]
        exact Nat.le_refl _
  | _ =>
    simp only [syncOpStep, Option.map_eq_some_iff] at step
    obtain ⟨_, _, result⟩ := step
    rw [← (Prod.mk.inj result).1]
    exact Nat.le_refl _

/-- Adding an administrative finalizer retains the total foreign cleanup credit. -/
theorem add_admin (q : List Nat) (s : ScopeStore) (scope key : Nat) (fin : FinName)
    (unique : (s.entries.map ScopeEntry.key).Nodup) (fresh : s.KeysBelow key)
    (admin : credit q fin = 0) :
    storedCredits q (s.addFinalizer scope key fin).1 = storedCredits q s := by
  unfold ScopeStore.addFinalizer
  split
  · rfl
  · rename_i entry found
    have member := List.mem_of_find?_eq_some found
    cases closing : entry.scope.closingExit? with
    | some exit =>
      simp only [Scope.addExit, closing]
      have changed := replace q s entry entry.scope unique member
      exact Nat.add_right_cancel changed
    | none =>
      simp only [Scope.addExit, closing]
      have added := add_open q entry.scope key fin (opened entry.scope closing)
        (fresh.fresh entry member)
      have changed := replace q s entry (entry.scope.addUnsafe key fin) unique member
      rw [added, admin, Nat.add_zero] at changed
      exact Nat.add_right_cancel changed

/-- Linking a fiber registers an administrative cleanup with no foreign release credit.
Consumer: the actual `link` command clause of `Execution.command_custody`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem link (q : List Nat) (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {s next : Stores} {key : Nat} (unique : (s.scopes.entries.map ScopeEntry.key).Nodup)
    (fresh : s.ScopeKeysFresh)
    (step : stores.scopeLinkFiber mode scope fiber s = some (next, key)) :
    storedCredits q next.scopes = storedCredits q s.scopes := by
  dsimp only [stores] at step
  cases found : s.scopes.entryAt scope with
  | none => rw [found] at step; cases step
  | some entry =>
    rw [found] at step
    dsimp only at step
    rw [← (Prod.mk.inj (Option.some.inj step)).1]
    exact add_admin q s.scopes scope s.nextName _ unique fresh rfl

/-- State-first close transfers all selected credits to the actual returned close program.
Consumer: the scope-close evaluator clause of `Execution.command_custody`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close (q : List Nat) (scope : Nat) (exit : ExitV) (masked : Bool)
    {s next : Stores} {program : Program} (unique : (s.scopes.entries.map ScopeEntry.key).Nodup)
    (step : storesCloseScope scope exit masked s = some (next, program)) :
    storedCredits q next.scopes + currentCredits q (embed program) = storedCredits q s.scopes := by
  cases found : s.scopes.entryAt scope with
  | none => rw [storesCloseScope_unknown scope exit masked s found] at step; cases step
  | some entry =>
    simp only [storesCloseScope, scopeCloseSnapshot, found, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, ScopeStore.closeState, Option.some.injEq,
      Prod.mk.injEq] at step
    obtain ⟨rfl, rfl⟩ := step
    have changed := replace q s.scopes entry (Scope.closeState entry.scope exit) unique
      (List.mem_of_find?_eq_some found)
    have transferred := close_scope q entry.scope exit
    rw [transferred.1, Nat.add_zero] at changed
    have returned := close_program_credits q entry.scope.strategy entry.scope.closeOrder exit
    rw [transferred.2] at returned
    exact (congrArg (fun n => storedCredits q
      (s.scopes.setEntry {entry with scope := Scope.closeState entry.scope exit}) + n) returned).trans changed

end Effect4.Program.ReleaseCustody.ScopeTransfer
