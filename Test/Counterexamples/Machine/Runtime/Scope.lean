import Std

/-!
# Scope runtime counterexamples

This file is a self-contained breaker model. It deliberately does not import
`Effect4.Runtime.Scope`: the witnesses must remain executable while the
production surface is still absent, and they must keep proving the attack after
the repaired declarations land.

Each theorem is finite and proves only the named attack. None of them is a
production law; the frozen laws live in `test/contracts/scope.contract.md`.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` section 6.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Runtime.Scope

/-! ## The shared miniature alphabets

A cause is a flat ordered list of error codes, matching the `Cause` packet's
carrier. A finalizer is a nominal `Nat` name; `runFinalizer` is the externally
supplied interpretation, the shape the production model takes as a parameter.
-/

/-- A miniature flat cause: an ordered list of error codes. -/
abbrev MiniCause := List Nat

/-- A miniature exit. -/
inductive MiniExit
  | success
  | failure (cause : MiniCause)
  deriving DecidableEq, Repr

/-- The reasons an exit contributes to a join. -/
def MiniExit.reasons : MiniExit -> MiniCause
  | success => []
  | failure cause => cause

/-- The pinned `exitAsVoidAll`: concatenate every failed exit's reasons, and
succeed when none remain. -/
def asVoidAll (exits : List MiniExit) : MiniExit :=
  match exits.flatMap MiniExit.reasons with
  | [] => .success
  | reason :: rest => .failure (reason :: rest)

/-- The externally supplied finalizer interpretation. Finalizer `0` succeeds,
`1` and `2` fail with their own error code, and `3` fails with an empty cause. -/
def runFinalizer : Nat -> MiniExit -> MiniExit
  | 0, _ => .success
  | 1, _ => .failure [1]
  | 2, _ => .failure [2]
  | 3, _ => .failure []
  | _, _ => .success

/-- The three inhabited `Open` shapes of rc.112, plus `Empty` and `Closed`. -/
inductive MiniState
  | empty
  | openEmpty
  | openInline (key : Nat) (finalizer : Nat)
  | openMap (entries : List (Nat × Nat))
  | closed (exit : MiniExit)
  deriving DecidableEq, Repr

/-- The materialised registration order of a state. -/
def MiniState.entries : MiniState -> List (Nat × Nat)
  | empty => []
  | openEmpty => []
  | openInline key finalizer => [(key, finalizer)]
  | openMap table => table
  | closed _ => []

def MiniState.isClosed : MiniState -> Bool
  | closed _ => true
  | _ => false

/-- `Map.prototype.set`: an existing key keeps its slot, a new key is appended. -/
def tableInsert (table : List (Nat × Nat)) (key finalizer : Nat) : List (Nat × Nat) :=
  if table.any (fun entry => decide (entry.fst = key)) then
    table.map (fun entry => if entry.fst = key then (key, finalizer) else entry)
  else
    table ++ [(key, finalizer)]

/-- `Map.prototype.delete`. -/
def tableRemove (table : List (Nat × Nat)) (key : Nat) : List (Nat × Nat) :=
  table.filter (fun entry => decide (entry.fst ≠ key))

/-- The pinned `scopeAddFinalizerUnsafe`. -/
def addUnsafe : MiniState -> Nat -> Nat -> MiniState
  | .empty, key, finalizer => .openInline key finalizer
  | .openEmpty, key, finalizer => .openInline key finalizer
  | .openInline existingKey existing, key, finalizer =>
    .openMap (tableInsert [(existingKey, existing)] key finalizer)
  | .openMap table, key, finalizer => .openMap (tableInsert table key finalizer)
  | .closed exit, _, _ => .closed exit

/-- The pinned `scopeRemoveFinalizerUnsafe`. -/
def removeUnsafe : MiniState -> Nat -> MiniState
  | .openInline existingKey existing, key =>
    if existingKey = key then .openEmpty else .openInline existingKey existing
  | .openMap table, key => .openMap (tableRemove table key)
  | state, _ => state

/-- The pinned `scopeAddFinalizerExit`: register when open, run now when closed. -/
def addExit (state : MiniState) (key finalizer : Nat) : MiniState × MiniExit :=
  match state with
  | .closed exit => (.closed exit, runFinalizer finalizer exit)
  | _ => (addUnsafe state key finalizer, MiniExit.success)

def stateOfEntries (entries : List (Nat × Nat)) : MiniState :=
  entries.foldl (fun state entry => addUnsafe state entry.fst entry.snd) MiniState.empty

def oneEntry : MiniState := stateOfEntries [(10, 0)]
def threeEntries : MiniState := stateOfEntries [(10, 0), (20, 1), (30, 2)]

/-! ## E4-RUN-CE-001 — close must write the Closed state before any finalizer -/

/-- The scope a finalizer observes while the pinned close runs: already Closed. -/
def duringClosePinned (state : MiniState) (exit : MiniExit) : MiniState :=
  if state.isClosed then state else .closed exit

/-- The rejected close runs finalizers first, so a finalizer still sees Open. -/
def duringCloseRunFirst (state : MiniState) (_exit : MiniExit) : MiniState := state

/-- E4-RUN-CE-001: a finalizer that registers another finalizer during close
sees a Closed scope under the pinned order, so its registration runs
immediately with the closing exit. Under the rejected order it is recorded in a
scope that is about to be discarded, and therefore never runs. -/
theorem close_must_write_state_first :
    addExit (duringClosePinned oneEntry (MiniExit.failure [7])) 40 1 =
        (MiniState.closed (MiniExit.failure [7]), MiniExit.failure [1]) /\
      (addExit (duringCloseRunFirst oneEntry (MiniExit.failure [7])) 40 1).snd =
        MiniExit.success /\
      (addExit (duringCloseRunFirst oneEntry (MiniExit.failure [7])) 40 1).fst.entries =
        [(10, 0), (40, 1)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-001: the state written by close cannot depend on any finalizer
result, because it is written before a finalizer runs. -/
theorem close_state_is_independent_of_finalizers :
    duringClosePinned threeEntries (MiniExit.failure [7]) =
        duringClosePinned threeEntries (MiniExit.failure [7]) /\
      (duringClosePinned threeEntries (MiniExit.failure [7])).entries = [] := by
  refine ⟨rfl, by decide⟩

/-! ## E4-RUN-CE-002 — finalizers run in reverse registration order -/

/-- The pinned close order: materialise in insertion order, iterate backwards. -/
def closeOrderPinned (state : MiniState) : List Nat :=
  (state.entries.map Prod.snd).reverse

/-- The rejected order: run in registration order. -/
def closeOrderFifo (state : MiniState) : List Nat :=
  state.entries.map Prod.snd

/-- E4-RUN-CE-002: the last registered finalizer runs first. -/
theorem close_order_is_lifo :
    closeOrderPinned threeEntries = [2, 1, 0] /\
      closeOrderFifo threeEntries = [0, 1, 2] /\
      closeOrderPinned threeEntries ≠ closeOrderFifo threeEntries := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-002: the order is observable in the merged closing cause, not
only in the sequence of calls. -/
theorem close_order_changes_the_cause :
    asVoidAll ((closeOrderPinned threeEntries).map (fun f => runFinalizer f .success)) =
        MiniExit.failure [2, 1] /\
      asVoidAll ((closeOrderFifo threeEntries).map (fun f => runFinalizer f .success)) =
        MiniExit.failure [1, 2] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-003 — close is idempotent -/

/-- The pinned close: an already-Closed scope is returned untouched. -/
def closePinned (state : MiniState) (exit : MiniExit) : MiniState × List MiniExit :=
  if state.isClosed then (state, [])
  else (.closed exit, (closeOrderPinned state).map (fun f => runFinalizer f exit))

/-- The rejected close: no `Closed` guard, so a second close overwrites the
stored exit and re-runs whatever it can still see. -/
def closeUnguarded (state : MiniState) (exit : MiniExit) : MiniState × List MiniExit :=
  (.closed exit, (closeOrderPinned state).map (fun f => runFinalizer f exit))

/-- E4-RUN-CE-003: a second close runs no finalizer and keeps the first exit. -/
theorem close_is_idempotent :
    closePinned (closePinned threeEntries MiniExit.success).fst (MiniExit.failure [9]) =
        (MiniState.closed MiniExit.success, []) /\
      closeUnguarded (closeUnguarded threeEntries MiniExit.success).fst
          (MiniExit.failure [9]) =
        (MiniState.closed (MiniExit.failure [9]), []) := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-003: without the guard the finalizers of an inline scope run
twice, because a `Closed` state that still exposed its registrations would be
closed again. -/
theorem close_guard_prevents_double_run :
    (closePinned oneEntry MiniExit.success).snd = [MiniExit.success] /\
      (closePinned (closePinned oneEntry MiniExit.success).fst MiniExit.success).snd = [] /\
      (closeUnguarded oneEntry MiniExit.success).snd = [MiniExit.success] := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## E4-RUN-CE-004 — adding to a Closed scope runs the finalizer now -/

/-- The rejected add: a Closed scope records the finalizer like any other. -/
def addExitRegistering (state : MiniState) (key finalizer : Nat) : MiniState × MiniExit :=
  (addUnsafe state key finalizer, MiniExit.success)

/-- The rejected add: a Closed scope silently drops the finalizer. -/
def addExitDropping (state : MiniState) (key finalizer : Nat) : MiniState × MiniExit :=
  match state with
  | .closed exit => (.closed exit, MiniExit.success)
  | _ => (addUnsafe state key finalizer, MiniExit.success)

/-- E4-RUN-CE-004: the pinned add returns the finalizer's own exit, run against
the stored closing exit; both rejected variants report success and never run
the finalizer. -/
theorem add_after_closed_runs_now :
    addExit (MiniState.closed (MiniExit.failure [7])) 40 1 =
        (MiniState.closed (MiniExit.failure [7]), MiniExit.failure [1]) /\
      addExitRegistering (MiniState.closed (MiniExit.failure [7])) 40 1 =
        (MiniState.closed (MiniExit.failure [7]), MiniExit.success) /\
      addExitDropping (MiniState.closed (MiniExit.failure [7])) 40 1 =
        (MiniState.closed (MiniExit.failure [7]), MiniExit.success) := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-004: `scopeAddFinalizerUnsafe` itself has no `Closed` arm, so the
registration list of a Closed scope never grows. -/
theorem add_after_closed_registers_nothing :
    (addExit (MiniState.closed (MiniExit.failure [7])) 40 1).fst.entries = [] /\
      addUnsafe (MiniState.closed (MiniExit.failure [7])) 40 1 =
        MiniState.closed (MiniExit.failure [7]) := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-005 — removal, and the cleared inline slot -/

/-- The rejected removal: it normalises every scope into a map first, so an
Empty or Closed scope becomes Open. -/
def removeNormalising (state : MiniState) (key : Nat) : MiniState :=
  .openMap (tableRemove state.entries key)

/-- E4-RUN-CE-005: removal leaves a non-Open scope untouched. A normalising
removal turns `Empty` into an Open scope, which would then accept
registrations, and turns a `Closed` scope back into an Open one, losing the
stored exit. -/
theorem remove_leaves_non_open_untouched :
    removeUnsafe MiniState.empty 10 = MiniState.empty /\
      removeUnsafe (MiniState.closed (MiniExit.failure [7])) 10 =
        MiniState.closed (MiniExit.failure [7]) /\
      removeNormalising MiniState.empty 10 = MiniState.openMap [] /\
      removeNormalising (MiniState.closed (MiniExit.failure [7])) 10 =
        MiniState.openMap [] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- E4-RUN-CE-005: clearing the inline slot yields neither `Empty` nor the
empty map. The difference is observable at the very next add: a cleared inline
slot takes it inline again, while an emptied map takes it into the map. -/
theorem cleared_inline_slot_is_its_own_state :
    removeUnsafe oneEntry 10 = MiniState.openEmpty /\
      MiniState.openEmpty ≠ MiniState.empty /\
      MiniState.openEmpty ≠ MiniState.openMap [] /\
      addUnsafe (removeUnsafe oneEntry 10) 50 0 = MiniState.openInline 50 0 /\
      addUnsafe (MiniState.openMap []) 50 0 = MiniState.openMap [(50, 0)] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- E4-RUN-CE-005: an inline slot under a different key is untouched, because
there is no map to delete from. -/
theorem remove_inline_miss_is_a_no_op :
    removeUnsafe oneEntry 99 = oneEntry := by
  decide

/-! ## E4-RUN-CE-006 — a child of a Closed parent is born Closed -/

/-- The pinned fork, parent side and child side. -/
def forkPinned (parent : MiniState) (key closeChild detachFromParent : Nat) :
    MiniState × MiniState :=
  match parent with
  | .closed exit => (.closed exit, .closed exit)
  | _ => (addUnsafe parent key closeChild,
      addUnsafe MiniState.empty key detachFromParent)

/-- The rejected fork: the child is always a brand new Empty scope. -/
def forkFreshChild (parent : MiniState) (key closeChild detachFromParent : Nat) :
    MiniState × MiniState :=
  (addUnsafe parent key closeChild, addUnsafe MiniState.empty key detachFromParent)

/-- E4-RUN-CE-006: a child forked from a Closed parent is born Closed with the
parent's exit. A fresh Empty child would accept registrations that no close
would ever run, and the parent's Closed scope would silently grow a finalizer. -/
theorem fork_of_closed_parent_is_born_closed :
    forkPinned (MiniState.closed (MiniExit.failure [7])) 99 1 2 =
        (MiniState.closed (MiniExit.failure [7]),
          MiniState.closed (MiniExit.failure [7])) /\
      (forkFreshChild (MiniState.closed (MiniExit.failure [7])) 99 1 2).snd =
        MiniState.openInline 99 2 /\
      (addExit (forkFreshChild (MiniState.closed (MiniExit.failure [7])) 99 1 2).snd 50
        1).fst.entries = [(99, 2), (50, 1)] := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## E4-RUN-CE-007 — the fork link is one shared key -/

/-- The rejected fork: each side mints its own key. -/
def forkTwoKeys (parent : MiniState) (parentKey childKey closeChild detachFromParent : Nat) :
    MiniState × MiniState :=
  (addUnsafe parent parentKey closeChild,
    addUnsafe MiniState.empty childKey detachFromParent)

/-- E4-RUN-CE-007: the child's own finalizer detaches the parent by removing
the shared key. With two keys the removal misses, so the parent keeps a
finalizer that closes an already-closed child — the leak the shared key
prevents. -/
theorem fork_link_needs_one_shared_key :
    removeUnsafe (forkPinned threeEntries 99 1 2).fst 99 =
        MiniState.openMap threeEntries.entries /\
      removeUnsafe (forkTwoKeys threeEntries 99 88 1 2).fst 88 ≠
        MiniState.openMap threeEntries.entries /\
      (removeUnsafe (forkTwoKeys threeEntries 99 88 1 2).fst 88).entries =
        [(10, 0), (20, 1), (30, 2), (99, 1)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-007: both sides really do carry the same key. -/
theorem fork_registers_the_same_key_on_both_sides :
    (forkPinned threeEntries 99 1 2).fst.entries.map Prod.fst = [10, 20, 30, 99] /\
      (forkPinned threeEntries 99 1 2).snd.entries.map Prod.fst = [99] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-008 — a failing finalizer does not abort the close -/

/-- The pinned sequential close: each finalizer is awaited through `exit()`,
so its failure is captured and the loop continues. -/
def sequentialExits (order : List Nat) (exit : MiniExit) : List MiniExit :=
  order.map (fun finalizer => runFinalizer finalizer exit)

/-- The rejected close: the first failing finalizer stops the loop. -/
def sequentialExitsShortCircuit : List Nat -> MiniExit -> List MiniExit
  | [], _ => []
  | finalizer :: rest, exit =>
    match runFinalizer finalizer exit with
    | .success => MiniExit.success :: sequentialExitsShortCircuit rest exit
    | .failure cause => [MiniExit.failure cause]

/-- E4-RUN-CE-008: with a failing finalizer in the middle of the close order,
the short-circuiting variant never runs the finalizers registered before it. -/
theorem sequential_close_captures_failures :
    sequentialExits [2, 1, 0] MiniExit.success =
        [MiniExit.failure [2], MiniExit.failure [1], MiniExit.success] /\
      sequentialExitsShortCircuit [2, 1, 0] MiniExit.success = [MiniExit.failure [2]] /\
      (sequentialExits [2, 1, 0] MiniExit.success).length = 3 /\
      (sequentialExitsShortCircuit [2, 1, 0] MiniExit.success).length = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- E4-RUN-CE-008: the dropped finalizer's failure is dropped from the closing
cause as well, so the difference is observable in the exit, not only in the
call sequence. -/
theorem short_circuit_loses_a_reason :
    asVoidAll (sequentialExits [2, 1, 0] MiniExit.success) = MiniExit.failure [2, 1] /\
      asVoidAll (sequentialExitsShortCircuit [2, 1, 0] MiniExit.success) =
        MiniExit.failure [2] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-009 — the merge, and the single-finalizer short circuit -/

/-- The pinned `scopeCloseUnsafe` result: nothing for no finalizer, the single
finalizer's own exit for one, and the `exitAsVoidAll` merge for many. -/
def closeResultPinned (order : List Nat) (exit : MiniExit) : MiniExit :=
  match sequentialExits order exit with
  | [] => .success
  | [only] => only
  | first :: second :: rest => asVoidAll (first :: second :: rest)

/-- The rejected result: always merge, including the one-finalizer case. -/
def closeResultAlwaysMerge (order : List Nat) (exit : MiniExit) : MiniExit :=
  asVoidAll (sequentialExits order exit)

/-- E4-RUN-CE-009: with exactly one finalizer rc.112 returns that finalizer's
effect directly, without `exitAsVoidAll`. A finalizer that fails with an empty
cause therefore fails the close, where the merge would have succeeded. -/
theorem single_finalizer_is_not_merged :
    closeResultPinned [3] MiniExit.success = MiniExit.failure [] /\
      closeResultAlwaysMerge [3] MiniExit.success = MiniExit.success /\
      closeResultPinned [3] MiniExit.success ≠
        closeResultAlwaysMerge [3] MiniExit.success := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-009: with two or more finalizers every failure reason is
concatenated into one flat cause, in close order, and the two agree. -/
theorem many_finalizers_are_merged_flat :
    closeResultPinned [2, 1, 0] MiniExit.success = MiniExit.failure [2, 1] /\
      closeResultAlwaysMerge [2, 1, 0] MiniExit.success = MiniExit.failure [2, 1] := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-009: the merge is `exitAsVoidAll`, not `causeCombine`: it
concatenates and keeps duplicates. -/
theorem merge_is_concatenation_not_union :
    closeResultPinned [1, 1] MiniExit.success = MiniExit.failure [1, 1] := by
  decide

/-! ## Kernel dependency receipts

Every attack witness above is finite and decidable. The accepted ceiling is
no dependency, `propext`, or `propext` with `Quot.sound`.
-/

#print axioms Test.Counterexamples.Runtime.Scope.close_must_write_state_first
#print axioms Test.Counterexamples.Runtime.Scope.close_state_is_independent_of_finalizers
#print axioms Test.Counterexamples.Runtime.Scope.close_order_is_lifo
#print axioms Test.Counterexamples.Runtime.Scope.close_order_changes_the_cause
#print axioms Test.Counterexamples.Runtime.Scope.close_is_idempotent
#print axioms Test.Counterexamples.Runtime.Scope.close_guard_prevents_double_run
#print axioms Test.Counterexamples.Runtime.Scope.add_after_closed_runs_now
#print axioms Test.Counterexamples.Runtime.Scope.add_after_closed_registers_nothing
#print axioms Test.Counterexamples.Runtime.Scope.remove_leaves_non_open_untouched
#print axioms Test.Counterexamples.Runtime.Scope.cleared_inline_slot_is_its_own_state
#print axioms Test.Counterexamples.Runtime.Scope.remove_inline_miss_is_a_no_op
#print axioms Test.Counterexamples.Runtime.Scope.fork_of_closed_parent_is_born_closed
#print axioms Test.Counterexamples.Runtime.Scope.fork_link_needs_one_shared_key
#print axioms Test.Counterexamples.Runtime.Scope.fork_registers_the_same_key_on_both_sides
#print axioms Test.Counterexamples.Runtime.Scope.sequential_close_captures_failures
#print axioms Test.Counterexamples.Runtime.Scope.short_circuit_loses_a_reason
#print axioms Test.Counterexamples.Runtime.Scope.single_finalizer_is_not_merged
#print axioms Test.Counterexamples.Runtime.Scope.many_finalizers_are_merged_flat
#print axioms Test.Counterexamples.Runtime.Scope.merge_is_concatenation_not_union

end Test.Counterexamples.Runtime.Scope
