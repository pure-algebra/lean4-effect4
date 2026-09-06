import Effect4.Machine.StoresLaws

/-!
# Stores laws contract — growth, validity and well-formedness of the stores, frozen

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §3 (lane 2). Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 10–17. The module under contract is
`src/Effect4/Machine/StoresLaws.lean`.

Every obligation below is ascribed at its exact proposition and supplied by name with `@`, so
a declaration that keeps the frozen name but weakens the statement fails here
(`Test/Program/ProvisionContract.lean` is the model). The executable receipts are `#guard`s
over first-order values: `syncOpStep` on `Stores.empty` for `refGet ⟨0⟩` (none) and after
`refMake` (some), `validIn` on the answers of a make-then-read sequence on each store, and
the register rows as pairs of guards. Every helper below is a store or an answer, never a
rendering; `Stores.WF` is decided through the instance the module supplies.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-STORES-CE-001` — `syncOpStep` is total. Refuted: `syncOpStep (refGet ⟨0⟩) Stores.empty
  = none`; `syncOpStep_isSome_of_valid` carries `SyncOp.validIn`, which refuses that key.
* `E4-STORES-CE-002` — a valid request's answer is valid without a heap invariant. Refuted:
  the heap `[Val.cell ⟨9⟩]` answers the dangling `cell ⟨9⟩` to the valid `refGet ⟨0⟩`;
  `syncOpStep_answer_valid` carries `Stores.WF`, which that heap fails.
* `E4-STORES-CE-003` — `Stores.WF` covers the program a completed Deferred stores. Refuted:
  completing a fresh Deferred with `ofRefGet ⟨9⟩` on an empty heap is a valid, stepping
  operation whose result is `WF` while `cell ⟨9⟩` is not valid in it; the stored program is
  a `Prim` that `Val.validIn` does not traverse (`STORES-FB-COMPLETION`, plan §7). `WF` is
  not widened in this slice.
-/

set_option autoImplicit false

namespace Test.Runtime.StoresLawsContract

open Effect4
open Effect4.Machine

/-! ## The frozen statements -/

section Statements

#check (@Effect4.Machine.Stores.le : Stores → Stores → Prop)
#check (@Effect4.Machine.Stores.le_refl : ∀ (s : Stores), s.le s)
#check (@Effect4.Machine.Stores.le_trans :
  ∀ {s s' s'' : Stores}, s.le s' → s'.le s'' → s.le s'')

#check (@Effect4.Machine.Val.validIn : Stores → Val → Bool)
#check (@Effect4.Machine.SyncOp.validIn : Stores → SyncOp → Bool)
#check (@Effect4.Machine.Stores.WF : Stores → Prop)
#check (@Effect4.Machine.Stores.empty_wf : Stores.empty.WF)
#check (@Effect4.Machine.SyncOp.isRead : SyncOp → Bool)

#check (@Effect4.Machine.Val.validIn_mono :
  ∀ {s s' : Stores}, s.le s' → ∀ (v : Val), v.validIn s = true → v.validIn s' = true)
#check (@Effect4.Machine.SyncOp.validIn_mono :
  ∀ {s s' : Stores}, s.le s' → ∀ (o : SyncOp), o.validIn s = true → o.validIn s' = true)

#check (@Effect4.Machine.refStep_length :
  ∀ (o : SyncOp) (heap : RefHeap) (v : Val) (heap' : RefHeap),
    refStep o heap = some (v, heap') → heap.length ≤ heap'.length)

#check (@Effect4.Machine.syncOpStep_le :
  ∀ (o : SyncOp) (s s' : Stores) (v : Val), syncOpStep o s = some (s', v) → s.le s')

#check (@Effect4.Machine.syncOpStep_isSome_of_valid :
  ∀ (o : SyncOp) (s : Stores), o.validIn s = true → (syncOpStep o s).isSome = true)

#check (@Effect4.Machine.syncOpStep_wf :
  ∀ (o : SyncOp) (s s' : Stores) (v : Val),
    s.WF → o.validIn s = true → syncOpStep o s = some (s', v) → s'.WF)

#check (@Effect4.Machine.syncOpStep_answer_valid :
  ∀ (o : SyncOp) (s s' : Stores) (v : Val),
    s.WF → o.validIn s = true → syncOpStep o s = some (s', v) → v.validIn s' = true)

#check (@Effect4.Machine.syncOpStep_read_unchanged :
  ∀ (o : SyncOp) (s s' : Stores) (v : Val),
    o.isRead = true → syncOpStep o s = some (s', v) → s' = s)

end Statements

/-! ## Harness: stores reached by one step, and the answers -/

/-- The store after one step, or the store it started from when the step refuses. -/
def after (o : SyncOp) (s : Stores) : Stores := ((syncOpStep o s).map Prod.fst).getD s

/-- The answer of one step. -/
def answer (o : SyncOp) (s : Stores) : Option Val := (syncOpStep o s).map Prod.snd

/-- `Ref.make(5)` on the empty store. -/
def s1 : Stores := after (SyncOp.refMake (Val.nat 5)) Stores.empty
/-- `Deferred.make()` on the empty store. -/
def s2 : Stores := after SyncOp.deferredMake Stores.empty
/-- `Deferred.succeed(d, 1)` after `Deferred.make()`. -/
def s2done : Stores :=
  after (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
/-- `Scope.make()` on the empty store. -/
def s3 : Stores := after (SyncOp.scopeMake .sequential) Stores.empty
/-- A heap holding a handle no allocation minted. -/
def dangling : Stores := { Stores.empty with refs := [Val.cell ⟨9⟩] }

/-! ## The register rows -/

section Rows

-- E4-STORES-CE-001: `syncOpStep` is not total; validity is the repair
#guard syncOpStep (SyncOp.refGet ⟨0⟩) Stores.empty = none
#guard SyncOp.validIn Stores.empty (SyncOp.refGet ⟨0⟩) = false
#guard (syncOpStep (SyncOp.refGet ⟨0⟩) s1).isSome
#guard SyncOp.validIn s1 (SyncOp.refGet ⟨0⟩) = true

-- E4-STORES-CE-002: a valid request's answer is not valid without the heap invariant
#guard SyncOp.validIn dangling (SyncOp.refGet ⟨0⟩) = true
#guard answer (SyncOp.refGet ⟨0⟩) dangling = some (Val.cell ⟨9⟩)
#guard Val.validIn dangling (Val.cell ⟨9⟩) = false
#guard ¬ Stores.WF dangling
#guard Stores.WF s1
#guard (answer (SyncOp.refGet ⟨0⟩) s1).map (Val.validIn s1) = some true

-- E4-STORES-CE-003: `WF` says nothing about a stored completion (STORES-FB-COMPLETION)
#guard SyncOp.validIn s2 (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨9⟩)) = true
#guard (syncOpStep (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨9⟩)) s2).isSome
#guard Stores.WF (after (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨9⟩)) s2)
#guard Val.validIn (after (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨9⟩)) s2)
  (Val.cell ⟨9⟩) = false

end Rows

/-! ## Make-then-read on the heap (`Stores.lean:484-525`) -/

section Heap

#guard answer (SyncOp.refMake (Val.nat 5)) Stores.empty = some (Val.cell ⟨0⟩)
#guard Val.validIn s1 (Val.cell ⟨0⟩)
#guard Val.validIn Stores.empty (Val.cell ⟨0⟩) = false
#guard answer (SyncOp.refGet ⟨0⟩) s1 = some (Val.nat 5)
#guard after (SyncOp.refGet ⟨0⟩) s1 = s1
#guard answer (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1 = some (Val.cell ⟨0⟩)
#guard answer (SyncOp.refGet ⟨0⟩) (after (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1) = some (Val.nat 7)
#guard (after (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1).refs.length = 1
#guard answer (SyncOp.refUpdateSomeAndGet ⟨0⟩ .zeroWhenPositive) s1 = some (Val.nat 0)
#guard Stores.WF (after (SyncOp.refUpdateSomeAndGet ⟨0⟩ .zeroWhenPositive) s1)
-- a handle stored in a cell: valid when it exists, and the argument is part of validity
#guard SyncOp.validIn s1 (SyncOp.refMake (Val.cell ⟨0⟩)) = true
#guard Stores.WF (after (SyncOp.refMake (Val.cell ⟨0⟩)) s1)
#guard SyncOp.validIn Stores.empty (SyncOp.refMake (Val.cell ⟨3⟩)) = false
#guard ¬ Stores.WF (after (SyncOp.refMake (Val.cell ⟨3⟩)) Stores.empty)

end Heap

/-! ## Make-then-read on the Deferred store (`Stores.lean:700-751`, `:1210-1226`) -/

section Deferred

#guard answer SyncOp.deferredMake Stores.empty = some (Val.promise ⟨0⟩)
#guard Val.validIn s2 (Val.promise ⟨0⟩)
#guard Val.validIn Stores.empty (Val.promise ⟨0⟩) = false
#guard syncOpStep (SyncOp.deferredIsDone ⟨0⟩) Stores.empty = none
#guard answer (SyncOp.deferredIsDone ⟨0⟩) s2 = some (Val.bool false)
#guard after (SyncOp.deferredIsDone ⟨0⟩) s2 = s2
#guard answer (SyncOp.deferredPoll ⟨0⟩) s2 = some (Val.bool false)
#guard after (SyncOp.deferredPoll ⟨0⟩) s2 = s2
#guard answer (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
  = some (Val.bool true)
#guard answer (SyncOp.deferredIsDone ⟨0⟩) s2done = some (Val.bool true)
#guard s2done.deferreds.cells.length = 1
#guard answer (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 2)))) s2done
  = some (Val.bool false)

end Deferred

/-! ## Make-then-read on the Scope store (`Stores.lean:902-928`, `:1227-1236`) -/

section Scope

#guard answer (SyncOp.scopeMake .sequential) Stores.empty = some (Val.scopeHandle 0)
#guard Val.validIn s3 (Val.scopeHandle 0)
#guard Val.validIn Stores.empty (Val.scopeHandle 0) = false
#guard s3.nextName = 1
#guard syncOpStep (SyncOp.scopeIsClosed 0) Stores.empty = none
#guard answer (SyncOp.scopeIsClosed 0) s3 = some (Val.bool false)
#guard after (SyncOp.scopeIsClosed 0) s3 = s3
#guard SyncOp.validIn s3 (SyncOp.scopeAdd 0 0 (FinName.release 1 false)) = true
#guard answer (SyncOp.scopeAdd 0 0 (FinName.release 1 false)) s3 = some Val.unit
#guard Val.validIn (after (SyncOp.scopeAdd 0 0 (FinName.release 1 false)) s3) (Val.scopeHandle 0)
#guard answer (SyncOp.scopeMake .parallel) s3 = some (Val.scopeHandle 1)

end Scope

/-! ## Compound values, and the reads -/

section Values

#guard Val.validIn s1 (Val.exitOk (Val.cell ⟨0⟩))
#guard Val.validIn s1 (Val.exitCons (Val.cell ⟨0⟩) (Val.exitCons (Val.nat 1) Val.exitNil))
#guard Val.validIn s1 (Val.exitCons (Val.cell ⟨1⟩) Val.exitNil) = false
#guard Val.validIn Stores.empty (Val.fiber ⟨3⟩)
#guard Val.validIn Stores.empty (Val.exitErr (Cause.fail Err.boom))
#guard SyncOp.isRead (SyncOp.refGet ⟨0⟩)
#guard SyncOp.isRead (SyncOp.deferredIsDone ⟨0⟩)
#guard SyncOp.isRead (SyncOp.deferredPoll ⟨0⟩)
#guard SyncOp.isRead (SyncOp.scopeIsClosed 0)
#guard SyncOp.isRead (SyncOp.refSet ⟨0⟩ Val.unit) = false
#guard SyncOp.isRead SyncOp.deferredMake = false

end Values

end Test.Runtime.StoresLawsContract
