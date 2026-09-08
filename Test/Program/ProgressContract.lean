import Effect4.Laws.Program.Progress

/-!
# Progress contract — a typed, valid request steps to a typed, valid answer, frozen

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §6, node `PROGRESS/answer`.
Packet: `Test/contracts/program-denotation.contract.md`. The module under contract is
`src/Effect4/Laws/Program/Progress.lean`, the first join of lanes 1 and 2.

Every obligation below is ascribed at its exact proposition and supplied by name with `@`, so
a declaration that keeps the frozen name but weakens the statement fails here
(`Test/Program/ProvisionContract.lean` is the model). The executable receipts are `#guard`s
over first-order values: the theorem's hypotheses and conclusions instantiated on the store
operations the compile contract's programs perform (`Test/Program/CompileContract.lean`:
`pRefSet`, `pRefUpdate`, `pRefModify`), one Deferred and one Scope sequence for the store
rows, the pure functions on numbers, and the two register rows as groups of guards. Every
helper is a store or an answer, never a rendering; `Stores.HeapNat` and `Stores.WF` are
decided through the instances the modules supply, and `Val.hasTy` is well-founded, so its
guards are evaluations, never `decide`.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-PROGRESS-CE-001` — a well-formed store answers typed values, so `answer_typed` needs
  no more than `Stores.WF`. Refuted: the heap `[Val.bool true]` is `WF`, `refGet ⟨0⟩` is
  valid in it, the request `Val.cell ⟨0⟩` has the row's request type, and the answer
  `Val.bool true` does not have the row's answer type `.nat`; `answer_typed` carries
  `Stores.HeapNat`, which that heap fails.
* `E4-PROGRESS-CE-002` — `Stores.HeapNat` survives every valid step, so its preservation can
  be stated on `SyncOp.validIn`. Refuted: `refMake (Val.bool true)` is valid on the empty
  store, steps, and leaves the heap `[Val.bool true]`; `step_heapNat` is stated on a typed
  request decoded through `syncOpOf`, and `Val.bool true` does not have `refMake`'s request
  type.
-/

set_option autoImplicit false

namespace Test.Program.ProgressContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## The frozen statements -/

section Statements

#check (@Effect4.Program.Stores.HeapNat : Stores → Prop)
#check (@Effect4.Program.Stores.empty_heapNat : Stores.HeapNat Stores.empty)

#check (@Effect4.Program.FnName.total_hasTy_nat :
  ∀ (f : FnName) (a : Val), Val.hasTy a .nat = true → Val.hasTy (f.total a) .nat = true)

#check (@Effect4.Program.FnName.partialUpdate_hasTy_nat :
  ∀ (f : FnName) (a a' : Val), f.partialUpdate a = some a' → Val.hasTy a .nat = true →
    Val.hasTy a' .nat = true)

#check (@Effect4.Program.FnName.modify_hasTy_nat :
  ∀ (f : FnName) (a : Val), Val.hasTy a .nat = true →
    Val.hasTy (f.modify a).1 .nat = true ∧ Val.hasTy (f.modify a).2 .nat = true)

#check (@Effect4.Program.FnName.modifySome_hasTy_nat :
  ∀ (f : FnName) (a : Val), Val.hasTy a .nat = true →
    Val.hasTy (f.modifySome a).1 .nat = true ∧
      Val.hasTy ((f.modifySome a).2.getD a) .nat = true)

#check (@Effect4.Program.Val.hasTy_cell_refTy :
  ∀ (k : RefKey), Val.hasTy (Val.cell k) NativeOp.refTy = true)
#check (@Effect4.Program.Val.hasTy_promise_deferredTy :
  ∀ (k : DeferredKey), Val.hasTy (Val.promise k) NativeOp.deferredTy = true)
#check (@Effect4.Program.Val.hasTy_scopeHandle_scope :
  ∀ (n : Nat), Val.hasTy (Val.scopeHandle n) Ty.scope = true)

#check (@Effect4.Program.refPoke_heapNat :
  ∀ (s : Stores) (cell : RefKey) (y : Val), Stores.HeapNat s → Val.hasTy y .nat = true →
    Stores.HeapNat { s with refs := refPoke s.refs cell y })

#check (@Effect4.Program.refStep_of_syncOpStep :
  ∀ {o : SyncOp} {s s' : Stores} {a : Val},
    (refStep o s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = some (s', a) →
      ∃ heap', refStep o s.refs = some (a, heap') ∧ s' = { s with refs := heap' })

#check (@Effect4.Program.step_typed :
  ∀ (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val),
    Stores.HeapNat s → Val.hasTy v (NativeOp.row op).request = true →
      NativeOp.syncOpOf op v = some o → syncOpStep o s = some (s', a) →
        Val.hasTy a (NativeOp.row op).answer = true ∧ Stores.HeapNat s')

#check (@Effect4.Program.answer_typed :
  ∀ (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val),
    Stores.HeapNat s → Val.hasTy v (NativeOp.row op).request = true →
      NativeOp.syncOpOf op v = some o → syncOpStep o s = some (s', a) →
        Val.hasTy a (NativeOp.row op).answer = true)

#check (@Effect4.Program.step_heapNat :
  ∀ (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val),
    Stores.HeapNat s → Val.hasTy v (NativeOp.row op).request = true →
      NativeOp.syncOpOf op v = some o → syncOpStep o s = some (s', a) → Stores.HeapNat s')

#check (@Effect4.Program.syncOpOf_validIn :
  ∀ (op : NativeOp) (v : Val) (o : SyncOp) (s : Stores),
    Val.hasTy v (NativeOp.row op).request = true → NativeOp.syncOpOf op v = some o →
      v.validIn s = true → o.validIn s = true)

#check (@Effect4.Program.progress :
  ∀ (op : NativeOp) (v : Val) (s : Stores),
    s.WF → Stores.HeapNat s → (NativeOp.row op).kind = .sync →
      Val.hasTy v (NativeOp.row op).request = true → v.validIn s = true →
        ∃ o s' a, NativeOp.syncOpOf op v = some o ∧ syncOpStep o s = some (s', a) ∧
          Val.hasTy a (NativeOp.row op).answer = true ∧ a.validIn s' = true ∧
          s'.WF ∧ Stores.HeapNat s')

end Statements

/-! ## Harness: stores reached by one step, and the answers -/

/-- The store after one step, or the store it started from when the step refuses. -/
def after (o : SyncOp) (s : Stores) : Stores := ((syncOpStep o s).map Prod.fst).getD s

/-- The answer of one step. -/
def answer (o : SyncOp) (s : Stores) : Option Val := (syncOpStep o s).map Prod.snd

/-- `Ref.make(5)` on the empty store: the first step of `pRefSet`, `pRefUpdate` and
`pRefModify`. -/
def s1 : Stores := after (SyncOp.refMake (Val.nat 5)) Stores.empty
/-- `Ref.set(ref, 7)` after `Ref.make(5)`: `pRefSet`'s second step. -/
def s1set : Stores := after (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1
/-- `Ref.update(ref, incr)` after `Ref.make(5)`: `pRefUpdate`'s second step. -/
def s1upd : Stores := after (SyncOp.refUpdate ⟨0⟩ .incr) s1
/-- `Ref.modify(ref, takeAndBump)` after `Ref.make(5)`: `pRefModify`'s second step. -/
def s1mod : Stores := after (SyncOp.refModify ⟨0⟩ .takeAndBump) s1
/-- `Deferred.make()` on the empty store. -/
def s2 : Stores := after SyncOp.deferredMake Stores.empty
/-- `Deferred.succeed(d, 1)` after `Deferred.make()`. -/
def s2done : Stores :=
  after (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
/-- A heap holding a boolean: well-formed, not numeric. -/
def boolCell : Stores := { Stores.empty with refs := [Val.bool true] }

/-- `pRefSet`'s `Ref.set` request: the pair of the cell and the number. -/
def setRequest : Val := Val.tuple [Val.cell ⟨0⟩, Val.nat 7]
/-- `Deferred.succeed`'s request: the pair of the promise and the number. -/
def succeedRequest : Val := Val.tuple [Val.promise ⟨0⟩, Val.nat 1]

/-! ## The register rows -/

section Rows

-- E4-PROGRESS-CE-001: `WF` is the handle half only; the answer's type needs `HeapNat`
#guard Stores.WF boolCell
#guard SyncOp.validIn boolCell (SyncOp.refGet ⟨0⟩) = true
#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row .refGet).request
#guard NativeOp.syncOpOf .refGet (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard answer (SyncOp.refGet ⟨0⟩) boolCell = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (NativeOp.row .refGet).answer = false
#guard ¬ Stores.HeapNat boolCell

-- E4-PROGRESS-CE-002: validity does not keep `HeapNat`; the typed request does
#guard Stores.HeapNat Stores.empty
#guard SyncOp.validIn Stores.empty (SyncOp.refMake (Val.bool true)) = true
#guard (syncOpStep (SyncOp.refMake (Val.bool true)) Stores.empty).isSome
#guard ¬ Stores.HeapNat (after (SyncOp.refMake (Val.bool true)) Stores.empty)
#guard Val.hasTy (Val.bool true) (NativeOp.row .refMake).request = false
#guard NativeOp.syncOpOf .refMake (Val.bool true) = none

end Rows

/-! ## `pRefSet`: `Ref.make(5)`, `Ref.set(ref, 7)`, `Ref.get(ref)` -/

section RefSet

-- `Ref.make(5)` on the empty store
#guard Stores.HeapNat Stores.empty
#guard Val.hasTy (Val.nat 5) (NativeOp.row .refMake).request
#guard NativeOp.syncOpOf .refMake (Val.nat 5) = some (SyncOp.refMake (Val.nat 5))
#guard SyncOp.validIn Stores.empty (SyncOp.refMake (Val.nat 5)) = true
#guard answer (SyncOp.refMake (Val.nat 5)) Stores.empty = some (Val.cell ⟨0⟩)
#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row .refMake).answer
#guard Val.validIn s1 (Val.cell ⟨0⟩)
#guard Stores.WF s1
#guard Stores.HeapNat s1
#guard s1.refs = [Val.nat 5]

-- `Ref.set(ref, 7)`: the request is the pair, the answer is the cell
#guard Val.hasTy setRequest (NativeOp.row .refSet).request
#guard Val.validIn s1 setRequest
#guard NativeOp.syncOpOf .refSet setRequest = some (SyncOp.refSet ⟨0⟩ (Val.nat 7))
#guard SyncOp.validIn s1 (SyncOp.refSet ⟨0⟩ (Val.nat 7)) = true
#guard answer (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1 = some (Val.cell ⟨0⟩)
#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row .refSet).answer
#guard Val.validIn s1set (Val.cell ⟨0⟩)
#guard Stores.WF s1set
#guard Stores.HeapNat s1set
#guard s1set.refs = [Val.nat 7]

-- `Ref.get(ref)`: the answer is the cell's number
#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row .refGet).request
#guard NativeOp.syncOpOf .refGet (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard SyncOp.validIn s1set (SyncOp.refGet ⟨0⟩) = true
#guard answer (SyncOp.refGet ⟨0⟩) s1set = some (Val.nat 7)
#guard Val.hasTy (Val.nat 7) (NativeOp.row .refGet).answer
#guard after (SyncOp.refGet ⟨0⟩) s1set = s1set

end RefSet

/-! ## `pRefUpdate`: `Ref.make(5)`, `Ref.update(ref, incr)`, `Ref.get(ref)` -/

section RefUpdate

#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row (.refUpdate .incr)).request
#guard NativeOp.syncOpOf (.refUpdate .incr) (Val.cell ⟨0⟩)
  = some (SyncOp.refUpdate ⟨0⟩ .incr)
#guard SyncOp.validIn s1 (SyncOp.refUpdate ⟨0⟩ .incr) = true
#guard answer (SyncOp.refUpdate ⟨0⟩ .incr) s1 = some Val.unit
#guard Val.hasTy Val.unit (NativeOp.row (.refUpdate .incr)).answer
#guard Stores.WF s1upd
#guard Stores.HeapNat s1upd
#guard s1upd.refs = [Val.nat 6]
#guard answer (SyncOp.refGet ⟨0⟩) s1upd = some (Val.nat 6)
#guard Val.hasTy (Val.nat 6) (NativeOp.row .refGet).answer

end RefUpdate

/-! ## `pRefModify`: `Ref.make(5)`, `Ref.modify(ref, takeAndBump)` -/

section RefModify

#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row (.refModify .takeAndBump)).request
#guard NativeOp.syncOpOf (.refModify .takeAndBump) (Val.cell ⟨0⟩)
  = some (SyncOp.refModify ⟨0⟩ .takeAndBump)
#guard SyncOp.validIn s1 (SyncOp.refModify ⟨0⟩ .takeAndBump) = true
#guard answer (SyncOp.refModify ⟨0⟩ .takeAndBump) s1 = some (Val.nat 5)
#guard Val.hasTy (Val.nat 5) (NativeOp.row (.refModify .takeAndBump)).answer
#guard Stores.WF s1mod
#guard Stores.HeapNat s1mod
#guard s1mod.refs = [Val.nat 6]

end RefModify

/-! ## The pure functions on numbers (`Stores.lean:458-482`) -/

section Functions

#guard Val.hasTy (FnName.total .incr (Val.nat 5)) .nat
#guard Val.hasTy (FnName.total .double (Val.nat 5)) .nat
#guard Val.hasTy (FnName.total .noChange (Val.nat 5)) .nat
#guard (FnName.partialUpdate .zeroWhenPositive (Val.nat 5)).map (Val.hasTy · .nat) = some true
#guard FnName.partialUpdate .zeroWhenPositive (Val.nat 0) = none
#guard FnName.partialUpdate .noChange (Val.nat 5) = none
#guard Val.hasTy (FnName.modify .takeAndBump (Val.nat 5)).1 .nat
#guard Val.hasTy (FnName.modify .takeAndBump (Val.nat 5)).2 .nat
#guard Val.hasTy (FnName.modifySome .noChange (Val.nat 5)).1 .nat
#guard Val.hasTy ((FnName.modifySome .noChange (Val.nat 5)).2.getD (Val.nat 5)) .nat
-- the functions fix a non-number, so the typing of the result is the typing of the argument
#guard Val.hasTy (FnName.total .incr (Val.bool true)) .nat = false

end Functions

/-! ## The Deferred rows (`Stores.lean:1210-1219`) -/

section Deferred

#guard Val.hasTy Val.unit (NativeOp.row .deferredMake).request
#guard NativeOp.syncOpOf .deferredMake Val.unit = some SyncOp.deferredMake
#guard answer SyncOp.deferredMake Stores.empty = some (Val.promise ⟨0⟩)
#guard Val.hasTy (Val.promise ⟨0⟩) (NativeOp.row .deferredMake).answer
#guard Val.validIn s2 (Val.promise ⟨0⟩)
#guard Stores.WF s2
#guard Stores.HeapNat s2

#guard Val.hasTy succeedRequest (NativeOp.row .deferredSucceed).request
#guard Val.validIn s2 succeedRequest
#guard NativeOp.syncOpOf .deferredSucceed succeedRequest
  = some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1))))
#guard SyncOp.validIn s2
  (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) = true
#guard answer
  (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
  = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (NativeOp.row .deferredSucceed).answer
#guard Stores.WF s2done
#guard Stores.HeapNat s2done

#guard Val.hasTy (Val.promise ⟨0⟩) (NativeOp.row .deferredIsDone).request
#guard NativeOp.syncOpOf .deferredIsDone (Val.promise ⟨0⟩)
  = some (SyncOp.deferredIsDone ⟨0⟩)
#guard answer (SyncOp.deferredIsDone ⟨0⟩) s2done = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (NativeOp.row .deferredIsDone).answer
#guard answer (SyncOp.deferredPoll ⟨0⟩) s2 = some (Val.bool false)
#guard Val.hasTy (Val.bool false) (NativeOp.row .deferredPoll).answer

-- the async row decodes to nothing: `answer_typed` has nothing to say about it
#guard (NativeOp.row .deferredAwait).kind = .async
#guard NativeOp.syncOpOf .deferredAwait (Val.promise ⟨0⟩) = none

end Deferred

/-! ## The Scope row (`Stores.lean:1227-1229`) -/

section Scope

#guard Val.hasTy Val.unit (NativeOp.row (.scopeMake .sequential)).request
#guard NativeOp.syncOpOf (.scopeMake .sequential) Val.unit = some (SyncOp.scopeMake .sequential)
#guard answer (SyncOp.scopeMake .sequential) Stores.empty = some (Val.scopeHandle 0)
#guard Val.hasTy (Val.scopeHandle 0) (NativeOp.row (.scopeMake .sequential)).answer
#guard Val.hasTy (Val.scopeHandle 0) (NativeOp.row (.scopeMake .parallel)).answer
#guard Val.validIn (after (SyncOp.scopeMake .sequential) Stores.empty) (Val.scopeHandle 0)
#guard Stores.HeapNat (after (SyncOp.scopeMake .sequential) Stores.empty)

end Scope

end Test.Program.ProgressContract
