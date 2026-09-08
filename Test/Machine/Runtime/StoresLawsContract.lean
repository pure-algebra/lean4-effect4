import Effect4.Machine.StoresLaws
import Effect4.Machine.StoresValue
import Effect4.Machine.ContextValue

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
#guard SyncOp.validIn s3 (SyncOp.scopeAdd 0 (FinName.release 1 false)) = true
#guard answer (SyncOp.scopeAdd 0 (FinName.release 1 false)) s3 = some Val.unit
#guard Val.validIn (after (SyncOp.scopeAdd 0 (FinName.release 1 false)) s3) (Val.scopeHandle 0)
-- the registration key is the supply's value, and the supply advances (`E4-CHECK-CE-016`)
#guard (after (SyncOp.scopeAdd 0 (FinName.release 1 false)) s3).nextName = 2
-- a registration on an unknown scope is a frontier, never a cause (M7)
#guard syncOpStep (SyncOp.scopeAdd 7 (FinName.release 1 false)) s3 = none
#guard answer (SyncOp.scopeMake .parallel) s3 = some (Val.scopeHandle 1)

end Scope

/-! ## Make-then-read on the memo world (`Layer.ts:396-458`, the join)

The Layer machine's memo store on the one `Stores`: a root map, a miss, a build (which
allocates the layer scope and the Deferred from the one supply), a hit that bumps the observer
count and answers the Deferred and the owner, two releases of which the last answers the layer
scope, a forked map that falls through to its parent, and `memoComplete`'s completion of the
build's Deferred — the wakeup borrowed from the Deferred family. -/

section Memo

/-- `makeMemoMapUnsafe()` on the empty store: map `⟨0⟩`. -/
def sM : Stores := after (SyncOp.memoFork none) Stores.empty
/-- `memoMapBuild`'s synchronous half for the layer at path `[0]`: scope `1`, Deferred `⟨0⟩`. -/
def sB : Stores := after (SyncOp.memoBuild [0] ⟨0⟩) sM
/-- A hit on the built entry. -/
def sG : Stores := after (SyncOp.memoGet [0] ⟨0⟩) sB
/-- A map forked off the root: `⟨2⟩`. -/
def sF : Stores := after (SyncOp.memoFork (some ⟨0⟩)) sB

#guard answer (SyncOp.memoFork none) Stores.empty = some (Val.memoMap ⟨0⟩)
#guard Val.validIn sM (Val.memoMap ⟨0⟩)
#guard Val.validIn Stores.empty (Val.memoMap ⟨0⟩) = false
#guard SyncOp.validIn Stores.empty (SyncOp.memoGet [0] ⟨0⟩) = false
#guard answer (SyncOp.memoGet [0] ⟨0⟩) sM = some Val.unit
#guard answer (SyncOp.memoBuild [0] ⟨0⟩) sM = some (Val.scopeHandle 1)
#guard sB.nextName = 2
#guard Val.validIn sB (Val.scopeHandle 1)
#guard Val.validIn sB (Val.promise ⟨0⟩)
#guard Stores.WF sB
-- a hit answers the entry's Deferred and its owner, and bumps the observers
#guard answer (SyncOp.memoGet [0] ⟨0⟩) sB = some (Val.pair (Val.promise ⟨0⟩) (Val.memoMap ⟨0⟩))
#guard (sG.memo.entryAt ⟨0⟩ [0]).map (·.observers) = some 2
#guard (answer (SyncOp.memoGet [0] ⟨0⟩) sB).map (Val.validIn sG) = some true
-- the second release is the last: the entry goes, the layer scope is answered to close
#guard answer (SyncOp.memoRelease [0] ⟨0⟩) sG = some Val.unit
#guard answer (SyncOp.memoRelease [0] ⟨0⟩) (after (SyncOp.memoRelease [0] ⟨0⟩) sG) =
  some (Val.scopeHandle 1)
#guard ((after (SyncOp.memoRelease [0] ⟨0⟩) (after (SyncOp.memoRelease [0] ⟨0⟩) sG)).memo.entryAt
  ⟨0⟩ [0]).isNone
-- a forked map falls through to its parent; another path is a miss
#guard answer (SyncOp.memoGet [0] ⟨2⟩) sF = some (Val.pair (Val.promise ⟨0⟩) (Val.memoMap ⟨0⟩))
#guard answer (SyncOp.memoGet [1] ⟨2⟩) sF = some Val.unit
-- `memoComplete` completes the build's Deferred: the Deferred family's wakeup, borrowed
#guard answer (SyncOp.deferredIsDone ⟨0⟩) sB = some (Val.bool false)
#guard answer (SyncOp.deferredIsDone ⟨0⟩)
  (after (SyncOp.memoComplete [0] ⟨0⟩ (Exit.success Val.unit)) sB) = some (Val.bool true)
#guard Stores.WF (after (SyncOp.memoComplete [0] ⟨0⟩ (Exit.success Val.unit)) sB)
-- `scopeForkUnsafe`: the child at the supply, linked under the shared key next
#guard answer (SyncOp.scopeFork 0 .sequential) s3 = some (Val.scopeHandle 1)
#guard (after (SyncOp.scopeFork 0 .sequential) s3).nextName = 3
#guard syncOpStep (SyncOp.scopeFork 7 .sequential) s3 = none

end Memo

/-! ## Compound values, and the reads -/

section Values

#guard Val.validIn s1 (Val.exitOk (Val.cell ⟨0⟩))
#guard Val.validIn s1 (Val.list [Val.cell ⟨0⟩, Val.nat 1])
#guard Val.validIn s1 (Val.list [Val.cell ⟨1⟩]) = false
#guard Val.validIn Stores.empty (Val.fiber ⟨3⟩)
#guard Val.validIn Stores.empty (Val.exitErr (Cause.fail Err.boom))
#guard SyncOp.isRead (SyncOp.refGet ⟨0⟩)
#guard SyncOp.isRead (SyncOp.deferredIsDone ⟨0⟩)
#guard SyncOp.isRead (SyncOp.deferredPoll ⟨0⟩)
#guard SyncOp.isRead (SyncOp.scopeIsClosed 0)
#guard SyncOp.isRead (SyncOp.refSet ⟨0⟩ Val.unit) = false
#guard SyncOp.isRead SyncOp.deferredMake = false

end Values

/-! ## The shared value foundation (U0, cut over in U1a)

`Machine.Val` is the shared carrier (`src/Effect4/Machine/Stores.lean`, per
`docs/research/2026-09-07-u1-cutover-dispatch.md` on the U0 contract
`docs/research/2026-09-07-u0-value-foundation.md`), smoke-tested on the values the sections
above build: the spellings are the U0 table's shapes, the readers (`Val.snapshot?`,
`Val.context?`, `Val.cause?`, `exitImage.ofVal`) are exact, the handle kinds stay distinct,
the fiber snapshot is not a list of exits, a cause carries no handle, `Val.keys` is the
carrier's `handles` read through `Handle.ofCode`, validity folds the handles, the spellings
work as patterns, and malformed trees are refused. -/

section Foundation

open Effect4.Store (Image)

/-- The value the C2 section reads back: a cell and a number in a two-cell list. -/
def tupleV : Val := Val.list [Val.cell ⟨0⟩, Val.nat 1]

/-- A nested exit: a success carrying a reified failure. -/
def nestedV : Val := Val.exitOk (Val.exitErr (Cause.fail (Err.tag 3)))

/-- A cached context with an ambient scope. -/
def ctxV : Val := Val.context (emptyCtx.withScope 2)

-- The spellings are the table's shapes.
#guard Val.cell ⟨3⟩ = Value.cell 3
#guard Val.fiber ⟨3⟩ = Store.Val.handle 1 3
#guard Val.exitNil = Val.list []
#guard Val.fibers [⟨1⟩, ⟨2⟩] = Value.fiberSnapshot (Val.list [Value.fiber 1, Value.fiber 2])
#guard ctxV = Value.fiberContext
  (Value.serviceContext [Store.Val.pair (Env.serviceKeyImage.toVal Env.scopeKey) (Value.scope 2)])
  (Val.nat 2048) (Val.bool false)
#guard nestedV = Value.exitOk (Value.exitErr (causeImage.toVal (Cause.fail (Err.tag 3))))
-- The readers are exact on representative values: the snapshot, a context, a cause, a
-- reified exit, an empty and a non-empty exit list.
#guard Val.snapshot? (Val.fibers [⟨1⟩, ⟨2⟩]) = some [⟨1⟩, ⟨2⟩]
#guard Val.context? ctxV = some (emptyCtx.withScope 2)
#guard Val.cause? (Val.exitErr (Cause.interrupt (some ⟨9⟩))) = some (Cause.interrupt (some ⟨9⟩))
#guard exitImage.ofVal nestedV = some (Exit.success (Val.exitErr (Cause.fail (Err.tag 3))))
#guard exitImage.ofVal (reifyExitVal (Exit.failure (Cause.die (Defect.user 4)))) =
  some (Exit.failure (Cause.die (Defect.user 4)))
#guard exitsVal [] = Val.exitNil
#guard exitsVal [Exit.success (Val.promise ⟨4⟩), Exit.failure (Cause.fail Err.boom)] =
  Val.list [Val.exitOk (Val.promise ⟨4⟩), Val.exitErr (Cause.fail Err.boom)]
#guard reasonsOfVal (exitsVal [Exit.success (Val.nat 1), Exit.failure (Cause.fail Err.boom)]) =
  [Reason.fail Err.boom ⟨[], List.nodup_nil⟩]
-- The snapshot of a fiber and the exit list holding that fiber are distinct trees; the kinds
-- of a handle at one index are distinct trees.
#guard Val.fibers [⟨1⟩] ≠ Val.list [Val.fiber ⟨1⟩]
#guard Val.cell ⟨1⟩ ≠ Val.promise ⟨1⟩
#guard Val.fiber ⟨1⟩ ≠ Val.scopeHandle 1
-- `Val.keys` is the carrier's `handles` read through `Handle.ofCode`; a cause names no handle
-- even when it records a fiber; the Layer machine's memo-map handle and an unregistered byte
-- are no frame-machine handle.
#guard Val.keys (Val.list [tupleV, ctxV]) = [Handle.cell ⟨0⟩, Handle.scope 2]
#guard (Val.list [tupleV, ctxV]).handles = (Val.keys (Val.list [tupleV, ctxV])).map Handle.code
#guard (Val.exitErr (Cause.interrupt (some ⟨9⟩))).handles = []
#guard (Val.exitErr (Cause.interrupt (some ⟨9⟩))).keys = []
#guard (Val.fibers [⟨1⟩, ⟨2⟩]).handles = [(1, 1), (1, 2)]
#guard (Val.fibers [⟨1⟩, ⟨2⟩]).keys = [Handle.fiber ⟨1⟩, Handle.fiber ⟨2⟩]
#guard Val.keys (Value.memoMap 1) = [Handle.memoMap 1]
#guard Val.keys (Store.Val.handle 9 1) = []
#guard Handle.image.ofVal (Value.memoMap 1) = some (Handle.memoMap 1)
#guard Handle.image.ofVal (Store.Val.handle 9 1) = none
-- Refused by the readers: a snapshot of non-handles, a cause with an unknown reason index, a
-- context with a number where the scope goes, an exit with two payloads, a string.
#guard Val.snapshot? (Value.fiberSnapshot (Val.list [Val.nat 1])) = none
#guard Val.cause? (Value.exitErr (Store.Val.ctor 0 [Val.list [Store.Val.ctor 7 []]])) = none
#guard Val.context? (Value.fiberContext (Store.Val.some (Val.nat 2)) (Val.nat 0) (Val.bool true)) = none
#guard exitImage.ofVal (Store.Val.ctor 0 [Val.nat 1, Val.nat 2]) = none
#guard exitImage.ofVal (Val.str "x") = none
-- Validity folds the handles: a context's ambient scope is checked (U1: the old carrier
-- accepted every context), a memo-map handle and an unregistered byte are never valid here.
#guard Val.validIn s3 ctxV = false
#guard Val.validIn s3 (Val.context (emptyCtx.withScope 0)) = true
#guard Val.validIn s3 (Value.memoMap 0) = false
#guard Val.validIn Stores.empty (Store.Val.handle 9 0) = false
-- Bytes: the checked encoder of the exit image answers, and its answer reads back.
#guard (exitImage.encode? (Exit.success tupleV)).bind exitImage.decode = some (Exit.success tupleV)
#guard (exitImage.encode? (Exit.failure (Cause.die (Defect.user 4)))).bind exitImage.decode =
  some (Exit.failure (Cause.die (Defect.user 4)))
-- A reified exit *value* and the exit *record* share one encoding (D1): the bytes of
-- `exitOk (exitErr c)` read back, as an exit, to `Exit.success (exitErr c)`; a value that is
-- not an exit is refused by the exit image.
#guard exitImage.decode (Store.Val.encode nestedV) =
  some (Exit.success (Val.exitErr (Cause.fail (Err.tag 3))))
#guard exitImage.decode (Store.Val.encode tupleV) = none

/-- The spellings are patterns: a `match` over the carrier by the runtime's shapes. -/
def shapeCode : Val → Nat
  | Val.fiber ⟨_⟩ => 1
  | Val.cell ⟨_⟩ => 2
  | Val.promise ⟨_⟩ => 3
  | Val.scopeHandle _ => 4
  | Val.exitOk _ => 10
  | Value.exitErr _ => 11
  | Value.fiberSnapshot _ => 13
  | _ => 0

#guard shapeCode (Val.cell ⟨3⟩) = 2
#guard shapeCode (Val.exitOk Val.unit) = 10
#guard shapeCode (Val.fibers []) = 13
#guard shapeCode tupleV = 0

-- The Layer machine's alphabet is the same carrier (U1b): a service context round-trips and
-- reads back its entries; the memo-map handle is admitted there; a spine of non-pairs and a
-- bad key are refused.
#guard Env.decode (Env.encode
    (((Env.Context.empty : Env.Ctx).addV ⟨⟨1⟩, ⟨2⟩⟩ (Env.Val.memoMap 4)).addV ⟨⟨3⟩, ⟨0⟩⟩ Env.Val.unit)) =
  some (((Env.Context.empty : Env.Ctx).addV ⟨⟨1⟩, ⟨2⟩⟩ (Env.Val.memoMap 4)).addV ⟨⟨3⟩, ⟨0⟩⟩ Env.Val.unit)
#guard Env.Val.pair (Env.Val.promise 1) (Env.Val.memoMap 2) =
  Store.Val.pair (Value.promise 1) (Value.memoMap 2)
#guard Env.decode (Value.serviceContext [Store.Val.nat 7]) = none
#guard Env.decode (Value.serviceContext [Store.Val.pair (Store.Val.nat 1) (Store.Val.nat 7)]) = none
#guard Env.decode (Value.cell 3) = none
#guard (Env.encode ((Env.Context.empty : Env.Ctx).addV ⟨⟨1⟩, ⟨2⟩⟩ (Env.Val.scopeHandle 4))).handles =
  [(4, 4)]
-- The service context and the cached fiber context are distinct trees.
#guard Env.encode (Env.Context.empty : Env.Ctx) ≠ Val.context emptyCtx
-- The hand-written key image writes the bytes the generated OCaml encoder writes
-- (`ocaml/eff/eff_wire.ml` `emit_service_key`, run against the `effect4` switch on
-- 2026-09-07 for the key `{1, 2}`: 74 bytes, listed here), so one decoder serves both.
#guard Env.serviceKeyImage.encode ⟨⟨1⟩, ⟨2⟩⟩ =
  [0x0a, 0, 0, 0, 0, 0, 0, 0, 0x41,
   0x02, 0, 0, 0, 0, 0, 0, 0, 0x00,
   0x0a, 0, 0, 0, 0, 0, 0, 0, 0x13,
   0x02, 0, 0, 0, 0, 0, 0, 0, 0x00,
   0x02, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x01,
   0x0a, 0, 0, 0, 0, 0, 0, 0, 0x13,
   0x02, 0, 0, 0, 0, 0, 0, 0, 0x00,
   0x02, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x02]
#guard (Env.serviceKeyImage.encode ⟨⟨1⟩, ⟨2⟩⟩).length = 74

#check (@Effect4.Machine.Val.keys_eq_handles :
  ∀ (v : Val), v.keys = v.handles.filterMap Handle.ofCode)
#check (@Effect4.Machine.Val.validIn_eq_handles :
  ∀ (s : Stores) (v : Val), v.validIn s = v.handles.all fun h => s.handleValid h.1 h.2)
#check @Effect4.Machine.Env.Val.ofSpine_entries

#print axioms Effect4.Machine.Val.image
#print axioms Effect4.Machine.Val.keys_eq_handles
#print axioms Effect4.Machine.Val.validIn_eq_handles
#print axioms Effect4.Machine.Val.handles_eq_keys_code
#print axioms Effect4.Machine.exitImage
#print axioms Effect4.Machine.Env.Val.image
#print axioms Effect4.Machine.Env.Val.ofSpine_entries

end Foundation

end Test.Runtime.StoresLawsContract
