import Effect4.Machine.Stores

/-!
# Machine.StoresLaws — growth, validity and well-formedness of the stores (slice 1, lane 2)

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §3. Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 10–17. Batteries:
`Test/Machine/Runtime/StoresLawsContract.lean` (the guards and the rows `E4-STORES-CE-001`,
`E4-STORES-CE-002`, `E4-STORES-CE-003`) and `Test/Machine/Runtime/StoresLawsAxiomReport.lean`.

This module orders `Effect4.Machine.Stores` (`src/Effect4/Machine/Stores.lean:1029-1043`) by
growth, says when a value's handles and an operation's keys exist in a store, and proves that
a valid operation always steps through `syncOpStep` (`Stores.lean:1209-1240`), grows the
store, keeps the heap well-formed, and answers a valid value. The store half of handle
validity (plan §1.3): the machine-wide `handles_minted` invariant is a later slice.

What is deliberately not said, each named so it is a refusal and not an omission:

* `STORES-FB-COMPLETION` — `Stores.WF` speaks only of the heap. A `Completion` stored in a
  Deferred cell (`Stores.lean:680-693`, `completionPrim` at `:1083`) is a `Prim` and is not
  traversed by `Val.validIn`; a Deferred completed with `ofRefGet cell` on a dangling cell is
  not excluded (plan §7, row `E4-STORES-CE-003`). `WF` is not widened in this slice.
* `Val.fiber` and `Val.fibers` are the machine's handles, not the store's: `validIn` accepts
  them (`Stores.handleValid`, the fiber byte).
* `Val.exitErr` carries a cause and no handle; it is valid everywhere (`Val.validIn_exitErr`).
* `ScopeStore.forkChild` is reached through `SyncOp.scopeFork` since the join; the memo world's
  operations are the join's, with `Stores.MemoValid` the conjunct `WF` gained for them.

`SyncOp.validIn` is a sufficient condition for `syncOpStep` to answer, not a necessary one:
`deferredCompleteWith` on an unknown cell answers `false` without stepping into the frontier
(`DeferredStore.complete`, `Stores.lean:742-751`), and the argument value of `refMake` is
part of validity because `syncOpStep_wf` stores it (plan §7).
-/

set_option autoImplicit false

namespace Effect4.Machine

/-! ## The growth order -/

/-- The stores only grow (plan §3.1, ENSURES 10): a heap never shrinks (`refStep`,
`Stores.lean:484`, appends or sets in place), a Deferred cell is never freed
(`DeferredStore.make` appends, `setCell` sets in place, `:700-710`), a scope entry is never
removed (`ScopeStore.make` appends, `setEntry` maps in place, `:906-912`), and the name
counter never decreases (`syncOpStep`'s `scopeMake` arm, `:1225-1227`). -/
def Stores.le (s s' : Stores) : Prop :=
  s.refs.length ≤ s'.refs.length ∧
  s.deferreds.cells.length ≤ s'.deferreds.cells.length ∧
  (∀ key, (s.scopes.entryAt key).isSome = true → (s'.scopes.entryAt key).isSome = true) ∧
  s.nextName ≤ s'.nextName ∧
  -- a memo map is never removed (`memoFork` appends, `setMap` maps in place; the join)
  ∀ id, (s.memo.mapAt id).isSome = true → (s'.memo.mapAt id).isSome = true

/-- Reflexive (ENSURES 10). -/
theorem Stores.le_refl (s : Stores) : s.le s :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h⟩

/-- Transitive (ENSURES 10). -/
theorem Stores.le_trans {s s' s'' : Stores} (h : s.le s') (h' : s'.le s'') : s.le s'' :=
  ⟨Nat.le_trans h.1 h'.1, Nat.le_trans h.2.1 h'.2.1,
    fun key hk => h'.2.2.1 key (h.2.2.1 key hk), Nat.le_trans h.2.2.2.1 h'.2.2.2.1,
    fun id hm => h'.2.2.2.2 id (h.2.2.2.2 id hm)⟩

/-! ## Validity -/

/-- One handle's kind byte and index against the store (plan §3.1, ENSURES 12): a cell byte
needs a heap index (`Stores.lean` `refPeek`), a promise byte a Deferred cell index
(`cellAt`), a scope byte a scope entry (`entryAt`); a fiber byte is the machine's, not the
store's, and is accepted; a `memoMap` byte a memo map (`MemoWorld.mapAt`, the join); an
unregistered byte names nothing this store holds. -/
def Stores.handleValid (s : Stores) (kind : UInt8) (index : Nat) : Bool :=
  match HandleKind.ofByte? kind with
  | some .fiber => true
  | some .cell => index < s.refs.length
  | some .promise => index < s.deferreds.cells.length
  | some .scope => (s.scopes.entryAt index).isSome
  | some .memoMap => (s.memo.mapAt ⟨index⟩).isSome
  | none => false

mutual
/-- A value's handles exist in the store (plan §3.1, ENSURES 12): every `handle` frame the
carrier carries, through `Stores.handleValid` — a `Val.cell` names a heap index, a
`Val.promise` a Deferred cell, a `Val.scopeHandle` a scope entry, a context its ambient scope;
a reified exit, a snapshot and a list are valid when their parts are; a tree with no handle
(a number, a reified failed exit, whose cause writes none) is valid everywhere.
`Val.validIn_eq_handles` is the fold over `Store.Val.handles`. -/
def Val.validIn (s : Stores) : Val → Bool
  | .handle kind index => s.handleValid kind index
  | .list values => Val.validInList s values
  | .pair a b => Val.validIn s a && Val.validIn s b
  | .some a => Val.validIn s a
  | .ctor _ args => Val.validInList s args
  | _ => true
/-- Every value of a list is valid. -/
def Val.validInList (s : Stores) : List Val → Bool
  | [] => true
  | value :: rest => Val.validIn s value && Val.validInList s rest
end

theorem Val.validIn_cell (s : Stores) (k : RefKey) :
    Val.validIn s (Val.cell k) = decide (k.index < s.refs.length) := rfl
theorem Val.validIn_promise (s : Stores) (k : DeferredKey) :
    Val.validIn s (Val.promise k) = decide (k.index < s.deferreds.cells.length) := rfl
theorem Val.validIn_scopeHandle (s : Stores) (key : Nat) :
    Val.validIn s (Val.scopeHandle key) = (s.scopes.entryAt key).isSome := rfl
theorem Val.validIn_memoMap (s : Stores) (id : MemoMapId) :
    Val.validIn s (Val.memoMap id) = (s.memo.mapAt id).isSome := rfl
theorem Val.validIn_fiber (s : Stores) (id : FiberId) : Val.validIn s (Val.fiber id) = true := rfl
theorem Val.validIn_exitOk (s : Stores) (v : Val) : Val.validIn s (Val.exitOk v) = Val.validIn s v := by
  simp only [Val.validIn, Val.validInList, Bool.and_true]

theorem Val.validInList_eq_all (s : Stores) (values : List Val) :
    Val.validInList s values = values.all (Val.validIn s) := by
  induction values with
  | nil => rfl
  | cons value rest ih => rw [Val.validInList, ih, List.all_cons]

theorem Val.validIn_list (s : Stores) (values : List Val) :
    Val.validIn s (Val.list values) = values.all (Val.validIn s) :=
  Val.validInList_eq_all s values

theorem Val.validInList_eq_handlesList (s : Stores) (values : List Val)
    (ih : ∀ x ∈ values, x.validIn s = x.handles.all fun h => s.handleValid h.1 h.2) :
    Val.validInList s values =
      (Store.Val.handlesList values).all fun h => s.handleValid h.1 h.2 := by
  induction values with
  | nil => rfl
  | cons value rest ihr =>
    rw [Val.validInList, Store.Val.handlesList_cons, List.all_append, ih value (by simp),
      ihr (fun x hx => ih x (by simp [hx]))]

/-- Validity is the fold of `Stores.handleValid` over the carrier's `handle` frames. -/
theorem Val.validIn_eq_handles (s : Stores) (v : Val) :
    v.validIn s = v.handles.all fun h => s.handleValid h.1 h.2 := by
  induction v using Store.Val.ind with
  | unit => rfl
  | bool _ => rfl
  | nat _ => rfl
  | str _ => rfl
  | bytes _ => rfl
  | none => rfl
  | ref _ _ => rfl
  | handle kind index =>
    show s.handleValid kind index = List.all [(kind, index)] fun h => s.handleValid h.1 h.2
    rw [List.all_cons, List.all_nil, Bool.and_true]
  | list values ih => exact Val.validInList_eq_handlesList s values ih
  | pair a b iha ihb =>
    show (Val.validIn s a && Val.validIn s b) =
      List.all (a.handles ++ b.handles) fun h => s.handleValid h.1 h.2
    rw [List.all_append, iha, ihb]
  | some a ih => exact ih
  | ctor _ args ih => exact Val.validInList_eq_handlesList s args ih

/-- A reified failed exit is valid everywhere: its cause writes no handle. -/
theorem Val.validIn_exitErr (s : Stores) (cause : CauseV) : Val.validIn s (Val.exitErr cause) = true := by
  rw [Val.validIn_eq_handles]
  show List.all (Store.Val.handles (.ctor 1 [causeImage.toVal cause])) _ = true
  rw [Store.Val.handles, Store.Val.handlesList_cons, causeImage_handleFree cause,
    Store.Val.handlesList_nil]
  rfl

/-- An operation's keys and argument values exist in the store (plan §3.1, ENSURES 12): the
`Ref` rows on the cell index and, where a value is written (`refMake`, `refSet`,
`refGetAndSet`, `refSetAndGet`; `Stores.lean:485-493`), on that value; the Deferred rows on
the cell index (`:1211-1224`); `deferredMake` and `scopeMake` unconditionally; `scopeAdd`,
`scopeRemove` and `scopeIsClosed` on the entry (`:1228-1234`). -/
def SyncOp.validIn (s : Stores) : SyncOp → Bool
  | SyncOp.refMake initial => initial.validIn s
  | SyncOp.refGet cell => cell.index < s.refs.length
  | SyncOp.refSet cell value => cell.index < s.refs.length && value.validIn s
  | SyncOp.refGetAndSet cell value => cell.index < s.refs.length && value.validIn s
  | SyncOp.refSetAndGet cell value => cell.index < s.refs.length && value.validIn s
  | SyncOp.refUpdate cell _ => cell.index < s.refs.length
  | SyncOp.refGetAndUpdate cell _ => cell.index < s.refs.length
  | SyncOp.refUpdateAndGet cell _ => cell.index < s.refs.length
  | SyncOp.refUpdateSome cell _ => cell.index < s.refs.length
  | SyncOp.refGetAndUpdateSome cell _ => cell.index < s.refs.length
  | SyncOp.refUpdateSomeAndGet cell _ => cell.index < s.refs.length
  | SyncOp.refModify cell _ => cell.index < s.refs.length
  | SyncOp.refModifySome cell _ => cell.index < s.refs.length
  | SyncOp.deferredMake => true
  | SyncOp.deferredIsDone cell => cell.index < s.deferreds.cells.length
  | SyncOp.deferredPoll cell => cell.index < s.deferreds.cells.length
  | SyncOp.deferredCompleteWith cell _ => cell.index < s.deferreds.cells.length
  | SyncOp.deferredInterruptWith cell _ => cell.index < s.deferreds.cells.length
  | SyncOp.deferredAwaitCleanup cell _ _ => cell.index < s.deferreds.cells.length
  | SyncOp.clockNow => true
  | SyncOp.sleepCancel _ _ => true
  | SyncOp.scopeMake _ => true
  | SyncOp.scopeAdd scope _ => (s.scopes.entryAt scope).isSome
  | SyncOp.scopeRemove scope _ => (s.scopes.entryAt scope).isSome
  | SyncOp.scopeIsClosed scope => (s.scopes.entryAt scope).isSome
  | SyncOp.scopeFork parent _ => (s.scopes.entryAt parent).isSome
  | SyncOp.memoFork none => true
  | SyncOp.memoFork (some parent) => (s.memo.mapAt parent).isSome
  | SyncOp.memoGet _ memoMap => (s.memo.mapAt memoMap).isSome
  | SyncOp.memoBuild _ memoMap => (s.memo.mapAt memoMap).isSome
  | SyncOp.memoComplete _ memoMap exit =>
    (s.memo.mapAt memoMap).isSome && (reifyExitVal exit).validIn s
  | SyncOp.memoRelease _ memoMap => (s.memo.mapAt memoMap).isSome

/-- Every memo entry's allocations exist: its Deferred cell and its layer scope (the join). -/
def Stores.MemoValid (s : Stores) : Prop :=
  ∀ m ∈ s.memo, ∀ e ∈ m.entries,
    e.2.deferred.index < s.deferreds.cells.length ∧
      (s.scopes.entryAt e.2.layerScope).isSome = true

instance (s : Stores) : Decidable s.MemoValid := by
  unfold Stores.MemoValid; infer_instance

/-- Every value the store holds and answers is valid in the store that holds it (plan §3.1,
ENSURES 12): the heap's values, and the closing exit of every closed scope — which
`scopeAdd` answers on a closed scope (`internal/effect.ts:3851-3853`; V1, 2026-09-07). Deferred
completions stay excluded: `STORES-FB-COMPLETION` in the header. -/
def Stores.WF (s : Stores) : Prop :=
  (∀ v ∈ s.refs, v.validIn s = true) ∧
    (∀ e ∈ s.scopes.entries,
      (e.scope.closingExit?.map fun exit => (reifyExitVal exit).validIn s).getD true = true) ∧
    s.MemoValid ∧ s.timers.WF

instance (s : Stores) : Decidable s.WF := by
  unfold Stores.WF; infer_instance

/-- `Stores.empty` (`Stores.lean:1043`) is well-formed: its heap, its scope store and its memo
world are empty (ENSURES 12; the bottom of every family's law). -/
theorem Stores.empty_wf : Stores.empty.WF :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), TimerStore.empty_wf⟩

/-- The closing exit a closed scope holds is valid in the store. -/
theorem Stores.WF.closingExit {s : Stores} (hwf : s.WF) {scope : Nat} {entry : ScopeEntry}
    {exit : ExitV} (hentry : s.scopes.entryAt scope = some entry)
    (hclose : entry.scope.closingExit? = some exit) : (reifyExitVal exit).validIn s = true := by
  have h := hwf.2.1 entry (List.mem_of_find?_eq_some hentry)
  rw [hclose] at h
  simpa only [Option.map, Option.getD] using h

/-- The four read-only operations of `syncOpStep`: `refGet` (`Stores.lean:486`),
`deferredIsDone` (`:1213`), `deferredPoll` (`:1215`), `scopeIsClosed` (`:1233`). The subject of
`syncOpStep_read_unchanged` (ENSURES 17). -/
def SyncOp.isRead : SyncOp → Bool
  | SyncOp.refGet _ => true
  | SyncOp.deferredIsDone _ => true
  | SyncOp.deferredPoll _ => true
  | SyncOp.scopeIsClosed _ => true
  | _ => false

/-! ## Monotonicity -/

/-- One handle's validity survives growth (plan §3.2, ENSURES 13): by its kind. -/
theorem Stores.handleValid_mono {s s' : Stores} (hle : s.le s') (kind : UInt8) (index : Nat)
    (h : s.handleValid kind index = true) : s'.handleValid kind index = true := by
  unfold Stores.handleValid at h ⊢
  generalize HandleKind.ofByte? kind = k at h ⊢
  cases k with
  | none => exact h
  | some k =>
    cases k with
    | fiber => rfl
    | cell => exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hle.1)
    | promise => exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hle.2.1)
    | scope => exact hle.2.2.1 index h
    | memoMap => exact hle.2.2.2.2 ⟨index⟩ h

/-- Validity survives growth (plan §3.2, ENSURES 13): every handle of the value does. -/
theorem Val.validIn_mono {s s' : Stores} (hle : s.le s') (v : Val) (h : v.validIn s = true) :
    v.validIn s' = true := by
  rw [Val.validIn_eq_handles, List.all_eq_true] at h ⊢
  exact fun x hx => Stores.handleValid_mono hle x.1 x.2 (h x hx)

/-- Validity of an operation survives growth (plan §3.2, ENSURES 13): cases. -/
theorem SyncOp.validIn_mono {s s' : Stores} (hle : s.le s') (o : SyncOp)
    (h : o.validIn s = true) : o.validIn s' = true := by
  cases o with
  | refMake initial => exact Val.validIn_mono hle initial h
  | clockNow | sleepCancel _ _ => rfl
  | refSet cell value | refGetAndSet cell value | refSetAndGet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 hle.1, Val.validIn_mono hle value h.2⟩
  | refGet cell | refUpdate cell _ | refGetAndUpdate cell _ | refUpdateAndGet cell _
  | refUpdateSome cell _ | refGetAndUpdateSome cell _ | refUpdateSomeAndGet cell _
  | refModify cell _ | refModifySome cell _ =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at h ⊢
    exact Nat.lt_of_lt_of_le h hle.1
  | deferredMake | scopeMake _ => rfl
  | deferredIsDone cell | deferredPoll cell | deferredCompleteWith cell _
  | deferredInterruptWith cell _ | deferredAwaitCleanup cell _ _ =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at h ⊢
    exact Nat.lt_of_lt_of_le h hle.2.1
  | scopeAdd scope _ | scopeRemove scope _ | scopeIsClosed scope | scopeFork scope _ =>
    exact hle.2.2.1 scope h
  | memoFork parent =>
    cases parent with
    | none => rfl
    | some parent => exact hle.2.2.2.2 parent h
  | memoGet _ memoMap | memoBuild _ memoMap | memoRelease _ memoMap => exact hle.2.2.2.2 memoMap h
  | memoComplete _ memoMap exit =>
    simp only [SyncOp.validIn, Bool.and_eq_true] at h ⊢
    exact ⟨hle.2.2.2.2 memoMap h.1, Val.validIn_mono hle _ h.2⟩

/-! ## The pure functions keep validity

`FnName.total` (`Stores.lean:458`) sends a `nat` to a `nat` and fixes everything else, so what
a read-modify-write row writes back is as valid as what it read. -/

/-- `total` preserves validity. -/
theorem FnName.total_validIn (s : Stores) (f : FnName) (a : Val) :
    (f.total a).validIn s = a.validIn s := by
  cases f <;> cases a <;> rfl

/-- `partialUpdate` (`Stores.lean:465`) preserves validity where it answers. -/
theorem FnName.partialUpdate_validIn (s : Stores) (f : FnName) (a a' : Val)
    (h : f.partialUpdate a = some a') : a'.validIn s = a.validIn s := by
  cases f with
  | noChange => simp [FnName.partialUpdate] at h
  | zeroWhenPositive =>
    cases a with
    | nat n =>
      cases n with
      | zero => simp [FnName.partialUpdate] at h
      | succ n =>
        simp only [FnName.partialUpdate, Option.some.injEq] at h
        subst h
        rfl
    | _ => simp [FnName.partialUpdate] at h
  | _ =>
    simp only [FnName.partialUpdate, Option.some.injEq] at h
    subst h
    exact FnName.total_validIn s _ a

/-- Both components of `modify` (`Stores.lean:472`) preserve validity. -/
theorem FnName.modify_validIn (s : Stores) (f : FnName) (a : Val) :
    (f.modify a).1.validIn s = a.validIn s ∧ (f.modify a).2.validIn s = a.validIn s := by
  cases f <;> cases a <;> exact ⟨rfl, rfl⟩

/-- Both components of `modifySome` (`Stores.lean:477`), the written one read through
`getD` as `refStep` does (`:521-523`), preserve validity. -/
theorem FnName.modifySome_validIn (s : Stores) (f : FnName) (a : Val) :
    (f.modifySome a).1.validIn s = a.validIn s ∧
      ((f.modifySome a).2.getD a).validIn s = a.validIn s := by
  cases f <;> cases a <;> exact ⟨rfl, rfl⟩

/-! ## The heap -/

/-- A key in range reads (`refPeek`, `Stores.lean:451`). -/
theorem refPeek_eq_some_of_lt (heap : RefHeap) (cell : RefKey) (h : cell.index < heap.length) :
    refPeek heap cell = some heap[cell.index] :=
  List.getElem?_eq_getElem h

/-- A key that reads is in range. -/
theorem lt_of_refPeek_eq_some {heap : RefHeap} {cell : RefKey} {a : Val}
    (h : refPeek heap cell = some a) : cell.index < heap.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- What a key reads is in the heap. -/
theorem mem_of_refPeek_eq_some {heap : RefHeap} {cell : RefKey} {a : Val}
    (h : refPeek heap cell = some a) : a ∈ heap :=
  List.mem_of_getElem? h

/-- The heap never shrinks under one `refStep` (plan §3.2, ENSURES 11): `refMake` appends
(`Stores.lean:485`), every other arm is `refPoke` (`:454`, `List.set`) or the heap itself. -/
theorem refStep_length (o : SyncOp) (heap : RefHeap) (v : Val) (heap' : RefHeap)
    (h : refStep o heap = some (v, heap')) : heap.length ≤ heap'.length := by
  cases o with
  | refMake initial =>
    simp only [refStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | refGet cell =>
    simp only [refStep] at h
    obtain ⟨a, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact Nat.le_refl _
  | refSet cell value | refGetAndSet cell value | refSetAndGet cell value
  | refUpdate cell f | refGetAndUpdate cell f | refUpdateAndGet cell f
  | refModify cell f | refModifySome cell f =>
    simp only [refStep] at h
    obtain ⟨a, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    simp [refPoke]
  | refUpdateSome cell pf | refGetAndUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    split <;> simp [refPoke]
  | refUpdateSomeAndGet cell pf =>
    simp only [refStep] at h
    obtain ⟨a, _, hf⟩ := Option.bind_eq_some_iff.mp h
    split at hf
    · obtain ⟨fresh, _, hff⟩ := Option.map_eq_some_iff.mp hf
      cases hff
      simp [refPoke]
    · cases hf
      exact Nat.le_refl _
  | _ => simp [refStep] at h

/-- Writing a valid value at a cell keeps every heap value valid in the store with the
written heap: `List.set` keeps the length, and a member of the written heap is a member of
the old one or the written value. -/
theorem refPoke_valid (s : Stores) (cell : RefKey) (y : Val) (hwf : s.WF)
    (hy : y.validIn s = true) :
    ∀ x ∈ refPoke s.refs cell y, x.validIn { s with refs := refPoke s.refs cell y } = true := by
  have hwf := hwf.1
  intro x hx
  have hle : s.le { s with refs := refPoke s.refs cell y } :=
    ⟨by simp [refPoke], Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h⟩
  apply Val.validIn_mono hle
  rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
  · exact hwf x hmem
  · exact hy

/-- The heap after a valid `refStep` on a well-formed heap is well-formed in the store that
carries it, and the answer is valid there: one arm per row of `refStep`
(`Stores.lean:484-525`). Heap writes store the argument value, `f.total a`, `f.modify`'s
second component, a `partialUpdate` answer, or a value already in the heap; answers are the
fresh cell, a heap value, the argument value, `unit`, or one of those images. -/
theorem refStep_valid (o : SyncOp) (s : Stores) (v : Val) (heap' : RefHeap) (hwf : s.WF)
    (hv : o.validIn s = true) (h : refStep o s.refs = some (v, heap')) :
    (∀ x ∈ heap', x.validIn { s with refs := heap' } = true) ∧
      v.validIn { s with refs := heap' } = true := by
  have hle : s.le { s with refs := heap' } :=
    ⟨refStep_length o s.refs v heap' h, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  have hwf' := hwf
  have hwf := hwf.1
  cases o with
  | refMake initial =>
    simp only [refStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun x hx => Val.validIn_mono hle x ?_, ?_⟩
    · rcases List.mem_append.mp hx with hmem | hone
      · exact hwf x hmem
      · rw [List.mem_singleton.mp hone]; exact hv
    · simp [Val.validIn_cell]
  | refGet cell =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨fun x hx => Val.validIn_mono hle x (hwf x hx),
      Val.validIn_mono hle a (hwf a (mem_of_refPeek_eq_some hpeek))⟩
  | refSet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine ⟨refPoke_valid s cell value hwf' hv.2, Val.validIn_mono hle _ ?_⟩
    simp only [Val.validIn_cell, decide_eq_true_eq]
    exact hv.1
  | refGetAndSet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨refPoke_valid s cell value hwf' hv.2,
      Val.validIn_mono hle a (hwf a (mem_of_refPeek_eq_some hpeek))⟩
  | refSetAndGet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨refPoke_valid s cell value hwf' hv.2, Val.validIn_mono hle value hv.2⟩
  | refUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf' ((FnName.total_validIn s f a).trans ha), rfl⟩
  | refGetAndUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf' ((FnName.total_validIn s f a).trans ha),
      Val.validIn_mono hle a ha⟩
  | refUpdateAndGet cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    have hfa : (f.total a).validIn s = true := (FnName.total_validIn s f a).trans ha
    exact ⟨refPoke_valid s cell _ hwf' hfa, Val.validIn_mono hle _ hfa⟩
  | refUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    refine ⟨?_, rfl⟩
    split
    · rename_i a' hpf
      exact refPoke_valid s cell a' hwf' ((FnName.partialUpdate_validIn s pf a a' hpf).trans ha)
    · exact fun x hx => hwf x hx
  | refGetAndUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    refine ⟨?_, Val.validIn_mono hle a ha⟩
    split
    · rename_i a' hpf
      exact refPoke_valid s cell a' hwf' ((FnName.partialUpdate_validIn s pf a a' hpf).trans ha)
    · exact fun x hx => hwf x hx
  | refUpdateSomeAndGet cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.bind_eq_some_iff.mp h
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    split at hf
    · rename_i a' hpf
      rw [refPeek_poke_self s.refs cell a' a hpeek] at hf
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have ha' : a'.validIn s = true := (FnName.partialUpdate_validIn s pf a a' hpf).trans ha
      exact ⟨refPoke_valid s cell a' hwf' ha', Val.validIn_mono hle a' ha'⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨fun x hx => Val.validIn_mono hle x (hwf x hx), Val.validIn_mono hle a ha⟩
  | refModify cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf' ((FnName.modify_validIn s f a).2.trans ha),
      Val.validIn_mono hle _ ((FnName.modify_validIn s f a).1.trans ha)⟩
  | refModifySome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf' ((FnName.modifySome_validIn s pf a).2.trans ha),
      Val.validIn_mono hle _ ((FnName.modifySome_validIn s pf a).1.trans ha)⟩
  | _ => simp [refStep] at h

/-! ## The Deferred and Scope stores -/

/-- `setCell` (`Stores.lean:708`) is `List.set`: the cell count is unchanged. -/
theorem DeferredStore.setCell_cells_length (self : DeferredStore) (cell : DeferredKey)
    (value : DeferredCell) : (self.setCell cell value).cells.length = self.cells.length :=
  List.length_set

/-- `complete` (`Stores.lean:742-751`) keeps the cell count: it answers the store itself or
one `setCell`. -/
theorem DeferredStore.complete_cells_length (self : DeferredStore) (cell : DeferredKey)
    (e : Program) : (self.complete cell e).1.cells.length = self.cells.length := by
  unfold DeferredStore.complete
  split
  · rfl
  · split
    · rfl
    · exact List.length_set

/-- `cancel` (`Stores.lean:732-738`) keeps the cell count. -/
theorem DeferredStore.cancel_cells_length (self : DeferredStore) (cell : DeferredKey)
    (waiter : FiberId) (token : Nat) :
    (self.cancel cell waiter token).cells.length = self.cells.length := by
  unfold DeferredStore.cancel
  split
  · rfl
  · exact List.length_set

/-- An entry exists under a key exactly when some entry carries that key
(`entryAt`, `Stores.lean:902`, is `List.find?`). -/
theorem ScopeStore.entryAt_isSome_iff (self : ScopeStore) (key : Nat) :
    (self.entryAt key).isSome = true ↔ ∃ e ∈ self.entries, e.key = key := by
  simp [ScopeStore.entryAt, List.find?_isSome]

/-- `make` (`Stores.lean:910`) appends: every entry survives. -/
theorem ScopeStore.entryAt_make_isSome (self : ScopeStore) (name : Nat)
    (strategy : FinalizerStrategy) (key : Nat) (h : (self.entryAt key).isSome = true) :
    ((self.make name strategy).entryAt key).isSome = true := by
  rw [ScopeStore.entryAt_isSome_iff] at h ⊢
  obtain ⟨e, he, hk⟩ := h
  exact ⟨e, List.mem_append_left _ he, hk⟩

/-- `make` (`Stores.lean:910`) appends the new key: it is present afterwards. -/
theorem ScopeStore.entryAt_make_self (self : ScopeStore) (name : Nat)
    (strategy : FinalizerStrategy) : ((self.make name strategy).entryAt name).isSome = true := by
  rw [ScopeStore.entryAt_isSome_iff]
  exact ⟨⟨name, Effect4.Scope.make strategy⟩,
    List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

/-- `setEntry` (`Stores.lean:906`) maps in place and keeps every key: every entry survives. -/
theorem ScopeStore.entryAt_setEntry_isSome (self : ScopeStore) (entry : ScopeEntry) (key : Nat)
    (h : (self.entryAt key).isSome = true) :
    ((self.setEntry entry).entryAt key).isSome = true := by
  rw [ScopeStore.entryAt_isSome_iff] at h ⊢
  obtain ⟨e, he, hk⟩ := h
  refine ⟨if e.key = entry.key then entry else e, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
  split
  · rename_i heq; rw [← heq]; exact hk
  · exact hk

/-- `addFinalizer` (`Stores.lean:915-921`, over `Scope.addExit`, `Scope.lean:613`) answers the
store itself or one `setEntry`: every entry survives. -/
theorem ScopeStore.entryAt_addFinalizer_isSome (self : ScopeStore) (scope finalizerKey : Nat)
    (fin : FinName) (key : Nat) (h : (self.entryAt key).isSome = true) :
    ((self.addFinalizer scope finalizerKey fin).1.entryAt key).isSome = true := by
  unfold ScopeStore.addFinalizer
  split
  · exact h
  · exact ScopeStore.entryAt_setEntry_isSome self _ key h

/-- `forkChild` (`Stores.lean`) sets the parent in place and appends the child: every entry
survives. -/
theorem ScopeStore.entryAt_forkChild_isSome (self : ScopeStore) (parent child shared : Nat)
    (strategy : FinalizerStrategy) (key : Nat) (h : (self.entryAt key).isSome = true) :
    ((self.forkChild parent child shared strategy).entryAt key).isSome = true := by
  unfold ScopeStore.forkChild
  cases hp : self.entryAt parent with
  | none => exact h
  | some p =>
    have h' := ScopeStore.entryAt_setEntry_isSome self
      { p with scope := (Effect4.Scope.fork p.scope strategy shared (FinName.closeChildScope child)
          (FinName.detachFromParent parent shared)).1 } key h
    rw [ScopeStore.entryAt_isSome_iff] at h' ⊢
    obtain ⟨e, he, hk⟩ := h'
    exact ⟨e, List.mem_append_left _ he, hk⟩

/-- `forkChild` appends the child's key: it is present afterwards. -/
theorem ScopeStore.entryAt_forkChild_child (self : ScopeStore) (parent child shared : Nat)
    (strategy : FinalizerStrategy) {p : ScopeEntry} (h : self.entryAt parent = some p) :
    ((self.forkChild parent child shared strategy).entryAt child).isSome = true := by
  simp only [ScopeStore.forkChild, h]
  rw [ScopeStore.entryAt_isSome_iff]
  exact ⟨⟨child, _⟩, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

/-- `removeFinalizer` (`Stores.lean:924-928`, over `Scope.removeUnsafe`, `Scope.lean:672`)
answers the store itself or one `setEntry`: every entry survives. -/
theorem ScopeStore.entryAt_removeFinalizer_isSome (self : ScopeStore) (scope finalizerKey : Nat)
    (key : Nat) (h : (self.entryAt key).isSome = true) :
    ((self.removeFinalizer scope finalizerKey).entryAt key).isSome = true := by
  unfold ScopeStore.removeFinalizer
  split
  · exact h
  · exact ScopeStore.entryAt_setEntry_isSome self _ key h

/-! ## The ten store arms of `syncOpStep`, as equations

`syncOpStep` (`Stores.lean:1209-1240`) destructures the pair a store operation answers with a
`let`; each equation below spells that arm with the projections, so a proof can rewrite it
without splitting the match. -/

/-- `Stores.lean:1210-1212`. -/
theorem syncOpStep_deferredMake (s : Stores) :
    syncOpStep SyncOp.deferredMake s =
      some ({ s with deferreds := s.deferreds.make.2 }, Val.promise s.deferreds.make.1) := rfl

/-- `Stores.lean:1213-1214`. -/
theorem syncOpStep_deferredIsDone (s : Stores) (cell : DeferredKey) :
    syncOpStep (SyncOp.deferredIsDone cell) s =
      (s.deferreds.isDone cell).map (fun flag => (s, Val.bool flag)) := rfl

/-- `Stores.lean:1215-1216`. -/
theorem syncOpStep_deferredPoll (s : Stores) (cell : DeferredKey) :
    syncOpStep (SyncOp.deferredPoll cell) s =
      (s.deferreds.poll cell).map (fun slot => (s, Val.bool slot.isSome)) := rfl

/-- `Stores.lean:1217-1219`. -/
theorem syncOpStep_deferredCompleteWith (s : Stores) (cell : DeferredKey)
    (c : Completion Val Err Defect FiberId Ann) :
    syncOpStep (SyncOp.deferredCompleteWith cell c) s =
      some ({ s with deferreds := (s.deferreds.complete cell (completionPrim c)).1 },
        Val.bool (s.deferreds.complete cell (completionPrim c)).2) := rfl

/-- `Stores.lean:1220-1224`. -/
theorem syncOpStep_deferredInterruptWith (s : Stores) (cell : DeferredKey)
    (interruptor : FiberId) :
    syncOpStep (SyncOp.deferredInterruptWith cell interruptor) s =
      some ({ s with deferreds :=
          (s.deferreds.complete cell
            (Prim.ofExit (Exit.failure (Cause.interrupt (some interruptor))))).1 },
        Val.bool (s.deferreds.complete cell
          (Prim.ofExit (Exit.failure (Cause.interrupt (some interruptor))))).2) := rfl

/-- `Stores.lean:1225-1226`. -/
theorem syncOpStep_deferredAwaitCleanup (s : Stores) (cell : DeferredKey) (waiter : FiberId)
    (token : Nat) :
    syncOpStep (SyncOp.deferredAwaitCleanup cell waiter token) s =
      some ({ s with deferreds := s.deferreds.cancel cell waiter token }, Val.unit) := rfl

/-- The clock read (the timer, A4). -/
theorem syncOpStep_clockNow (s : Stores) :
    syncOpStep SyncOp.clockNow s = some (s, Val.nat s.timers.now) := rfl

/-- `clearTimeout` (the timer, A4). -/
theorem syncOpStep_sleepCancel (s : Stores) (waiter : FiberId) (token : Nat) :
    syncOpStep (SyncOp.sleepCancel waiter token) s =
      some ({ s with timers := s.timers.cancel waiter token }, Val.unit) := rfl

/-- `Stores.lean:1227-1229`. -/
theorem syncOpStep_scopeMake (s : Stores) (strategy : FinalizerStrategy) :
    syncOpStep (SyncOp.scopeMake strategy) s =
      some ({ s with scopes := s.scopes.make s.nextName strategy, nextName := s.nextName + 1 },
        Val.scopeHandle s.nextName) := rfl

/-- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`) as the step spells it: an
unknown scope is a frontier, a closed scope answers its closing exit, an open one registers
under the supply's own value and advances the supply, so an identity allocated later cannot
collide with one this registration accepted (`E4-CHECK-CE-016`). The three branches are the
equations below. -/
theorem syncOpStep_scopeAdd (s : Stores) (scope : Nat) (fin : FinName) :
    syncOpStep (SyncOp.scopeAdd scope fin) s =
      match s.scopes.entryAt scope with
      | none => none
      | some entry =>
        match entry.scope.closingExit? with
        | some exit => some (s, reifyExitVal exit)
        | none =>
          some ({ s with
              scopes := s.scopes.setEntry { entry with scope := entry.scope.addUnsafe s.nextName fin }
              nextName := s.nextName + 1 },
            Val.unit) := rfl

/-- Unknown scope: the step is a frontier (M7). -/
theorem syncOpStep_scopeAdd_none (s : Stores) (scope : Nat) (fin : FinName)
    (h : s.scopes.entryAt scope = none) : syncOpStep (SyncOp.scopeAdd scope fin) s = none := by
  rw [syncOpStep_scopeAdd, h]

/-- Closed scope: the store is untouched and the closing exit is answered, reified
(`:3851-3853`); the caller runs the finalizer now. census: scope.add-after-closed -/
theorem syncOpStep_scopeAdd_closed (s : Stores) (scope : Nat) (fin : FinName)
    {entry : ScopeEntry} {exit : ExitV} (hentry : s.scopes.entryAt scope = some entry)
    (hclose : entry.scope.closingExit? = some exit) :
    syncOpStep (SyncOp.scopeAdd scope fin) s = some (s, reifyExitVal exit) := by
  rw [syncOpStep_scopeAdd, hentry]
  simp only [hclose]

/-- Open scope: registered under the supply's value, the supply one higher (`:3855-3856`).
census: scope.add-finalizer -/
theorem syncOpStep_scopeAdd_open (s : Stores) (scope : Nat) (fin : FinName)
    {entry : ScopeEntry} (hentry : s.scopes.entryAt scope = some entry)
    (hopen : entry.scope.closingExit? = none) :
    syncOpStep (SyncOp.scopeAdd scope fin) s =
      some ({ s with
          scopes := s.scopes.setEntry { entry with scope := entry.scope.addUnsafe s.nextName fin }
          nextName := s.nextName + 1 },
        Val.unit) := by
  rw [syncOpStep_scopeAdd, hentry]
  simp only [hopen]

/-- `Stores.lean:1233-1234`. -/
theorem syncOpStep_scopeRemove (s : Stores) (scope key : Nat) :
    syncOpStep (SyncOp.scopeRemove scope key) s =
      some ({ s with scopes := s.scopes.removeFinalizer scope key }, Val.unit) := rfl

/-- `Stores.lean:1235-1236`. -/
theorem syncOpStep_scopeIsClosed (s : Stores) (scope : Nat) :
    syncOpStep (SyncOp.scopeIsClosed scope) s =
      (s.scopes.entryAt scope).map (fun entry => (s, Val.bool entry.scope.isClosed)) := rfl

/-! ### The six arms of the join (`Layer.ts:396-458`, `internal/effect.ts:3834-3844`) -/

/-- `scopeForkUnsafe` on an unknown parent: a frontier. -/
theorem syncOpStep_scopeFork_none (s : Stores) (parent : Nat) (strategy : FinalizerStrategy)
    (h : s.scopes.entryAt parent = none) :
    syncOpStep (SyncOp.scopeFork parent strategy) s = none := by
  simp only [syncOpStep, h]

/-- `scopeForkUnsafe` on a known parent: the child at the supply, the shared key next, the supply
past both. census: scope.fork-linkage -/
theorem syncOpStep_scopeFork_some (s : Stores) (parent : Nat) (strategy : FinalizerStrategy)
    {entry : ScopeEntry} (h : s.scopes.entryAt parent = some entry) :
    syncOpStep (SyncOp.scopeFork parent strategy) s =
      some ({ s with
          scopes := s.scopes.forkChild parent s.nextName (s.nextName + 1) strategy
          nextName := s.nextName + 2 },
        Val.scopeHandle s.nextName) := by
  simp only [syncOpStep, h]

theorem syncOpStep_memoFork (s : Stores) (parent : Option MemoMapId) :
    syncOpStep (SyncOp.memoFork parent) s =
      some ({ s with memo := s.memo ++ [⟨⟨s.nextName⟩, parent, []⟩], nextName := s.nextName + 1 },
        Val.memoMap ⟨s.nextName⟩) := rfl

theorem syncOpStep_memoGet_none (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (h : s.memo.get layer memoMap = none) :
    syncOpStep (SyncOp.memoGet layer memoMap) s = some (s, Val.unit) := by
  simp only [syncOpStep, h]

/-- A hit bumps the owning entry's observers and answers its Deferred and owner
(`Layer.ts:245`, `:438-442`). census: layer.memo-get -/
theorem syncOpStep_memoGet_some (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    {owner : MemoMapId} {entry : MemoEntry} (h : s.memo.get layer memoMap = some (owner, entry)) :
    syncOpStep (SyncOp.memoGet layer memoMap) s =
      some ({ s with
          memo := s.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 } },
        Val.pair (Val.promise entry.deferred) (Val.memoMap owner)) := by
  simp only [syncOpStep, h]

/-- `memoMapBuild`'s synchronous half (`Layer.ts:396-411`): the layer scope at the supply, a
fresh Deferred, the entry with one observer. census: layer.memo-build-once -/
theorem syncOpStep_memoBuild (s : Stores) (layer : LayerId) (memoMap : MemoMapId) :
    syncOpStep (SyncOp.memoBuild layer memoMap) s =
      some ({ s with
          scopes := s.scopes.make s.nextName FinalizerStrategy.sequential
          deferreds := s.deferreds.make.2
          memo := s.memo.insertEntry memoMap layer
            ⟨1, Prim.async (Name.registerAwait s.deferreds.make.1) true
                (some (Name.cancelAwait s.deferreds.make.1)),
              s.nextName, s.deferreds.make.1, FinName.memoEntry layer memoMap⟩
          nextName := s.nextName + 1 },
        Val.scopeHandle s.nextName) := rfl

theorem syncOpStep_memoComplete_none (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (exit : ExitV) (h : s.memo.entryAt memoMap layer = none) :
    syncOpStep (SyncOp.memoComplete layer memoMap exit) s = some (s, Val.unit) := by
  simp only [syncOpStep, h]

/-- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`): the exit stored, the Deferred completed —
the wakeup borrowed from the Deferred family. census: layer.memo-build-once -/
theorem syncOpStep_memoComplete_some (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (exit : ExitV) {entry : MemoEntry} (h : s.memo.entryAt memoMap layer = some entry) :
    syncOpStep (SyncOp.memoComplete layer memoMap exit) s =
      some ({ s with
          memo := s.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit }
          deferreds := (s.deferreds.complete entry.deferred (Prim.ofExit exit)).1 },
        Val.unit) := by
  simp only [syncOpStep, h]

theorem syncOpStep_memoRelease_none (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (h : s.memo.entryAt memoMap layer = none) :
    syncOpStep (SyncOp.memoRelease layer memoMap) s = some (s, Val.unit) := by
  simp only [syncOpStep, h]

/-- The last observer's release deletes the entry and answers the layer scope (`Layer.ts:403-406`).
census: layer.memo-release -/
theorem syncOpStep_memoRelease_last (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    {entry : MemoEntry} (h : s.memo.entryAt memoMap layer = some entry)
    (hobs : entry.observers ≤ 1) :
    syncOpStep (SyncOp.memoRelease layer memoMap) s =
      some ({ s with memo := s.memo.deleteEntry memoMap layer }, Val.scopeHandle entry.layerScope) := by
  simp only [syncOpStep, h, hobs, ite_true]

/-- Any other release decrements (`:408`). census: layer.memo-release -/
theorem syncOpStep_memoRelease_dec (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    {entry : MemoEntry} (h : s.memo.entryAt memoMap layer = some entry)
    (hobs : ¬ entry.observers ≤ 1) :
    syncOpStep (SyncOp.memoRelease layer memoMap) s =
      some ({ s with
          memo := s.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 } },
        Val.unit) := by
  simp only [syncOpStep, h, hobs, ite_false]

/-- `memoGet` is a read of every family but `memo` (the Layer machine's
`memoGet_rebuilds_nothing`, restated on the joined store in a stronger spelling). -/
theorem syncOpStep_memoGet_families (s s' : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (v : Val) (h : syncOpStep (SyncOp.memoGet layer memoMap) s = some (s', v)) :
    s'.refs = s.refs ∧ s'.deferreds = s.deferreds ∧ s'.scopes = s.scopes ∧
      s'.nextName = s.nextName := by
  cases hget : s.memo.get layer memoMap with
  | none =>
    rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  | some p =>
    obtain ⟨owner, entry⟩ := p
    rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### The join's finalizer names, as programs (`Layer.ts:343`, `:401-417`)

The program a finalizer name runs and the store continuation `closeIfLast` reads, one `rfl`
each: the compile route's witnesses for the layer rows of the census
(`Test/Audit/RuntimeCoverage.lean`, the join). -/

/-- `fromBuild`'s child scope closes only when the build failed (`Layer.ts:343`).
census: layer.from-build-child-scope -/
theorem finProgram_closeChildOnFailure_failure (scope : Nat) (cause : CauseV) :
    finProgram (FinName.closeChildOnFailure scope) (Exit.failure cause) =
      Prim.withFiber (Thunk.act (ActionName.closeScope scope (Exit.failure cause))) := rfl

/-- A successful build leaves its child scope, and its finalizers, attached to the caller scope.
census: layer.from-build-child-scope -/
theorem finProgram_closeChildOnFailure_success (scope : Nat) (v : Val) :
    finProgram (FinName.closeChildOnFailure scope) (Exit.success v) = Prim.success Val.unit := rfl

/-- The memo entry finalizer: `memoRelease`, then `closeIfLast` on its answer (`:401-410`).
census: layer.memo-finalizer-last-observer -/
theorem finProgram_memoEntry (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV) :
    finProgram (FinName.memoEntry layer memoMap) exit =
      Prim.onSuccess (Prim.sync (Thunk.op (SyncOp.memoRelease layer memoMap)))
        (Name.closeIfLast exit) := rfl

/-- `memoMapBuild`'s `onExit` (`:414-417`): the exit stored and the Deferred completed.
census: layer.memo-build-once -/
theorem finProgram_memoDone (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV) :
    finProgram (FinName.memoDone layer memoMap) exit =
      Prim.sync (Thunk.op (SyncOp.memoComplete layer memoMap exit)) := rfl

/-- The last observer's release answered the layer scope: closed with the closing exit (`:406`);
`contAOf_closeIfLast_other` (`Program/Intro.lean`) is the other answer, void (`:408`).
census: layer.memo-finalizer-last-observer -/
theorem contAOf_closeIfLast_scope (exit : ExitV) (scope : Nat) :
    contAOf (Name.closeIfLast exit) (Val.scopeHandle scope) =
      Prim.withFiber (Thunk.act (ActionName.closeScope scope exit)) := rfl

/-! ## The laws of `syncOpStep` -/

/-- A step grows the store (plan §3.2, ENSURES 11): one case per arm of `syncOpStep`. -/
theorem syncOpStep_le (o : SyncOp) (s s' : Stores) (v : Val) (h : syncOpStep o s = some (s', v)) :
    s.le s' := by
  cases o with
  | deferredMake =>
    simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, by simp [DeferredStore.make], fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact Stores.le_refl s
  | deferredCompleteWith cell c =>
    simp only [syncOpStep_deferredCompleteWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.complete_cells_length _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  | deferredInterruptWith cell interruptor =>
    simp only [syncOpStep_deferredInterruptWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.complete_cells_length _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  | deferredAwaitCleanup cell waiter token =>
    simp only [syncOpStep_deferredAwaitCleanup, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.cancel_cells_length _ _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun key hk => ScopeStore.entryAt_make_isSome _ _ _ key hk, Nat.le_succ _, fun _ hm => hm⟩
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact Stores.le_refl s
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨Nat.le_refl _, Nat.le_refl _,
          fun k hk => ScopeStore.entryAt_setEntry_isSome _ _ k hk, Nat.le_succ _, fun _ hm => hm⟩
  | scopeRemove scope key =>
    simp only [syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun k hk => ScopeStore.entryAt_removeFinalizer_isSome _ _ _ k hk, Nat.le_refl _, fun _ hm => hm⟩
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨Nat.le_refl _, Nat.le_refl _,
        fun k hk => ScopeStore.entryAt_forkChild_isSome _ _ _ _ _ k hk, Nat.le_add_right _ _,
        fun _ hm => hm⟩
  | memoFork parent =>
    simp only [syncOpStep_memoFork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_succ _, fun id hm => by
      show ((s.memo ++ [(⟨⟨s.nextName⟩, parent, []⟩ : MemoMap)]).mapAt id).isSome = true
      exact MemoWorld.mapAt_append_isSome hm⟩
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none =>
      rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact Stores.le_refl s
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, fun id hm => by
        show ((s.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 }).mapAt
          id).isSome = true
        exact MemoWorld.mapAt_updateEntry_isSome hm⟩
  | memoBuild layer memoMap =>
    simp only [syncOpStep_memoBuild, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, by simp [DeferredStore.make],
      fun k hk => ScopeStore.entryAt_make_isSome _ _ _ k hk, Nat.le_succ _, fun id hm => by
        show ((s.memo.insertEntry memoMap layer _).mapAt id).isSome = true
        exact MemoWorld.mapAt_insertEntry_isSome hm⟩
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact Stores.le_refl s
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.complete_cells_length _ _ _).symm,
        fun _ hk => hk, Nat.le_refl _, fun id hm => by
          show ((s.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit }).mapAt
            id).isSome = true
          exact MemoWorld.mapAt_updateEntry_isSome hm⟩
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact Stores.le_refl s
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, fun id hm => by
          show ((s.memo.deleteEntry memoMap layer).mapAt id).isSome = true
          exact MemoWorld.mapAt_deleteEntry_isSome hm⟩
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, fun id hm => by
          show ((s.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 }).mapAt
            id).isSome = true
          exact MemoWorld.mapAt_updateEntry_isSome hm⟩
  | clockNow =>
    simp only [syncOpStep_clockNow, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Stores.le_refl s
  | sleepCancel waiter token =>
    simp only [syncOpStep_sleepCancel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, fun _ hm => hm⟩
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact ⟨refStep_length _ s.refs a heap' hstep, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _,
      fun _ hm => hm⟩

/-- A step keeps every closing exit the store held: a closed scope's exit is answered, never
rewritten; an open registration goes under `addUnsafe`; the heap and Deferred arms leave the
scope store as it is. -/
theorem syncOpStep_closingExit (o : SyncOp) (s s' : Stores) (v : Val)
    (h : syncOpStep o s = some (s', v)) :
    ∀ e ∈ s'.scopes.entries, ∀ exit, e.scope.closingExit? = some exit →
      ∃ e₀ ∈ s.scopes.entries, e₀.scope.closingExit? = some exit := by
  cases o with
  | deferredMake =>
    simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun e he exit hc => ⟨e, he, hc⟩
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact fun e he exit hc => ⟨e, he, hc⟩
  | deferredCompleteWith _ _ | deferredInterruptWith _ _ | deferredAwaitCleanup _ _ _ =>
    simp only [syncOpStep_deferredCompleteWith, syncOpStep_deferredInterruptWith,
      syncOpStep_deferredAwaitCleanup, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun e he exit hc => ⟨e, he, hc⟩
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro e he exit hc
    simp only [ScopeStore.make, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ⟨e, he, hc⟩
    · exact nomatch hc
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact fun e he exit hc => ⟨e, he, hc⟩
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        intro e he exit hc
        rcases ScopeStore.mem_setEntry he with rfl | he
        · rw [Scope.closingExit_addUnsafe] at hc
          exact ⟨entry, List.mem_of_find?_eq_some hentry, hc⟩
        · exact ⟨e, he, hc⟩
  | scopeRemove scope key =>
    simp only [syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro e he exit hc
    simp only [ScopeStore.removeFinalizer] at he
    split at he
    · exact ⟨e, he, hc⟩
    · next entry hentry =>
      rcases ScopeStore.mem_setEntry he with rfl | he
      · rw [Scope.closingExit_removeUnsafe] at hc
        exact ⟨entry, List.mem_of_find?_eq_some hentry, hc⟩
      · exact ⟨e, he, hc⟩
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      intro e he exit hc
      simp only [ScopeStore.forkChild, hentry] at he
      cases hclose : entry.scope.closingExit? with
      | some ex =>
        simp only [Effect4.Scope.fork, hclose, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · rcases ScopeStore.mem_setEntry he with rfl | he
          · exact ⟨entry, List.mem_of_find?_eq_some hentry, hc⟩
          · exact ⟨e, he, hc⟩
        · refine ⟨entry, List.mem_of_find?_eq_some hentry, ?_⟩
          rw [hclose]
          exact hc
      | none =>
        simp only [Effect4.Scope.fork, hclose, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · rcases ScopeStore.mem_setEntry he with rfl | he
          · rw [Scope.closingExit_addUnsafe, hclose] at hc
            exact nomatch hc
          · exact ⟨e, he, hc⟩
        · rw [Scope.closingExit_addUnsafe] at hc
          exact nomatch hc
  | memoFork parent =>
    simp only [syncOpStep_memoFork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun e he exit hc => ⟨e, he, hc⟩
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none =>
      rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun e he exit hc => ⟨e, he, hc⟩
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun e he exit hc => ⟨e, he, hc⟩
  | memoBuild layer memoMap =>
    simp only [syncOpStep_memoBuild, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro e he exit hc
    simp only [ScopeStore.make, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ⟨e, he, hc⟩
    · exact nomatch hc
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun e he exit hc => ⟨e, he, hc⟩
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun e he exit hc => ⟨e, he, hc⟩
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun e he exit hc => ⟨e, he, hc⟩
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact fun e he exit hc => ⟨e, he, hc⟩
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact fun e he exit hc => ⟨e, he, hc⟩
  | clockNow | sleepCancel _ _ =>
    simp only [syncOpStep_clockNow, syncOpStep_sleepCancel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun e he exit hc => ⟨e, he, hc⟩
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact fun e he exit hc => ⟨e, he, hc⟩

/-- The closing exits stay valid across a step: each one is one the old store held, and
validity is monotone along `le`. -/
theorem syncOpStep_closingValid (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.WF)
    (h : syncOpStep o s = some (s', v)) :
    ∀ e ∈ s'.scopes.entries,
      (e.scope.closingExit?.map fun exit => (reifyExitVal exit).validIn s').getD true = true := by
  have hle := syncOpStep_le o s s' v h
  intro e he
  cases hc : e.scope.closingExit? with
  | none => rfl
  | some exit =>
    obtain ⟨e₀, he₀, hc₀⟩ := syncOpStep_closingExit o s s' v h e he exit hc
    have h₀ := hwf.2.1 e₀ he₀
    rw [hc₀] at h₀
    simp only [Option.map, Option.getD] at h₀ ⊢
    exact Val.validIn_mono hle _ h₀

/-- A valid operation steps (plan §3.2, ENSURES 14): every `none` of `syncOpStep` and
`refStep` is a failed lookup, and validity is the lookup's success; `refUpdateSomeAndGet`
re-reads after a `refPoke`, which keeps the length (`refPeek_poke_self`, `Stores.lean`). -/
theorem syncOpStep_isSome_of_valid (o : SyncOp) (s : Stores) (hv : o.validIn s = true) :
    (syncOpStep o s).isSome = true := by
  cases o with
  | refMake initial => rfl
  | clockNow | sleepCancel _ _ => rfl
  | refGet cell | refUpdate cell _ | refGetAndUpdate cell _ | refUpdateAndGet cell _
  | refUpdateSome cell _ | refGetAndUpdateSome cell _ | refModify cell _ | refModifySome cell _ =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at hv
    simp [syncOpStep, refStep, refPeek_eq_some_of_lt s.refs cell hv]
  | refSet cell value | refGetAndSet cell value | refSetAndGet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [syncOpStep, refStep, refPeek_eq_some_of_lt s.refs cell hv.1]
  | refUpdateSomeAndGet cell pf =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at hv
    have hpeek := refPeek_eq_some_of_lt s.refs cell hv
    simp only [syncOpStep, refStep, hpeek, Option.isSome_map, Option.bind_some]
    split
    · rename_i a' _
      simp [refPeek_poke_self s.refs cell a' _ hpeek]
    · rfl
  | deferredMake => rfl
  | deferredIsDone cell =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at hv
    simp [syncOpStep_deferredIsDone, DeferredStore.isDone, DeferredStore.cellAt,
      List.getElem?_eq_getElem hv]
  | deferredPoll cell =>
    simp only [SyncOp.validIn, decide_eq_true_eq] at hv
    simp [syncOpStep_deferredPoll, DeferredStore.poll, DeferredStore.cellAt,
      List.getElem?_eq_getElem hv]
  | deferredCompleteWith cell c => rfl
  | deferredInterruptWith cell interruptor => rfl
  | deferredAwaitCleanup cell waiter token => rfl
  | scopeMake strategy => rfl
  | scopeAdd scope fin =>
    simp only [SyncOp.validIn] at hv
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hv
    cases hclose : entry.scope.closingExit? with
    | some exit => rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose]; rfl
    | none => rw [syncOpStep_scopeAdd_open s scope fin hentry hclose]; rfl
  | scopeRemove scope key => rfl
  | scopeIsClosed scope =>
    simp only [SyncOp.validIn] at hv
    simp [syncOpStep_scopeIsClosed, hv]
  | scopeFork parent strategy =>
    simp only [SyncOp.validIn] at hv
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hv
    rw [syncOpStep_scopeFork_some s parent strategy hentry]
    rfl
  | memoFork parent => rfl
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none => rw [syncOpStep_memoGet_none s layer memoMap hget]; rfl
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget]
      rfl
  | memoBuild layer memoMap => rfl
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none => rw [syncOpStep_memoComplete_none s layer memoMap exit hentry]; rfl
    | some entry => rw [syncOpStep_memoComplete_some s layer memoMap exit hentry]; rfl
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none => rw [syncOpStep_memoRelease_none s layer memoMap hentry]; rfl
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs]; rfl
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs]; rfl

/-- A memo entry's allocations exist after a step (the join): the old entries by growth, a
built entry by its own allocations, the world otherwise unchanged. -/
theorem syncOpStep_memoValid (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.WF)
    (h : syncOpStep o s = some (s', v)) : s'.MemoValid := by
  have hle := syncOpStep_le o s s' v h
  have hsame : ∀ {t : Stores}, t.memo = s.memo → s.le t → t.MemoValid := by
    intro t ht hlt m hm e he
    rw [ht] at hm
    obtain ⟨hd, hs⟩ := hwf.2.2.1 m hm e he
    exact ⟨Nat.lt_of_lt_of_le hd hlt.2.1, hlt.2.2.1 _ hs⟩
  cases o with
  | memoFork parent =>
    simp only [syncOpStep_memoFork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro m hm e he
    rcases List.mem_append.mp hm with hm | hm
    · exact hwf.2.2.1 m hm e he
    · rw [List.mem_singleton] at hm
      subst hm
      exact nomatch he
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none =>
      rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf.2.2.1
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      intro m hm e he
      have hm' : m ∈ s.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 } :=
        hm
      obtain ⟨m₀, hm₀, e₀, he₀, heq⟩ := MemoWorld.mem_updateEntry_entries hm' he
      obtain ⟨hd, hs⟩ := hwf.2.2.1 m₀ hm₀ e₀ he₀
      rcases heq with rfl | rfl
      · exact ⟨hd, hs⟩
      · exact ⟨hd, hs⟩
  | memoBuild layer memoMap =>
    simp only [syncOpStep_memoBuild, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro m hm e he
    have hm' : m ∈ s.memo.insertEntry memoMap layer _ := hm
    rcases MemoWorld.mem_insertEntry_entries hm' he with ⟨m₀, hm₀, he₀⟩ | rfl
    · obtain ⟨hd, hs⟩ := hwf.2.2.1 m₀ hm₀ e he₀
      exact ⟨Nat.lt_of_lt_of_le hd hle.2.1, hle.2.2.1 _ hs⟩
    · exact ⟨by simp [DeferredStore.make], ScopeStore.entryAt_make_self _ _ _⟩
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf.2.2.1
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      intro m hm e he
      have hm' : m ∈ s.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit } :=
        hm
      obtain ⟨m₀, hm₀, e₀, he₀, heq⟩ := MemoWorld.mem_updateEntry_entries hm' he
      obtain ⟨hd, hs⟩ := hwf.2.2.1 m₀ hm₀ e₀ he₀
      rcases heq with rfl | rfl
      · exact ⟨Nat.lt_of_lt_of_le hd hle.2.1, hs⟩
      · exact ⟨Nat.lt_of_lt_of_le hd hle.2.1, hs⟩
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf.2.2.1
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        intro m hm e he
        have hm' : m ∈ s.memo.deleteEntry memoMap layer := hm
        obtain ⟨m₀, hm₀, he₀⟩ := MemoWorld.mem_deleteEntry_entries hm' he
        exact hwf.2.2.1 m₀ hm₀ e he₀
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        intro m hm e he
        have hm' : m ∈ s.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 } :=
          hm
        obtain ⟨m₀, hm₀, e₀, he₀, heq⟩ := MemoWorld.mem_updateEntry_entries hm' he
        obtain ⟨hd, hs⟩ := hwf.2.2.1 m₀ hm₀ e₀ he₀
        rcases heq with rfl | rfl
        · exact ⟨hd, hs⟩
        · exact ⟨hd, hs⟩
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hsame rfl hle
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | scopeMake _ | scopeRemove _ _ =>
    simp only [syncOpStep_deferredMake, syncOpStep_deferredCompleteWith,
      syncOpStep_deferredInterruptWith, syncOpStep_deferredAwaitCleanup, syncOpStep_scopeMake,
      syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hsame rfl hle
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hsame rfl hle
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hsame rfl hle
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hsame rfl hle
  | clockNow | sleepCancel _ _ =>
    simp only [syncOpStep_clockNow, syncOpStep_sleepCancel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hsame rfl hle
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hsame rfl hle

/-- The timer's law across a step (the timer, A4): only `sleepCancel` touches the timer store,
and a cancel keeps every remaining deadline ahead of the clock. -/
theorem syncOpStep_timers_wf (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.timers.WF)
    (h : syncOpStep o s = some (s', v)) : s'.timers.WF := by
  cases o with
  | sleepCancel waiter token =>
    simp only [syncOpStep_sleepCancel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact TimerStore.cancel_wf hwf waiter token
  | clockNow =>
    simp only [syncOpStep_clockNow, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hwf
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | scopeMake _ | scopeRemove _ _ | memoFork _ | memoBuild _ _ =>
    simp only [syncOpStep_deferredMake, syncOpStep_deferredCompleteWith,
      syncOpStep_deferredInterruptWith, syncOpStep_deferredAwaitCleanup, syncOpStep_scopeMake,
      syncOpStep_scopeRemove, syncOpStep_memoFork, syncOpStep_memoBuild,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hwf
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hwf
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hwf
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hwf
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none =>
      rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hwf
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hwf
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hwf

/-- A valid step from a well-formed store reaches a well-formed store (plan §3.2,
ENSURES 15): the heap arms by `refStep_valid`, the store arms by growth alone, since they
leave the heap untouched; the closing exits by `syncOpStep_closingValid`. -/
theorem syncOpStep_wf (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.WF)
    (hv : o.validIn s = true) (h : syncOpStep o s = some (s', v)) : s'.WF := by
  have hle := syncOpStep_le o s s' v h
  refine ⟨?_, syncOpStep_closingValid o s s' v hwf h, syncOpStep_memoValid o s s' v hwf h,
    syncOpStep_timers_wf o s s' v hwf.2.2.2 h⟩
  cases o with
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | scopeMake _ | scopeRemove _ _ | clockNow | sleepCancel _ _ =>
    simp only [syncOpStep_deferredMake, syncOpStep_deferredCompleteWith,
      syncOpStep_deferredInterruptWith, syncOpStep_deferredAwaitCleanup, syncOpStep_scopeMake,
      syncOpStep_scopeRemove, syncOpStep_clockNow, syncOpStep_sleepCancel,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro x hx
    exact Val.validIn_mono hle x (hwf.1 x hx)
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hwf.1
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        intro x hx
        exact Val.validIn_mono hle x (hwf.1 x hx)
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hwf.1
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | memoFork parent =>
    simp only [syncOpStep_memoFork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | memoGet layer memoMap =>
    obtain ⟨hrefs, _, _, _⟩ := syncOpStep_memoGet_families s s' layer memoMap v h
    rw [hrefs]
    exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | memoBuild layer memoMap =>
    simp only [syncOpStep_memoBuild, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf.1
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hwf.1
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact fun x hx => Val.validIn_mono hle x (hwf.1 x hx)
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact (refStep_valid _ s a heap' hwf hv hstep).1

/-- A valid step from a well-formed store answers a valid value (plan §3.2, ENSURES 16):
`refMake` answers the fresh cell, reads answer heap values, `deferredMake` the new index,
`scopeMake` the name it appends, the rest a scalar. -/
theorem syncOpStep_answer_valid (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.WF)
    (hv : o.validIn s = true) (h : syncOpStep o s = some (s', v)) : v.validIn s' = true := by
  cases o with
  | deferredMake =>
    simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Val.validIn_promise, DeferredStore.make]
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    rfl
  | deferredCompleteWith _ _ | deferredInterruptWith _ _ | deferredAwaitCleanup _ _ _
  | scopeRemove _ _ =>
    simp only [syncOpStep_deferredCompleteWith, syncOpStep_deferredInterruptWith,
      syncOpStep_deferredAwaitCleanup, syncOpStep_scopeRemove,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | scopeAdd scope fin =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope fin hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        -- the closing exit the store answers is one it holds, valid by `WF`
        rw [syncOpStep_scopeAdd_closed s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hwf.closingExit hentry hclose
      | none =>
        rw [syncOpStep_scopeAdd_open s scope fin hentry hclose, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ScopeStore.entryAt_make_self s.scopes s.nextName strategy
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ScopeStore.entryAt_forkChild_child s.scopes parent s.nextName (s.nextName + 1)
        strategy hentry
  | memoFork parent =>
    simp only [syncOpStep_memoFork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact MemoWorld.mapAt_append_self s.memo ⟨⟨s.nextName⟩, parent, []⟩
  | memoGet layer memoMap =>
    cases hget : s.memo.get layer memoMap with
    | none =>
      rw [syncOpStep_memoGet_none s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | some p =>
      obtain ⟨owner, entry⟩ := p
      rw [syncOpStep_memoGet_some s layer memoMap hget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m, hm, hid, hmem⟩ := MemoWorld.get_mem hget
      obtain ⟨hd, _⟩ := hwf.2.2.1 m hm _ hmem
      show (Val.validIn _ (Val.promise entry.deferred) && Val.validIn _ (Val.memoMap owner)) = true
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true hd, ?_⟩
      rw [Val.validIn_memoMap]
      show ((s.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 }).mapAt
        owner).isSome = true
      exact MemoWorld.mapAt_updateEntry_isSome (hid ▸ MemoWorld.mapAt_isSome_of_mem hm)
  | memoBuild layer memoMap =>
    simp only [syncOpStep_memoBuild, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ScopeStore.entryAt_make_self s.scopes s.nextName FinalizerStrategy.sequential
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m, hm, _, hmem⟩ := MemoWorld.entryAt_mem hentry
        exact (hwf.2.2.1 m hm _ hmem).2
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  | clockNow | sleepCancel _ _ =>
    simp only [syncOpStep_clockNow, syncOpStep_sleepCancel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact (refStep_valid _ s a heap' hwf hv hstep).2

/-- A read leaves the store as it was (plan §3.2, ENSURES 17): `refGet`, `deferredIsDone`,
`deferredPoll` and `scopeIsClosed` (`SyncOp.isRead`) thread the store through unchanged. -/
theorem syncOpStep_read_unchanged (o : SyncOp) (s s' : Stores) (v : Val)
    (hread : o.isRead = true) (h : syncOpStep o s = some (s', v)) : s' = s := by
  cases o with
  | refGet cell =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    simp only [refStep] at hstep
    obtain ⟨b, _, hb⟩ := Option.map_eq_some_iff.mp hstep
    cases hb
    rfl
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    rfl
  | _ => simp [SyncOp.isRead] at hread

end Effect4.Machine
