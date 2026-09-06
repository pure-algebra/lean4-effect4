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
  them (`Stores.lean:155-158`).
* `Val.exitErr` carries a cause and no handle; it is valid everywhere.
* `ScopeStore.forkChild` (`Stores.lean:932`) is not reachable from `syncOpStep` and has no
  law here.

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
  s.nextName ≤ s'.nextName

/-- Reflexive (ENSURES 10). -/
theorem Stores.le_refl (s : Stores) : s.le s :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩

/-- Transitive (ENSURES 10). -/
theorem Stores.le_trans {s s' s'' : Stores} (h : s.le s') (h' : s'.le s'') : s.le s'' :=
  ⟨Nat.le_trans h.1 h'.1, Nat.le_trans h.2.1 h'.2.1,
    fun key hk => h'.2.2.1 key (h.2.2.1 key hk), Nat.le_trans h.2.2.2 h'.2.2.2⟩

/-! ## Validity -/

/-- A value's handles exist in the store (plan §3.1, ENSURES 12): a `Val.cell` names a heap
index (`Stores.lean:160`, `refPeek` at `:451`), a `Val.promise` a Deferred cell index
(`:162`, `cellAt` at `:704`), a `Val.scopeHandle` a scope entry (`:164`, `entryAt` at `:902`);
a reified exit and the list cells are valid when their parts are. Fibers are the machine's,
not the store's. -/
def Val.validIn (s : Stores) : Val → Bool
  | Val.cell k => k.index < s.refs.length
  | Val.promise k => k.index < s.deferreds.cells.length
  | Val.scopeHandle key => (s.scopes.entryAt key).isSome
  | Val.exitOk v => Val.validIn s v
  | Val.exitCons h t => Val.validIn s h && Val.validIn s t
  | _ => true

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
  | SyncOp.scopeMake _ => true
  | SyncOp.scopeAdd scope _ _ => (s.scopes.entryAt scope).isSome
  | SyncOp.scopeRemove scope _ => (s.scopes.entryAt scope).isSome
  | SyncOp.scopeIsClosed scope => (s.scopes.entryAt scope).isSome

/-- Every value the heap holds is valid in the store that holds it (plan §3.1, ENSURES 12).
The heap only; `STORES-FB-COMPLETION` in the header. -/
def Stores.WF (s : Stores) : Prop := ∀ v ∈ s.refs, v.validIn s = true

instance (s : Stores) : Decidable s.WF := by
  unfold Stores.WF; infer_instance

/-- `Stores.empty` (`Stores.lean:1043`) is well-formed: its heap is empty (ENSURES 12). -/
theorem Stores.empty_wf : Stores.empty.WF := fun _ h => nomatch h

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

/-- Validity survives growth (plan §3.2, ENSURES 13): induction on the value. -/
theorem Val.validIn_mono {s s' : Stores} (hle : s.le s') (v : Val) (h : v.validIn s = true) :
    v.validIn s' = true := by
  induction v with
  | cell k =>
    simp only [Val.validIn, decide_eq_true_eq] at h ⊢
    exact Nat.lt_of_lt_of_le h hle.1
  | promise k =>
    simp only [Val.validIn, decide_eq_true_eq] at h ⊢
    exact Nat.lt_of_lt_of_le h hle.2.1
  | scopeHandle key => exact hle.2.2.1 key h
  | exitOk v ih => exact ih h
  | exitCons hd tl ih1 ih2 =>
    simp only [Val.validIn, Bool.and_eq_true] at h ⊢
    exact ⟨ih1 h.1, ih2 h.2⟩
  | _ => rfl

/-- Validity of an operation survives growth (plan §3.2, ENSURES 13): cases. -/
theorem SyncOp.validIn_mono {s s' : Stores} (hle : s.le s') (o : SyncOp)
    (h : o.validIn s = true) : o.validIn s' = true := by
  cases o with
  | refMake initial => exact Val.validIn_mono hle initial h
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
  | scopeAdd scope _ _ | scopeRemove scope _ | scopeIsClosed scope => exact hle.2.2.1 scope h

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
  intro x hx
  have hle : s.le { s with refs := refPoke s.refs cell y } :=
    ⟨by simp [refPoke], Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
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
    ⟨refStep_length o s.refs v heap' h, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _⟩
  cases o with
  | refMake initial =>
    simp only [refStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun x hx => Val.validIn_mono hle x ?_, ?_⟩
    · rcases List.mem_append.mp hx with hmem | hone
      · exact hwf x hmem
      · rw [List.mem_singleton.mp hone]; exact hv
    · simp [Val.validIn]
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
    refine ⟨refPoke_valid s cell value hwf hv.2, Val.validIn_mono hle _ ?_⟩
    simp only [Val.validIn, decide_eq_true_eq]
    exact hv.1
  | refGetAndSet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨refPoke_valid s cell value hwf hv.2,
      Val.validIn_mono hle a (hwf a (mem_of_refPeek_eq_some hpeek))⟩
  | refSetAndGet cell value =>
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨refPoke_valid s cell value hwf hv.2, Val.validIn_mono hle value hv.2⟩
  | refUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf ((FnName.total_validIn s f a).trans ha), rfl⟩
  | refGetAndUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf ((FnName.total_validIn s f a).trans ha),
      Val.validIn_mono hle a ha⟩
  | refUpdateAndGet cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    have hfa : (f.total a).validIn s = true := (FnName.total_validIn s f a).trans ha
    exact ⟨refPoke_valid s cell _ hwf hfa, Val.validIn_mono hle _ hfa⟩
  | refUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    refine ⟨?_, rfl⟩
    split
    · rename_i a' hpf
      exact refPoke_valid s cell a' hwf ((FnName.partialUpdate_validIn s pf a a' hpf).trans ha)
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
      exact refPoke_valid s cell a' hwf ((FnName.partialUpdate_validIn s pf a a' hpf).trans ha)
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
      exact ⟨refPoke_valid s cell a' hwf ha', Val.validIn_mono hle a' ha'⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨fun x hx => Val.validIn_mono hle x (hwf x hx), Val.validIn_mono hle a ha⟩
  | refModify cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf ((FnName.modify_validIn s f a).2.trans ha),
      Val.validIn_mono hle _ ((FnName.modify_validIn s f a).1.trans ha)⟩
  | refModifySome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have ha : a.validIn s = true := hwf a (mem_of_refPeek_eq_some hpeek)
    exact ⟨refPoke_valid s cell _ hwf ((FnName.modifySome_validIn s pf a).2.trans ha),
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
theorem syncOpStep_deferredCompleteWith (s : Stores) (cell : DeferredKey) (c : Completion) :
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

/-- `Stores.lean:1227-1229`. -/
theorem syncOpStep_scopeMake (s : Stores) (strategy : FinalizerStrategy) :
    syncOpStep (SyncOp.scopeMake strategy) s =
      some ({ s with scopes := s.scopes.make s.nextName strategy, nextName := s.nextName + 1 },
        Val.scopeHandle s.nextName) := rfl

/-- `Stores.lean:1230-1232`. -/
theorem syncOpStep_scopeAdd (s : Stores) (scope key : Nat) (fin : FinName) :
    syncOpStep (SyncOp.scopeAdd scope key fin) s =
      some ({ s with scopes := (s.scopes.addFinalizer scope key fin).1 }, Val.unit) := rfl

/-- `Stores.lean:1233-1234`. -/
theorem syncOpStep_scopeRemove (s : Stores) (scope key : Nat) :
    syncOpStep (SyncOp.scopeRemove scope key) s =
      some ({ s with scopes := s.scopes.removeFinalizer scope key }, Val.unit) := rfl

/-- `Stores.lean:1235-1236`. -/
theorem syncOpStep_scopeIsClosed (s : Stores) (scope : Nat) :
    syncOpStep (SyncOp.scopeIsClosed scope) s =
      (s.scopes.entryAt scope).map (fun entry => (s, Val.bool entry.scope.isClosed)) := rfl

/-! ## The laws of `syncOpStep` -/

/-- A step grows the store (plan §3.2, ENSURES 11): one case per arm of `syncOpStep`. -/
theorem syncOpStep_le (o : SyncOp) (s s' : Stores) (v : Val) (h : syncOpStep o s = some (s', v)) :
    s.le s' := by
  cases o with
  | deferredMake =>
    simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, by simp [DeferredStore.make], fun _ hk => hk, Nat.le_refl _⟩
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact Stores.le_refl s
  | deferredCompleteWith cell c =>
    simp only [syncOpStep_deferredCompleteWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.complete_cells_length _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _⟩
  | deferredInterruptWith cell interruptor =>
    simp only [syncOpStep_deferredInterruptWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.complete_cells_length _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _⟩
  | deferredAwaitCleanup cell waiter token =>
    simp only [syncOpStep_deferredAwaitCleanup, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_of_eq (DeferredStore.cancel_cells_length _ _ _ _).symm,
      fun _ hk => hk, Nat.le_refl _⟩
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun key hk => ScopeStore.entryAt_make_isSome _ _ _ key hk, Nat.le_succ _⟩
  | scopeAdd scope key fin =>
    simp only [syncOpStep_scopeAdd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun k hk => ScopeStore.entryAt_addFinalizer_isSome _ _ _ _ k hk, Nat.le_refl _⟩
  | scopeRemove scope key =>
    simp only [syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun k hk => ScopeStore.entryAt_removeFinalizer_isSome _ _ _ k hk, Nat.le_refl _⟩
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact ⟨refStep_length _ s.refs a heap' hstep, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _⟩

/-- A valid operation steps (plan §3.2, ENSURES 14): every `none` of `syncOpStep` and
`refStep` is a failed lookup, and validity is the lookup's success; `refUpdateSomeAndGet`
re-reads after a `refPoke`, which keeps the length (`refPeek_poke_self`, `Stores.lean`). -/
theorem syncOpStep_isSome_of_valid (o : SyncOp) (s : Stores) (hv : o.validIn s = true) :
    (syncOpStep o s).isSome = true := by
  cases o with
  | refMake initial => rfl
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
  | scopeAdd scope key fin => rfl
  | scopeRemove scope key => rfl
  | scopeIsClosed scope =>
    simp only [SyncOp.validIn] at hv
    simp [syncOpStep_scopeIsClosed, hv]

/-- A valid step from a well-formed store reaches a well-formed store (plan §3.2,
ENSURES 15): the heap arms by `refStep_valid`, the store arms by growth alone, since they
leave the heap untouched. -/
theorem syncOpStep_wf (o : SyncOp) (s s' : Stores) (v : Val) (hwf : s.WF)
    (hv : o.validIn s = true) (h : syncOpStep o s = some (s', v)) : s'.WF := by
  have hle := syncOpStep_le o s s' v h
  cases o with
  | deferredMake | deferredCompleteWith _ _ | deferredInterruptWith _ _
  | deferredAwaitCleanup _ _ _ | scopeMake _ | scopeAdd _ _ _ | scopeRemove _ _ =>
    simp only [syncOpStep_deferredMake, syncOpStep_deferredCompleteWith,
      syncOpStep_deferredInterruptWith, syncOpStep_deferredAwaitCleanup, syncOpStep_scopeMake,
      syncOpStep_scopeAdd, syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro x hx
    exact Val.validIn_mono hle x (hwf x hx)
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    exact hwf
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
    simp [Val.validIn, DeferredStore.make]
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    rfl
  | deferredCompleteWith _ _ | deferredInterruptWith _ _ | deferredAwaitCleanup _ _ _
  | scopeAdd _ _ _ | scopeRemove _ _ =>
    simp only [syncOpStep_deferredCompleteWith, syncOpStep_deferredInterruptWith,
      syncOpStep_deferredAwaitCleanup, syncOpStep_scopeAdd, syncOpStep_scopeRemove,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ScopeStore.entryAt_make_self s.scopes s.nextName strategy
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
