import Effect4.Laws.Program.Typed
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.RefKernel

/-!
# Program.Progress — a typed, valid request steps to a typed, valid answer (the first join)

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §6, node `PROGRESS/answer`.
Packet: `Test/contracts/program-denotation.contract.md`. Batteries:
`Test/Program/ProgressContract.lean` (the guards and the rows `E4-PROGRESS-CE-001`,
`E4-PROGRESS-CE-002`).

This module joins lane 1 (`src/Effect4/Laws/Program/Typed.lean`: which values inhabit which types,
and that a typed request decodes to a store operation) with lane 2
(`src/Effect4/Laws/Machine/StoresLaws.lean`: a valid operation steps, keeps the heap well-formed,
and answers a valid value). The join is `answer_typed`: the value a store step answers to a
typed request has the row's answer type. `progress` is the corollary that reads the two lanes
together: a typed, valid request decodes, steps, and its answer is typed and valid in a store
that is again well-formed.

One hypothesis the plan did not write is needed, and one witness shows why. `Stores.WF`
(`StoresLaws.lean:108`) says only that the heap's handles exist; a heap `[Val.bool true]` is
well-formed, `refGet ⟨0⟩` is valid in it, its request `Val.cell ⟨0⟩` has the row's request
type, and the answer `Val.bool true` is not a `.nat` (`E4-PROGRESS-CE-001`). So the theorem
carries `Stores.HeapNat`, every cell holds a number — the `number` in the one cell type this
cut spells, `NativeOp.refTy` (`Native.lean:133`) — and `step_heapNat` shows the typed route
keeps it. Validity alone does not: `refMake (Val.bool true)` is a valid operation that breaks
it (`E4-PROGRESS-CE-002`), which is why preservation is stated on a typed request and not on
`SyncOp.validIn`.

Three of the plan's hypotheses are not needed for the answer's type, once the step is given:
`Stores.WF` (the answer's type comes from `HeapNat`, its validity from lane 2's
`syncOpStep_answer_valid`, which does carry `WF`), `SyncOp.validIn` (the step's existence is
what validity buys, and `hstep` already asserts it), and the row's kind (`syncOpOf` sends the
one `async` row to `none`, `syncOpOf_async_none`). All three return in `progress`, where the
step is concluded rather than assumed.

Lane 1 types no `FnName` result (`Stores.lean:458-482`); the four `FnName.*_hasTy_nat`
theorems below fill that for the `.nat` column, in this module rather than in lane 1's file.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Pure option selection retains store validity -/

/-- A presence test constructs only a Boolean; raw malformed option inputs refuse. -/
theorem NativeAtom.isSome_validIn (s : Stores) (input result : Val)
    (heval : NativeAtom.eval .isSome [input] = some result) :
    Val.validIn s result = true := by
  cases input <;> simp only [NativeAtom.eval, reduceCtorEq] at heval
  all_goals cases heval; rfl

/-- Option selection retains store validity of the selected argument. This does not
replace the separate minted-fiber invariant, which uses the machine's whole handle world. -/
theorem NativeAtom.getOrElse_validIn (s : Stores) (input fallback result : Val)
    (hinput : Val.validIn s input = true) (hfallback : Val.validIn s fallback = true)
    (heval : NativeAtom.eval .getOrElse [input, fallback] = some result) :
    Val.validIn s result = true := by
  cases input <;> simp only [NativeAtom.eval, reduceCtorEq] at heval
  all_goals cases heval
  all_goals first | exact hfallback | exact hinput

/-! ## The heap holds numbers -/

/-- Every cell of the heap holds a `.nat`: the typing half of the heap invariant, beside lane
2's `Stores.WF` (`StoresLaws.lean:108`), which is the handle half. The one cell type this cut
spells is `NativeOp.refTy = "Ref.Ref<number>"`, so this is what the type promises. -/
def Stores.HeapNat (s : Stores) : Prop := ∀ v ∈ s.refs, Val.hasTy v .nat = true

instance instDecidableHeapNat (s : Stores) : Decidable (Stores.HeapNat s) := by
  unfold Stores.HeapNat; infer_instance

/-- `Stores.empty` (`Stores.lean:1043`) has an empty heap. -/
theorem Stores.empty_heapNat : Stores.HeapNat Stores.empty := fun _ h => nomatch h

/-! ## The pure functions send numbers to numbers

Lane 1 types no `FnName` result; these four are the `.nat` column of `FnName.total`,
`partialUpdate`, `modify` and `modifySome` (`Stores.lean:458-482`). -/

/-- `total` (`Stores.lean:458`) on a number is a number. -/
theorem FnName.total_hasTy_nat (f : FnName) (a : Val) (ha : Val.hasTy a .nat = true) :
    Val.hasTy (f.total a) .nat = true := by
  obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv ha
  cases f <;> simp [FnName.total, Val.hasTy]

/-- `partialUpdate` (`Stores.lean:465`) on a number answers a number where it answers. -/
theorem FnName.partialUpdate_hasTy_nat (f : FnName) (a a' : Val) (h : f.partialUpdate a = some a')
    (ha : Val.hasTy a .nat = true) : Val.hasTy a' .nat = true := by
  obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv ha
  cases f with
  | noChange => simp [FnName.partialUpdate] at h
  | zeroWhenPositive =>
    cases n with
    | zero => simp [FnName.partialUpdate] at h
    | succ n =>
      simp only [FnName.partialUpdate, Option.some.injEq] at h
      subst h
      simp [Val.hasTy]
  | _ =>
    simp only [FnName.partialUpdate, Option.some.injEq] at h
    subst h
    exact FnName.total_hasTy_nat _ _ ha

/-- Both components of `modify` (`Stores.lean:472`) on a number are numbers. -/
theorem FnName.modify_hasTy_nat (f : FnName) (a : Val) (ha : Val.hasTy a .nat = true) :
    Val.hasTy (f.modify a).1 .nat = true ∧ Val.hasTy (f.modify a).2 .nat = true := by
  obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv ha
  cases f <;> simp [FnName.modify, FnName.total, Val.hasTy]

/-- Both components of `modifySome` (`Stores.lean:477`) on a number, the written one read
through `getD` as `refStep` does (`Stores.lean:521-523`), are numbers. -/
theorem FnName.modifySome_hasTy_nat (f : FnName) (a : Val) (ha : Val.hasTy a .nat = true) :
    Val.hasTy (f.modifySome a).1 .nat = true ∧
      Val.hasTy ((f.modifySome a).2.getD a) .nat = true := by
  obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv ha
  cases f <;> simp [FnName.modifySome, FnName.modify, FnName.total, Val.hasTy]

/-! ## The handles inhabit their spellings

`Val.hasTy` on a handle compares the type's spelling with the handle's (`Typed.lean:60-63`);
on the row's own spelling that is a string literal against itself. `simp` settles it through
`LawfulBEq String`, which reaches `Classical.choice`; `rfl` settles it by evaluation and
reaches nothing, so these three are spelled that way and the join uses them. -/

/-- A cell inhabits `NativeOp.refTy` (`Native.lean:133`). -/
theorem Val.hasTy_cell_refTy (k : RefKey) : Val.hasTy (Val.cell k) NativeOp.refTy = true := by
  simp only [Val.hasTy, NativeOp.refTy]
  rfl

/-- A promise inhabits `NativeOp.deferredTy` (`Native.lean:134`). -/
theorem Val.hasTy_promise_deferredTy (k : DeferredKey) :
    Val.hasTy (Val.promise k) NativeOp.deferredTy = true := by
  simp only [Val.hasTy, NativeOp.deferredTy]
  rfl

/-- A scope handle inhabits `Ty.scope` (`Eff.lean:144`). -/
theorem Val.hasTy_scopeHandle_scope (n : Nat) : Val.hasTy (Val.scopeHandle n) Ty.scope = true := by
  simp only [Val.hasTy, Ty.scope]
  rfl

/-! ## The heap rows, typed once -/

/-- The written component of a typed pair request has the pair's second type. -/
theorem Val.hasTy_tuple_snd {x y : Val} {a b : Ty}
    (h : Val.hasTy (Val.tuple [x, y]) (.prod a b) = true) : Val.hasTy y b = true := by
  obtain ⟨_, _, he, _, hy⟩ := Val.hasTy_prod_inv h
  cases he
  exact hy

/-- A typed request of a heap row decodes to an operation whose kernel (`SyncOp.refKernel`,
`Laws/Machine/RefKernel.lean`) reads numbers, writes numbers, and answers the row's answer type.
One case a row, and the cases are `syncOpOf`'s own: `split` on its match hands each arm its
request decoded, `h_2` (`refGet`) to `h_13` (`refModifySome`). Reads answer the cell's number;
the writes of `refSet`, `refGetAndSet` and `refSetAndGet` are the request's number; the
read-modify-write rows answer and write through `FnName.*_hasTy_nat`. -/
theorem NativeOp.kernel_typed {op : NativeOp} {v : Val} {o : SyncOp} {cell : RefKey}
    {k : RefKernel} (hv : Val.hasTy v (NativeOp.row op).request = true)
    (ho : NativeOp.syncOpOf op v = some o) (hk : o.refKernel = some (cell, k)) :
    RefKernel.Keeps (Val.hasTy · .nat = true) (Val.hasTy · (NativeOp.row op).answer = true) k := by
  unfold NativeOp.syncOpOf at ho
  split at ho <;> cases ho <;> cases hk <;> intro c r hc hr <;> cases hr
  case h_2 =>  -- refGet
    exact ⟨hc, nofun⟩
  case h_3 =>  -- refSet
    exact ⟨Val.hasTy_cell_refTy _, fun _ h => by cases h; exact Val.hasTy_tuple_snd hv⟩
  case h_4 =>  -- refGetAndSet
    exact ⟨hc, fun _ h => by cases h; exact Val.hasTy_tuple_snd hv⟩
  case h_5 =>  -- refSetAndGet
    exact ⟨Val.hasTy_tuple_snd hv, fun _ h => by cases h; exact Val.hasTy_tuple_snd hv⟩
  case h_6 f _ =>  -- refUpdate
    exact ⟨rfl, fun _ h => by cases h; exact FnName.total_hasTy_nat f c hc⟩
  case h_7 f _ =>  -- refGetAndUpdate
    exact ⟨hc, fun _ h => by cases h; exact FnName.total_hasTy_nat f c hc⟩
  case h_8 f _ =>  -- refUpdateAndGet
    have ht := FnName.total_hasTy_nat f c hc
    exact ⟨ht, fun _ h => by cases h; exact ht⟩
  case h_9 f _ =>  -- refUpdateSome
    exact ⟨rfl, fun a' h => FnName.partialUpdate_hasTy_nat f c a' h hc⟩
  case h_10 f _ =>  -- refGetAndUpdateSome
    exact ⟨hc, fun a' h => FnName.partialUpdate_hasTy_nat f c a' h hc⟩
  case h_11 f _ =>  -- refUpdateSomeAndGet: what it wrote, or what it read
    have hw := fun a' h => FnName.partialUpdate_hasTy_nat f c a' h hc
    exact ⟨RefKernel.getD_keeps hw hc, hw⟩
  case h_12 f _ =>  -- refModify
    have hm := FnName.modify_hasTy_nat f c hc
    exact ⟨hm.1, fun _ h => by cases h; exact hm.2⟩
  case h_13 f _ =>  -- refModifySome
    have hm := FnName.modifySome_hasTy_nat f c hc
    exact ⟨hm.1, fun _ h => by cases h; exact hm.2⟩

/-! ## The join -/

/-- A typed request's step answers a value of the row's answer type and leaves every cell a
number. The heap rows but `refMake` are one case: the step is the operation's kernel
(`syncOpStep_eq_refStepOf`), typed by its line of `NativeOp.kernel_typed`, and
`refStepOf_keeps` carries every cell's number through the write. The other rows take
`syncOpOf`'s own cases: `refMake` answers the fresh cell and appends the request's number, and
the Deferred, scope and clock rows leave the heap alone and answer through their arm equations
(`StoresLaws.lean`). -/
theorem step_typed (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val)
    (hheap : Stores.HeapNat s)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (ho : NativeOp.syncOpOf op v = some o)
    (hstep : syncOpStep o s = some (s', a)) :
    Val.hasTy a (NativeOp.row op).answer = true ∧ Stores.HeapNat s' := by
  cases hk : o.refKernel with
  | some p =>
    obtain ⟨cell, k⟩ := p
    rw [syncOpStep_eq_refStepOf hk] at hstep
    obtain ⟨⟨b, heap'⟩, hr, hf⟩ := Option.map_eq_some_iff.mp hstep
    cases hf
    exact refStepOf_keeps hheap (NativeOp.kernel_typed hv ho hk) hr
  | none =>
    unfold NativeOp.syncOpOf at ho
    split at ho <;> cases ho <;> cases hk
    case h_1 =>  -- refMake: the fresh cell, and the heap grown by the request's number
      simp only [syncOpStep, refStep, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine ⟨Val.hasTy_cell_refTy _, fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hmem | hone
      · exact hheap x hmem
      · rw [List.mem_singleton.mp hone]
        rfl
    case h_14 =>  -- deferredMake
      simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨Val.hasTy_promise_deferredTy _, hheap⟩
    case h_15 =>  -- deferredIsDone
      simp only [syncOpStep_deferredIsDone] at hstep
      obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp hstep
      cases hf
      exact ⟨rfl, hheap⟩
    case h_16 =>  -- deferredPoll
      simp only [syncOpStep_deferredPoll] at hstep
      obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp hstep
      cases hf
      exact ⟨rfl, hheap⟩
    case h_17 | h_18 =>  -- deferredSucceed, deferredFail
      simp only [syncOpStep_deferredCompleteWith, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨rfl, hheap⟩
    case h_19 strategy =>  -- scopeMake, whose row is spelled per strategy
      simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      cases strategy <;> exact ⟨Val.hasTy_scopeHandle_scope s.nextName, hheap⟩
    case h_20 =>  -- clockNow
      simp only [syncOpStep_clockNow, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨rfl, hheap⟩

/-- `PROGRESS/answer` (plan §6): the value a store step answers to a typed request has the
row's answer type. Stated on the step itself, so neither `Stores.WF` nor `SyncOp.validIn`
nor the row's kind is needed (module header); `Stores.HeapNat` is. -/
theorem answer_typed (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val)
    (hheap : Stores.HeapNat s)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (ho : NativeOp.syncOpOf op v = some o)
    (hstep : syncOpStep o s = some (s', a)) :
    Val.hasTy a (NativeOp.row op).answer = true :=
  (step_typed op v o s s' a hheap hv ho hstep).1

/-- A typed request's step leaves every cell a number: `HeapNat` is an invariant of the typed
route. It is not an invariant of valid operations (`E4-PROGRESS-CE-002`), which is why the
request is typed here and the operation is decoded from it. -/
theorem step_heapNat (op : NativeOp) (v : Val) (o : SyncOp) (s s' : Stores) (a : Val)
    (hheap : Stores.HeapNat s)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (ho : NativeOp.syncOpOf op v = some o)
    (hstep : syncOpStep o s = some (s', a)) : Stores.HeapNat s' :=
  (step_typed op v o s s' a hheap hv ho hstep).2

/-! ## Progress -/

/-- A typed request value's handles are the decoded operation's keys, so the value's validity
(`Val.validIn`, `StoresLaws.lean:68`) is the operation's (`SyncOp.validIn`, `:81`): the
request of a heap row is the cell, or the cell paired with the written number; of a Deferred
row the promise, or the promise paired with a number; of `deferredMake` and `scopeMake` the
unit. -/
theorem syncOpOf_validIn (op : NativeOp) (v : Val) (o : SyncOp) (s : Stores)
    (hv : Val.hasTy v (NativeOp.row op).request = true)
    (ho : NativeOp.syncOpOf op v = some o) (hval : v.validIn s = true) : o.validIn s = true := by
  cases op with
  | refMake =>
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hv
    cases ho
    rfl
  | refSet | refGetAndSet | refSetAndGet =>
    obtain ⟨x, y, rfl, hx, _⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hx
    cases ho
    simpa [Val.validIn_list, Val.validIn_cell, SyncOp.validIn] using hval
  | deferredMake =>
    obtain rfl := Val.hasTy_unit_inv hv
    cases ho
    rfl
  | deferredIsDone | deferredPoll =>
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hv
    cases ho
    exact hval
  | deferredSucceed | deferredFail =>
    obtain ⟨x, y, rfl, hx, hy⟩ := Val.hasTy_prod_inv hv
    obtain ⟨k, rfl⟩ := Val.hasTy_deferredTy_inv hx
    obtain ⟨n, rfl⟩ := Val.hasTy_nat_inv hy
    cases ho
    simp only [Val.validIn_list, List.all_cons, List.all_nil, Val.validIn_promise, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hval
    simp only [SyncOp.validIn, decide_eq_true_eq]
    exact hval.1
  | external _ => cases ho
  | deferredAwait =>
    rw [syncOpOf_async_none NativeOp.deferredAwait v rfl] at ho
    cases ho
  | scopeMake strategy =>
    cases strategy with
    | sequential =>
      obtain rfl := Val.hasTy_unit_inv hv
      cases ho
      rfl
    | parallel =>
      obtain rfl := Val.hasTy_unit_inv hv
      cases ho
      rfl
  | sleep =>
    rw [syncOpOf_async_none NativeOp.sleep v rfl] at ho
    cases ho
  | clockNow =>
    obtain rfl := Val.hasTy_unit_inv hv
    cases ho
    rfl
  -- every remaining row is a bare cell request: the handle IS the operation's key
  | _ =>
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    cases ho
    exact hval

/-- The two lanes read together: a typed, valid request of a `sync` row on a well-formed
store whose cells hold numbers decodes (`syncOpOf_isSome`), steps
(`syncOpStep_isSome_of_valid` through `syncOpOf_validIn`), and answers a value of the row's
answer type (`answer_typed`) that is valid in the new store (`syncOpStep_answer_valid`),
which is again well-formed (`syncOpStep_wf`) with numbers in its cells (`step_heapNat`). -/
theorem progress (op : NativeOp) (v : Val) (s : Stores)
    (hwf : s.WF) (hheap : Stores.HeapNat s) (hkind : (NativeOp.row op).kind = .sync)
    (hv : Val.hasTy v (NativeOp.row op).request = true) (hval : v.validIn s = true) :
    ∃ o s' a, NativeOp.syncOpOf op v = some o ∧ syncOpStep o s = some (s', a) ∧
      Val.hasTy a (NativeOp.row op).answer = true ∧ a.validIn s' = true ∧
      s'.WF ∧ Stores.HeapNat s' := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (syncOpOf_isSome op v hv hkind)
  have hvalid : o.validIn s = true := syncOpOf_validIn op v o s hv ho hval
  obtain ⟨⟨s', a⟩, hstep⟩ :=
    Option.isSome_iff_exists.mp (syncOpStep_isSome_of_valid o s hvalid)
  exact ⟨o, s', a, ho, hstep, answer_typed op v o s s' a hheap hv ho hstep,
    syncOpStep_answer_valid o s s' a hwf hvalid hstep, syncOpStep_wf o s s' a hwf hvalid hstep,
    step_heapNat op v o s s' a hheap hv ho hstep⟩

end Effect4.Program
