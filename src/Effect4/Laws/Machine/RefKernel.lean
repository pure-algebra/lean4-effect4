import Effect4.Machine.Stores
import Effect4.Laws.Machine.Arena
import Effect4.Laws.Auto.Obligations

/-!
# Machine.RefKernel — the heap rows as one kernel

Every heap row of `refStep` (`Machine/Stores.lean`) but `refMake` reads one cell, computes from
the value it read an answer and what to leave in the cell, and writes that back. `refStepOf`
states that shape once; `SyncOp.refKernel` gives each row its cell and its kernel, one line a
row; `refStep_eq_refStepOf` proves the table is the machine, row by row. A fact about the heap
rows is then proved once, on the kernel (`refStepOf_keeps`), from one fact per row about what
that row's kernel answers and writes.

`refStep` stays the machine's definition: its census clauses (`refStep_make` and kin) keep their
statements, and no function value enters the runtime closure. A kernel answers `none` where its
row has no answer for the value it read. No row does today; once a row carries a term
(decisions row 43), a term that does not evaluate is that `none`, and `refStepOf` carries it as
the step's frontier.
-/

set_option autoImplicit false

namespace Effect4.Machine

/-- What a heap row does with the value it read: its answer, and the value to leave in the cell
(`none` leaves the cell as it was). -/
abbrev RefKernel := Val → Option (Val × Option Val)

/-- Leave `next` in the cell, or the heap as it was. -/
def refWriteBack (heap : RefHeap) (cell : RefKey) : Option Val → RefHeap
  | some next => refPoke heap cell next
  | none => heap

/-- The heap step of a kernel row: read `cell`, run the kernel on what it holds, write back. -/
def refStepOf (cell : RefKey) (k : RefKernel) (heap : RefHeap) : Option (Val × RefHeap) :=
  (refPeek heap cell).bind fun a => (k a).map fun r => (r.1, refWriteBack heap cell r.2)

/-- Each heap row's cell and kernel. `refMake` allocates, so it is not a kernel row, and no other
operation touches the heap. -/
def SyncOp.refKernel : SyncOp → Option (RefKey × RefKernel)
  | .refGet cell => some (cell, fun a => some (a, none))
  | .refSet cell value => some (cell, fun _ => some (Val.cell cell, some value))
  | .refGetAndSet cell value => some (cell, fun a => some (a, some value))
  | .refSetAndGet cell value => some (cell, fun _ => some (value, some value))
  | .refUpdate cell f => some (cell, fun a => some (Val.unit, some (f.total a)))
  | .refGetAndUpdate cell f => some (cell, fun a => some (a, some (f.total a)))
  | .refUpdateAndGet cell f => some (cell, fun a => some (f.total a, some (f.total a)))
  | .refUpdateSome cell pf => some (cell, fun a => some (Val.unit, pf.partialUpdate a))
  | .refGetAndUpdateSome cell pf => some (cell, fun a => some (a, pf.partialUpdate a))
  | .refUpdateSomeAndGet cell pf =>
    some (cell, fun a => some ((pf.partialUpdate a).getD a, pf.partialUpdate a))
  | .refModify cell f => some (cell, fun a => some ((f.modify a).1, some (f.modify a).2))
  | .refModifySome cell pf =>
    some (cell, fun a => some ((pf.modifySome a).1, some ((pf.modifySome a).2.getD a)))
  | .refMake _ | .deferredMake | .deferredIsDone _ | .deferredPoll _ | .deferredCompleteWith _ _
  | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ | .clockNow | .sleepCancel _ _
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _
  | .memoFork _ | .memoGet _ _ | .memoBuild _ _ | .memoComplete _ _ _ | .memoRelease _ _ => none

/-! ## The table is the machine -/

/-- Each row's kernel, run by `refStepOf`, is its `refStep` arm: after the read, the two agree
by unfolding (`refStep` maps over the read where `refStepOf` binds, since a kernel may refuse).
`refUpdateSomeAndGet` reads the cell again after its write, and that read is the value written
(`refPeek_poke_self`). -/
theorem refStep_eq_refStepOf {o : SyncOp} {cell : RefKey} {k : RefKernel}
    (hk : o.refKernel = some (cell, k)) (heap : RefHeap) :
    refStep o heap = refStepOf cell k heap := by
  cases o with
  | refUpdateSomeAndGet _ pf =>
    cases hk
    simp only [refStep, refStepOf]
    refine Option.bind_congr fun a hpeek => ?_
    cases pf.partialUpdate a with
    | some a' =>
      dsimp only
      rw [refPeek_poke_self heap cell a' a hpeek]
      rfl
    | none => rfl
  | _ =>
    cases hk <;> simp only [refStep, refStepOf, Option.map_eq_bind] <;>
      exact Option.bind_congr fun _ _ => rfl

/-- A heap step allocates or runs a kernel row. -/
theorem refStep_cases {o : SyncOp} {heap heap' : RefHeap} {a : Val}
    (h : refStep o heap = some (a, heap')) :
    (∃ initial, o = .refMake initial) ∨
      ∃ cell k, o.refKernel = some (cell, k) ∧ refStepOf cell k heap = some (a, heap') := by
  cases hk : o.refKernel with
  | some p =>
    obtain ⟨cell, k⟩ := p
    exact .inr ⟨cell, k, rfl, (refStep_eq_refStepOf hk heap).symm.trans h⟩
  | none =>
    cases o with
    | refMake initial => exact .inl ⟨initial, rfl⟩
    | _ => cases hk <;> cases h

/-- A kernel row's store step is its heap step, with the heap put back in the store. -/
theorem syncOpStep_eq_refStepOf {o : SyncOp} {cell : RefKey} {k : RefKernel}
    (hk : o.refKernel = some (cell, k)) (s : Stores) :
    syncOpStep o s = (refStepOf cell k s.refs).map fun step => ({ s with refs := step.2 }, step.1) := by
  rw [← refStep_eq_refStepOf hk s.refs]
  cases o <;> cases hk <;> rfl

/-! ## One proof for every kernel row -/

/-- What the write-back leaves has the heap's length. -/
theorem refWriteBack_length (heap : RefHeap) (cell : RefKey) (w : Option Val) :
    (refWriteBack heap cell w).length = heap.length := by
  cases w with
  | some next => exact List.length_set
  | none => rfl

/-- A cell after the write-back held its value before, or is the value written. -/
theorem mem_refWriteBack {heap : RefHeap} {cell : RefKey} {w : Option Val} {x : Val}
    (h : x ∈ refWriteBack heap cell w) : x ∈ heap ∨ ∃ next, w = some next ∧ x = next := by
  cases w with
  | some next =>
    rcases List.mem_or_eq_of_mem_set h with hmem | rfl
    · exact .inl hmem
    · exact .inr ⟨x, rfl, rfl⟩
  | none => exact .inl h

/-- A kernel row keeps the heap's length. -/
theorem refStepOf_length {cell : RefKey} {k : RefKernel} {heap heap' : RefHeap} {a : Val}
    (h : refStepOf cell k heap = some (a, heap')) : heap'.length = heap.length := by
  obtain ⟨c, _, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, _, hf⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at hf
  obtain ⟨_, rfl⟩ := hf
  exact refWriteBack_length heap cell r.2

/-- `k` keeps `P` on the cells and answers in `Q`: on a value with `P` it answers a value with
`Q`, and whatever it writes has `P`. -/
def RefKernel.Keeps (P Q : Val → Prop) (k : RefKernel) : Prop :=
  ∀ c r, P c → k c = some r → Q r.1 ∧ ∀ next, r.2 = some next → P next

/-- `updateSomeAndGet` answers what it wrote, or what it read when it wrote nothing, so its answer
has any property both have. -/
theorem RefKernel.getD_keeps {P : Val → Prop} {w : Option Val} {a : Val}
    (hw : ∀ next, w = some next → P next) (ha : P a) : P (w.getD a) := by
  cases w with
  | some next => exact hw next rfl
  | none => exact ha

/-- The one proof about a heap row: when every cell has `P` and the row's kernel keeps it, every
cell after the step has `P` and the answer has `Q`. -/
theorem refStepOf_keeps {P Q : Val → Prop} {cell : RefKey} {k : RefKernel}
    {heap heap' : RefHeap} {a : Val} (hheap : ∀ c ∈ heap, P c) (hk : RefKernel.Keeps P Q k)
    (h : refStepOf cell k heap = some (a, heap')) : Q a ∧ ∀ c ∈ heap', P c := by
  obtain ⟨c, hpeek, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hkr, hf⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  obtain ⟨hq, hnext⟩ := hk c r (hheap c (List.mem_of_getElem? hpeek)) hkr
  refine ⟨hq, fun x hx => ?_⟩
  rcases mem_refWriteBack hx with hmem | ⟨next, hw, rfl⟩
  · exact hheap x hmem
  · exact hnext x hw

end Effect4.Machine

-- BEGIN M1 PHASE B RefKernel
namespace Effect4.Machine

/-! The arena kernel projects to the list kernel; its size and predicate laws
therefore follow from the existing list-kernel laws. -/

/-- Same optional write-back as the existing list kernel, at an arbitrary carrier. -/
def writeBackA {σ α : Type} [Arena σ α] (s : σ) (cell : RefKey) : Option α → σ
  | some next => Arena.poke s cell.index next
  | none => s

def refStepOfA {σ : Type} [Arena σ Val] (cell : RefKey) (k : RefKernel)
    (s : σ) : Option (Val × σ) :=
  (Arena.peek s cell.index).bind fun a =>
    (k a).map fun r => (r.1, writeBackA s cell r.2)

namespace ArenaObligations

theorem toList_refStepOf {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    (cell : RefKey) (k : RefKernel) (s : σ) : ProofGraph.Obligation (
    (refStepOfA cell k s).map (Prod.map id Arena.toList) =
      refStepOf cell k (Arena.toList s)) := ⟨⟩

theorem refStepOfA_list (cell : RefKey) (k : RefKernel) (xs : List Val) :
    ProofGraph.Obligation (refStepOfA cell k xs = refStepOf cell k xs) := ⟨⟩

theorem refStepOfA_size {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    {cell : RefKey} {k : RefKernel} {s s' : σ} {a : Val}
    (_h : refStepOfA cell k s = some (a, s')) :
    ProofGraph.Obligation (Arena.size s' = Arena.size s) := ⟨⟩

theorem refStepOfA_keeps {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    {P Q : Val → Prop} {cell : RefKey} {k : RefKernel} {s s' : σ} {a : Val}
    (_hheap : ∀ i v, Arena.peek s i = some v → P v)
    (_hk : RefKernel.Keeps P Q k) (_h : refStepOfA cell k s = some (a, s')) :
    ProofGraph.Obligation (Q a ∧ ∀ i v, Arena.peek s' i = some v → P v) := ⟨⟩

end ArenaObligations

namespace M1.RefKernelSupport

theorem toList_writeBackA {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    (s : σ) (cell : RefKey) (next : Option Val) : ProofGraph.Obligation
    (Arena.toList (writeBackA s cell next) = refWriteBack (Arena.toList s) cell next) := ⟨⟩

end M1.RefKernelSupport

/-- Projecting the optional write-back gives the existing list write-back. -/
theorem toList_writeBackA {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    (s : σ) (cell : RefKey) (next : Option Val) :
    Arena.toList (writeBackA s cell next) = refWriteBack (Arena.toList s) cell next := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
    (add norm simp [writeBackA, refWriteBack, refPoke])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_writeBackA

/-- The arena kernel projects to the existing list kernel. -/
theorem toList_refStepOf {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    (cell : RefKey) (k : RefKernel) (s : σ) :
    (refStepOfA cell k s).map (Prod.map id Arena.toList) =
      refStepOf cell k (Arena.toList s) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
    (add norm simp [refStepOfA, refStepOf, refPeek, Arena.peek_toList,
      Function.comp_def, Prod.map])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] toList_refStepOf

/-- The generic kernel on lists is the existing list kernel. -/
theorem refStepOfA_list (cell : RefKey) (k : RefKernel) (xs : List Val) :
    refStepOfA cell k xs = refStepOf cell k xs := by
  have project : (Arena.toList : List Val → List Val) = id := by
    funext values
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  simpa only [project, Prod.map_id, Option.map_id_apply, id_eq] using
    (toList_refStepOf cell k xs)

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] refStepOfA_list

/-- The projected list step supplies the arena step's size law. -/
theorem refStepOfA_size {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    {cell : RefKey} {k : RefKernel} {s s' : σ} {a : Val}
    (h : refStepOfA cell k s = some (a, s')) : Arena.size s' = Arena.size s := by
  have projected : refStepOf cell k (Arena.toList s) = some (a, Arena.toList s') := by
    rw [← toList_refStepOf, h]
    rfl
  have lengths := refStepOf_length projected
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] refStepOfA_size

/-- The projected list step supplies the arena step's cell and answer predicates. -/
theorem refStepOfA_keeps {σ : Type} [Arena σ Val] [LawfulArena σ Val]
    {P Q : Val → Prop} {cell : RefKey} {k : RefKernel} {s s' : σ} {a : Val}
    (hheap : ∀ i v, Arena.peek s i = some v → P v)
    (hk : RefKernel.Keeps P Q k) (h : refStepOfA cell k s = some (a, s')) :
    Q a ∧ ∀ i v, Arena.peek s' i = some v → P v := by
  have projected : refStepOf cell k (Arena.toList s) = some (a, Arena.toList s') := by
    rw [← toList_refStepOf, h]
    rfl
  have cells : ∀ v ∈ Arena.toList s, P v := by
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
      (add norm simp [Arena.peek_toList, List.mem_iff_getElem?])
  have kept := refStepOf_keeps cells hk projected
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
    (add norm simp [Arena.peek_toList]) (add safe forward [List.mem_of_getElem?])

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] refStepOfA_keeps

#typed_state_obligations Effect4.Machine.ArenaObligations ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

#typed_state_obligations Effect4.Machine.M1.RefKernelSupport ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

end Effect4.Machine
-- END M1 PHASE B RefKernel
