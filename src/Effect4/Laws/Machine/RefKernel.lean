import Effect4.Machine.Stores
import Effect4.Laws.Machine.Arena
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Machine.TermHandles

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
row has no answer for the value it read: a term row (decisions row 43) whose term does not
evaluate at `env ++ [a]`, or answers outside the row's shape (`termKernel`). `refStepOf` carries
that `none` as the step's frontier.

What a kernel answers and writes carries only the frames of the value it read and of the row's
own values (`SyncOp.refKernel_handles`): at a term row, the term's value carries only its
environment's (`RawHandles.evalTerm_handles`, `Laws/Machine/TermHandles.lean`). So every
property of values that their frames decide passes through every heap row
(`RefKernel.Frames.keeps`): validity in the store (`SyncOp.refKernel_validIn`,
`Laws/Machine/StoresLaws.lean`) and key containment (`SyncOp.refKernel_keys`,
`Laws/Machine/Handles.lean`).
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

/-- A term row's kernel: the term's value at `env ++ [a]`, read in the row's shape by `decode`,
then the row's answer and write-back by `arrange`. A term that does not evaluate, or whose value
`decode` refuses, is the kernel's `none`. -/
def termKernel {D : Type} (decode : Val → Option D) (arrange : Val → D → Val × Option Val)
    (f : Program.Term) (env : List Val) : RefKernel :=
  fun a => ((Program.evalTerm (env ++ [a]) f).bind decode).map (arrange a)

/-- Each heap row's cell and kernel. `refMake` allocates, so it is not a kernel row, and no other
operation touches the heap. A term row decodes as its `refStep` arm does: the value itself, the
exact option image, or the exact pair image. -/
def SyncOp.refKernel : SyncOp → Option (RefKey × RefKernel)
  | .refGet cell => some (cell, fun a => some (a, none))
  | .refSet cell value => some (cell, fun _ => some (Val.cell cell, some value))
  | .refGetAndSet cell value => some (cell, fun a => some (a, some value))
  | .refSetAndGet cell value => some (cell, fun _ => some (value, some value))
  | .refUpdate cell f env => some (cell, termKernel some (fun _ a' => (Val.unit, some a')) f env)
  | .refGetAndUpdate cell f env => some (cell, termKernel some (fun a a' => (a, some a')) f env)
  | .refUpdateAndGet cell f env => some (cell, termKernel some (fun _ a' => (a', some a')) f env)
  | .refUpdateSome cell f env =>
    some (cell, termKernel (Store.Image.ofOption Store.Image.ident) (fun _ o => (Val.unit, o)) f env)
  | .refGetAndUpdateSome cell f env =>
    some (cell, termKernel (Store.Image.ofOption Store.Image.ident) (fun a o => (a, o)) f env)
  | .refUpdateSomeAndGet cell f env =>
    some (cell,
      termKernel (Store.Image.ofOption Store.Image.ident) (fun a o => (o.getD a, o)) f env)
  | .refModify cell f env =>
    some (cell, termKernel (Store.Image.ofTuple2 Store.Image.ident Store.Image.ident)
      (fun _ r => (r.1, some r.2)) f env)
  | .refModifySome cell f env =>
    some (cell,
      termKernel (Store.Image.ofTuple2 Store.Image.ident (Store.Image.option Store.Image.ident))
        (fun a r => (r.1, some (r.2.getD a))) f env)
  | .refMake _ | .deferredMake | .deferredIsDone _ | .deferredPoll _ | .deferredCompleteWith _ _
  | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ | .clockNow | .sleepCancel _ _
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _
  | .memoFork _ | .memoGet _ _ | .memoBuild _ _ | .memoComplete _ _ _ | .memoRelease _ _ => none

/-! ## The table is the machine -/

/-- Each row's kernel, run by `refStepOf`, is its `refStep` arm: after the read, the two agree
by unfolding (`refStep` maps over the read where `refStepOf` binds, since a kernel may refuse).
A term row agrees once its term's value is decoded. `refUpdateSomeAndGet` reads the cell again
after its write, and that read is the value written (`refPeek_poke_self`). -/
theorem refStep_eq_refStepOf {o : SyncOp} {cell : RefKey} {k : RefKernel}
    (hk : o.refKernel = some (cell, k)) (heap : RefHeap) :
    refStep o heap = refStepOf cell k heap := by
  cases o with
  | refUpdate _ f env | refGetAndUpdate _ f env | refUpdateAndGet _ f env =>
    cases hk
    refine Option.bind_congr fun a _ => ?_
    show _ = (((Program.evalTerm (env ++ [a]) f).bind some).map _).map _
    cases Program.evalTerm (env ++ [a]) f <;> rfl
  | refUpdateSome _ f env | refGetAndUpdateSome _ f env =>
    cases hk
    refine Option.bind_congr fun a _ => ?_
    show _ = (((Program.evalTerm (env ++ [a]) f).bind _).map _).map _
    cases (Program.evalTerm (env ++ [a]) f).bind (Store.Image.ofOption Store.Image.ident) with
    | none => rfl
    | some next => cases next <;> rfl
  | refUpdateSomeAndGet _ f env =>
    cases hk
    refine Option.bind_congr fun a hpeek => ?_
    show _ = (((Program.evalTerm (env ++ [a]) f).bind _).map _).map _
    cases (Program.evalTerm (env ++ [a]) f).bind (Store.Image.ofOption Store.Image.ident) with
    | none => rfl
    | some next =>
      cases next with
      | some a' =>
        show (refPeek (refPoke heap cell a') cell).map _ = _
        rw [refPeek_poke_self heap cell a' a hpeek]
        rfl
      | none => rfl
  | refModify _ f env =>
    cases hk
    refine Option.bind_congr fun a _ => ?_
    show _ = (((Program.evalTerm (env ++ [a]) f).bind _).map _).map _
    cases (Program.evalTerm (env ++ [a]) f).bind
      (Store.Image.ofTuple2 Store.Image.ident Store.Image.ident) <;> rfl
  | refModifySome _ f env =>
    cases hk
    refine Option.bind_congr fun a _ => ?_
    show _ = (((Program.evalTerm (env ++ [a]) f).bind _).map _).map _
    cases (Program.evalTerm (env ++ [a]) f).bind
      (Store.Image.ofTuple2 Store.Image.ident (Store.Image.option Store.Image.ident)) <;> rfl
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

/-! ### Write and read at an allocated cell, and at one the store never allocated

The store step of the two primitive state rows, the co-operations of the store comodel whose
state laws `Laws/Program/StoreComodel.lean` proves (formal pass, algebra note A9). A cell the
heap holds is allocated: the heap only grows. -/

/-- On an allocated cell, `refSet` writes the value and answers the cell. -/
theorem syncOpStep_refSet_allocated {s : Stores} {c : RefKey} (h : c.index < s.refs.length)
    (v : Val) :
    syncOpStep (.refSet c v) s = some ({ s with refs := s.refs.set c.index v }, Val.cell c) := by
  have hp : refPeek s.refs c = some (s.refs[c.index]'h) := List.getElem?_eq_getElem h
  show (refStep (.refSet c v) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
  simp only [refStep, hp, Option.map_some, refPoke]

/-- On an allocated cell, `refGet` answers what the cell holds and leaves the stores. -/
theorem syncOpStep_refGet_allocated {s : Stores} {c : RefKey} (h : c.index < s.refs.length) :
    syncOpStep (.refGet c) s = some (s, s.refs[c.index]'h) := by
  have hp : refPeek s.refs c = some (s.refs[c.index]'h) := List.getElem?_eq_getElem h
  show (refStep (.refGet c) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
  simp only [refStep, hp, Option.map_some]

/-- On a cell the store never allocated, neither `refSet` nor `refGet` steps: the store handler's
fallback answers for both (`E4-DEN-CE-002`). -/
theorem syncOpStep_ref_unallocated {s : Stores} {c : RefKey} (h : ¬ c.index < s.refs.length)
    (v : Val) : syncOpStep (.refSet c v) s = none ∧ syncOpStep (.refGet c) s = none := by
  have hp : refPeek s.refs c = none := List.getElem?_eq_none (Nat.le_of_not_lt h)
  constructor
  · show (refStep (.refSet c v) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
    simp only [refStep, hp, Option.map_none]
  · show (refStep (.refGet c) s.refs).map (fun step => ({ s with refs := step.2 }, step.1)) = _
    simp only [refStep, hp, Option.map_none]

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

/-! ## Frames: what a heap row answers and writes

A heap row answers and writes the value it read, `unit`, its own values (`SyncOp.refArgs`) or,
at a term row, parts of its term's value, which carries only its environment's frames
(`RawHandles.evalTerm_handles`). So its answer and its write carry only frames of the value it
read and of its own values (`SyncOp.refKernel_handles`). A property of values that frames decide
then passes through every heap row (`RefKernel.Frames.keeps`), with no case on the row. -/

/-- The values a heap row carries besides the one it reads: the cell `refSet` answers and the
value it writes, the value the other two `set` rows write, a term row's environment. -/
def SyncOp.refArgs : SyncOp → List Val
  | .refSet cell value => [Val.cell cell, value]
  | .refGetAndSet _ value | .refSetAndGet _ value => [value]
  | .refUpdate _ _ env | .refGetAndUpdate _ _ env | .refUpdateAndGet _ _ env
  | .refUpdateSome _ _ env | .refGetAndUpdateSome _ _ env | .refUpdateSomeAndGet _ _ env
  | .refModify _ _ env | .refModifySome _ _ env => env
  | _ => []

/-- `k` answers and writes only frames of the value it read and of `L`. -/
def RefKernel.Frames (L : List Val) (k : RefKernel) : Prop :=
  ∀ a r, k a = some r →
    Store.Val.handles r.1 ⊆ (L ++ [a]).flatMap Store.Val.handles ∧
      ∀ next, r.2 = some next → Store.Val.handles next ⊆ (L ++ [a]).flatMap Store.Val.handles

/-- A property of values that their frames decide: a value has it when every frame it carries is
a frame of values that have it. Validity in a store and key containment are two
(`Val.validIn_framesClosed`, `Val.keys_framesClosed`). -/
def FramesClosed (P : Val → Prop) : Prop :=
  ∀ v (L : List Val), Store.Val.handles v ⊆ L.flatMap Store.Val.handles → (∀ x ∈ L, P x) → P v

/-- **A frames-closed property passes through a kernel** that answers and writes only frames of
the value it read and of `L`, when every value of `L` has it. -/
theorem RefKernel.Frames.keeps {P : Val → Prop} {L : List Val} {k : RefKernel}
    (closed : FramesClosed P) (hargs : ∀ x ∈ L, P x) (h : k.Frames L) : k.Keeps P P := by
  intro a r ha hr
  have hall : ∀ x ∈ L ++ [a], P x := fun x hx =>
    (List.mem_append.mp hx).elim (hargs x) fun hx => (List.mem_singleton.mp hx) ▸ ha
  obtain ⟨hanswer, hwrite⟩ := h a r hr
  exact ⟨closed _ _ hanswer hall, fun next hn => closed _ _ (hwrite next hn) hall⟩

/-- A member's frames are frames of the list. -/
theorem mem_flatMap_handles {x : Val} {L : List Val} (h : x ∈ L) :
    Store.Val.handles x ⊆ L.flatMap Store.Val.handles :=
  fun _ hx => List.mem_flatMap.mpr ⟨x, h, hx⟩

/-- What the exact option image reads off a value carries only that value's frames. -/
theorem ofOption_ident_handles {v : Val} {o : Option Val}
    (h : Store.Image.ofOption Store.Image.ident v = some o) {next : Val} (hn : o = some next) :
    Store.Val.handles next ⊆ Store.Val.handles v := by
  subst hn
  rw [(Store.Image.option Store.Image.ident).ofVal_exact h]
  exact List.Subset.refl _

/-- What the exact pair image reads off a value carries only that value's frames. -/
theorem ofTuple2_ident_handles {β : Type} {J : Store.Image β} {v x : Val} {y : β}
    (h : Store.Image.ofTuple2 Store.Image.ident J v = some (x, y)) :
    Store.Val.handles x ⊆ Store.Val.handles v ∧
      Store.Val.handles (J.toVal y) ⊆ Store.Val.handles v := by
  rw [(Store.Image.tuple2 Store.Image.ident J).ofVal_exact h]
  exact ⟨fun _ hx => List.mem_append_left _ hx,
    fun _ hx => List.mem_append_right _ (List.mem_append_left _ hx)⟩

/-- **A term kernel answers and writes only frames of its environment and the value read**, when
its arrangement builds from the value read and from what the decoder reads off the term's value,
which carries only the environment's frames and the read value's (`RawHandles.evalTerm_handles`). -/
theorem termKernel_frames {D : Type} {decode : Val → Option D}
    {arrange : Val → D → Val × Option Val} {f : Program.Term} {env : List Val}
    (shape : ∀ a v d, decode v = some d →
      Store.Val.handles (arrange a d).1 ⊆ Store.Val.handles v ++ Store.Val.handles a ∧
        ∀ next, (arrange a d).2 = some next →
          Store.Val.handles next ⊆ Store.Val.handles v ++ Store.Val.handles a) :
    (termKernel decode arrange f env).Frames env := by
  intro a r hr
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨v, hv, hdec⟩ := Option.bind_eq_some_iff.mp hd
  have hframes : Store.Val.handles v ++ Store.Val.handles a ⊆
      (env ++ [a]).flatMap Store.Val.handles :=
    List.append_subset.mpr ⟨Program.RawHandles.evalTerm_handles f (env ++ [a]) v hv,
      mem_flatMap_handles (List.mem_append_right env (List.mem_singleton_self a))⟩
  obtain ⟨hanswer, hwrite⟩ := shape a v d hdec
  exact ⟨List.Subset.trans hanswer hframes,
    fun next hn => List.Subset.trans (hwrite next hn) hframes⟩

/-- **Every heap row answers and writes only frames of the value it read and of its own values.**
The four rows without a term by their kernels; a term row by `termKernel_frames` and its
decoder's exactness. -/
theorem SyncOp.refKernel_handles {o : SyncOp} {cell : RefKey} {k : RefKernel}
    (hk : o.refKernel = some (cell, k)) : k.Frames o.refArgs := by
  have read : ∀ (L : List Val) (a : Val), Store.Val.handles a ⊆ (L ++ [a]).flatMap Store.Val.handles :=
    fun L a => mem_flatMap_handles (List.mem_append_right L (List.mem_singleton_self a))
  have arg : ∀ (L : List Val) (a x : Val), x ∈ L →
      Store.Val.handles x ⊆ (L ++ [a]).flatMap Store.Val.handles :=
    fun L a x hx => mem_flatMap_handles (List.mem_append_left [a] hx)
  have left : ∀ v a : Val, Store.Val.handles v ⊆ Store.Val.handles v ++ Store.Val.handles a :=
    fun _ _ _ hx => List.mem_append_left _ hx
  have right : ∀ v a : Val, Store.Val.handles a ⊆ Store.Val.handles v ++ Store.Val.handles a :=
    fun _ _ _ hx => List.mem_append_right _ hx
  cases o <;> cases hk
  case refGet => exact fun a r hr => by cases hr; exact ⟨read [] a, nofun⟩
  case refSet =>
    exact fun a r hr => by
      cases hr
      exact ⟨arg _ a _ (List.mem_cons_self ..), fun _ hn => by
        cases hn; exact arg _ a _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  case refGetAndSet =>
    exact fun a r hr => by
      cases hr
      exact ⟨read _ a, fun _ hn => by cases hn; exact arg _ a _ (List.mem_cons_self ..)⟩
  case refSetAndGet =>
    exact fun a r hr => by
      cases hr
      exact ⟨arg _ a _ (List.mem_cons_self ..), fun _ hn => by
        cases hn; exact arg _ a _ (List.mem_cons_self ..)⟩
  case refUpdate =>
    exact termKernel_frames fun a v d hd => by
      cases hd; exact ⟨List.nil_subset _, fun _ hn => by cases hn; exact left _ _⟩
  case refGetAndUpdate =>
    exact termKernel_frames fun a v d hd => by
      cases hd; exact ⟨(right _ _), fun _ hn => by cases hn; exact left _ _⟩
  case refUpdateAndGet =>
    exact termKernel_frames fun a v d hd => by
      cases hd; exact ⟨(left _ _), fun _ hn => by cases hn; exact left _ _⟩
  case refUpdateSome =>
    exact termKernel_frames fun a v d hd =>
      ⟨List.nil_subset _, fun _ hn => List.Subset.trans (ofOption_ident_handles hd hn) (left _ _)⟩
  case refGetAndUpdateSome =>
    exact termKernel_frames fun a v d hd =>
      ⟨(right _ _), fun _ hn => List.Subset.trans (ofOption_ident_handles hd hn) (left _ _)⟩
  case refUpdateSomeAndGet =>
    refine termKernel_frames fun a v d hd =>
      ⟨?_, fun _ hn => List.Subset.trans (ofOption_ident_handles hd hn) (left _ _)⟩
    cases d with
    | some next => exact List.Subset.trans (ofOption_ident_handles hd rfl) (left _ _)
    | none => exact right _ _
  case refModify =>
    exact termKernel_frames fun a v d hd =>
      ⟨List.Subset.trans (ofTuple2_ident_handles hd).1 (left _ _), fun _ hn => by
        cases hn; exact List.Subset.trans (ofTuple2_ident_handles hd).2 (left _ _)⟩
  case refModifySome =>
    refine termKernel_frames fun a v d hd =>
      ⟨List.Subset.trans (ofTuple2_ident_handles hd).1 (left _ _), fun _ hn => ?_⟩
    cases hn
    obtain ⟨x, o⟩ := d
    cases o with
    | some next => exact List.Subset.trans (ofTuple2_ident_handles hd).2 (left _ _)
    | none => exact right _ _

/-- Writing one cell leaves every other lookup exactly unchanged, including absent keys. -/
theorem refWriteBack_peek_other (heap : RefHeap) (cell : RefKey) (next : Option Val)
    (index : Nat) (different : index ≠ cell.index) :
    refPeek (refWriteBack heap cell next) ⟨index⟩ = refPeek heap ⟨index⟩ := by
  cases next with
  | none => rfl
  | some value =>
    exact List.getElem?_set_ne (Ne.symm different)

/-- C2 follows the actual refStep equation. The selected cell keeps its own predicate;
all other predicates survive by exact lookup equality, not by a homogeneous heap assumption. -/
theorem indexed_ref_step_preserves
    (P : Nat → Val → Prop) (Q : Val → Prop)
    (op : SyncOp) (cell : RefKey) (kernel : RefKernel)
    (before after : RefHeap) (answer : Val)
    (row : op.refKernel = some (cell, kernel))
    (typed : ∀ index value, refPeek before ⟨index⟩ = some value → P index value)
    (keeps : RefKernel.Keeps (P cell.index) Q kernel)
    (step : refStep op before = some (answer, after)) :
    Q answer ∧
    (∀ index value, refPeek after ⟨index⟩ = some value → P index value) ∧
    after.length = before.length ∧
    (∀ index, index ≠ cell.index → refPeek after ⟨index⟩ = refPeek before ⟨index⟩) := by
  rw [refStep_eq_refStepOf row] at step
  obtain ⟨value, read, mapped⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨pair, ran, output⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Prod.mk.injEq] at output
  obtain ⟨rfl, rfl⟩ := output
  obtain ⟨answerOk, written⟩ := keeps value pair (typed cell.index value read) ran
  refine ⟨answerOk, ?_, refWriteBack_length before cell pair.2,
    fun index different => refWriteBack_peek_other before cell pair.2 index different⟩
  intro index current lookup
  by_cases selected : index = cell.index
  · subst index
    cases hnext : pair.2 with
    | none =>
      rw [hnext] at lookup
      exact typed cell.index current lookup
    | some next =>
      rw [hnext] at lookup
      change refPeek (refPoke before cell next) cell = some current at lookup
      have self := refPeek_poke_self before cell next value read
      rw [self] at lookup
      cases lookup
      exact written _ hnext
  · rw [refWriteBack_peek_other before cell pair.2 index selected] at lookup
    exact typed index current lookup

attribute [aesop safe -100 apply (rule_sets := [Effect4.Stores])] indexed_ref_step_preserves

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

end Effect4.Machine
-- END M1 PHASE B RefKernel
