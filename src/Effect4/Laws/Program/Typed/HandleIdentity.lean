import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Typed.Adequacy

/-!
# Laws.Program.Typed.HandleIdentity — the identity of a handle inside a term

Concept: Store Typing (`store-typing`). Requirement: R4. The registry claim
`handle-identity-laws` (decisions row 229) is `handle_identity_laws`, a `HandleIdentityLaws`:
the identity test's evaluation, its totality on two members of one handle type, its three order
laws, a fresh handle's absence from every value that fits the earlier world, a later world's
membership, and the containment of a term's handles.

The top node is a decomposition: its proof cites one theorem for each field, so its status is
derived from theirs (`#plan_status`). No field rests on a planned goal.

Reach. The test reads one kind byte and two keys, and no payload, no cell and no world.
Freshness reads the world's declaration tables, and the allocation supplies the undeclared key at
typed cell columns (`CellsTyped`).

What it does not establish. No correspondence in a target: that two handles have equal keys
exactly when their host objects are one object is each target's relation (decisions row 229).

Consumers. The Queue's withdrawal by identity reads `HandleIdentityLaws`, and the reading of a
step term reads `sameHandle_promises` (`src/Effect4/Laws/Step/Reading.lean`).
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program

/-! ## The identity of a handle -/

/-- The identity test on two handle frames: one kind byte compares the two keys, and two kinds
refuse. It reads no payload, no cell and no world. -/
theorem sameHandle_eval (kind kind' : UInt8) (index index' : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      if kind = kind' then some (Val.bool (decide (index = index'))) else none := rfl

/-- On two cells the test decides the equality of the two keys. -/
theorem sameHandle_cells (k k' : RefKey) :
    NativeAtom.eval .sameHandle [Val.cell k, Val.cell k'] = some (Val.bool (decide (k = k'))) := by
  have hdec : decide (k.index = k'.index) = decide (k = k') :=
    decide_eq_decide.mpr
      ⟨fun h => by cases k; cases k'; exact congrArg RefKey.mk h, fun h => congrArg RefKey.index h⟩
  show (if (2 : UInt8) = 2 then some (Val.bool (decide (k.index = k'.index))) else none) = _
  rw [if_pos rfl, hdec]

/-- On two Deferred cells the test decides the equality of the two keys. -/
theorem sameHandle_promises (k k' : DeferredKey) :
    NativeAtom.eval .sameHandle [Val.promise k, Val.promise k'] =
      some (Val.bool (decide (k = k'))) := by
  have hdec : decide (k.index = k'.index) = decide (k = k') :=
    decide_eq_decide.mpr
      ⟨fun h => by cases k; cases k'; exact congrArg DeferredKey.mk h,
        fun h => congrArg DeferredKey.index h⟩
  show (if (3 : UInt8) = 3 then some (Val.bool (decide (k.index = k'.index))) else none) = _
  rw [if_pos rfl, hdec]

/-- **Total on two members of `refOf`**, at any two payload types: the test answers, and its
answer decides the equality of the two keys. -/
theorem sameHandle_total_ref {w : World} {a b : Val} {A B : Ty} (ha : Fits w a (.refOf A))
    (hb : Fits w b (.refOf B)) :
    ∃ k k', a = Val.cell k ∧ b = Val.cell k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k'))) := by
  obtain ⟨k, rfl, _⟩ := fits_refOf_inv ha
  obtain ⟨k', rfl, _⟩ := fits_refOf_inv hb
  exact ⟨k, k', rfl, rfl, sameHandle_cells k k'⟩

/-- **Total on two members of `deferredOf`**, at any payload and error types. -/
theorem sameHandle_total_deferred {w : World} {a b : Val} {A E B F : Ty}
    (ha : Fits w a (.deferredOf A E)) (hb : Fits w b (.deferredOf B F)) :
    ∃ k k', a = Val.promise k ∧ b = Val.promise k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k'))) := by
  obtain ⟨k, rfl, _⟩ := fits_deferredOf_inv ha
  obtain ⟨k', rfl, _⟩ := fits_deferredOf_inv hb
  exact ⟨k, k', rfl, rfl, sameHandle_promises k k'⟩

/-- **Reflexive**: a handle is the same handle as itself. -/
theorem sameHandle_refl (kind : UInt8) (index : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind index] =
      some (Val.bool true) := by
  rw [sameHandle_eval, if_pos rfl, decide_eq_true rfl]

/-- **Symmetric**: the answer, a refusal of two kinds included, does not read the order. -/
theorem sameHandle_symm (kind kind' : UInt8) (index index' : Nat) :
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      NativeAtom.eval .sameHandle [.handle kind' index', .handle kind index] := by
  rw [sameHandle_eval, sameHandle_eval]
  by_cases hkind : kind = kind'
  · rw [if_pos hkind, if_pos hkind.symm,
      (decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩ : decide (index = index') = decide (index' = index))]
  · rw [if_neg hkind, if_neg (fun h => hkind h.symm)]

/-- **The allocation supplies a fresh cell**: at typed cell columns, the cell that `refMake`
answers is undeclared before the step. The key comes from the allocation itself, not from the
world's order. -/
theorem refMake_fresh {w : World} (cells : CellsTyped w) {value : Val} {state : Stores}
    {key : RefKey} (step : syncOpStep (.refMake value) w.state = some (state, Val.cell key)) :
    w.Ρ key = none := by
  rw [syncOpStep_refMake, Option.some.injEq, Prod.mk.injEq] at step
  obtain rfl := cell_inj step.2
  cases h : w.Ρ ⟨w.state.refs.length⟩ with
  | none => rfl
  | some t =>
    have hlt := (cells.heap ⟨w.state.refs.length⟩).mp (by rw [h]; rfl)
    exact absurd hlt (Nat.lt_irrefl _)

/-- **The allocation supplies a fresh Deferred cell**, as `refMake_fresh`. -/
theorem deferredMake_fresh {w : World} (cells : CellsTyped w) {state : Stores}
    {key : DeferredKey} (step : syncOpStep .deferredMake w.state = some (state, Val.promise key)) :
    w.«Π» key = none := by
  rw [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at step
  obtain rfl := promise_inj step.2
  exact cells.promise_fresh

/-- **A fresh cell is the same handle as no handle of a value that fits the earlier world**, at
any type and any depth of nesting: every raw handle frame of a member is live in its kind's
column (`fits_live`), and the fresh cell is declared in none. -/
theorem sameHandle_fresh_cell {w : World} {key : RefKey} (fresh : w.Ρ key = none) {v : Val}
    {ty : Ty} (hv : Fits w v ty) (kind : UInt8) (index : Nat)
    (hmem : (kind, index) ∈ Store.Val.handles v) :
    NativeAtom.eval .sameHandle [Val.cell key, .handle kind index] ≠ some (Val.bool true) := by
  intro heq
  have heq' : (if (2 : UInt8) = kind then some (Val.bool (decide (key.index = index)))
      else none) = some (Val.bool true) := heq
  split at heq'
  · next hkind =>
    by_cases hidx : key.index = index
    · have hlive : KindLive w index (HandleKind.ofByte? kind) :=
        fits_live w ty v hv (kind, index) hmem
      have hcellKind : HandleKind.ofByte? 2 = some .cell := HandleKind.ofByte?_byte .cell
      rw [← hkind, hcellKind] at hlive
      have hdecl : (w.Ρ ⟨index⟩).isSome = true := hlive
      have hkey : (⟨index⟩ : RefKey) = key := by
        cases key
        exact congrArg RefKey.mk hidx.symm
      rw [hkey, fresh] at hdecl
      cases hdecl
    · rw [decide_eq_false hidx] at heq'
      cases heq'
  · cases heq'

/-- **A fresh Deferred cell is the same handle as no handle of a value that fits the earlier
world**, as `sameHandle_fresh_cell`. -/
theorem sameHandle_fresh_promise {w : World} {key : DeferredKey} (fresh : w.«Π» key = none)
    {v : Val} {ty : Ty} (hv : Fits w v ty) (kind : UInt8) (index : Nat)
    (hmem : (kind, index) ∈ Store.Val.handles v) :
    NativeAtom.eval .sameHandle [Val.promise key, .handle kind index] ≠ some (Val.bool true) := by
  intro heq
  have heq' : (if (3 : UInt8) = kind then some (Val.bool (decide (key.index = index)))
      else none) = some (Val.bool true) := heq
  split at heq'
  · next hkind =>
    by_cases hidx : key.index = index
    · have hlive : KindLive w index (HandleKind.ofByte? kind) :=
        fits_live w ty v hv (kind, index) hmem
      have hpromiseKind : HandleKind.ofByte? 3 = some .promise := HandleKind.ofByte?_byte .promise
      rw [← hkind, hpromiseKind] at hlive
      have hdecl : (w.«Π» ⟨index⟩).isSome = true := hlive
      have hkey : (⟨index⟩ : DeferredKey) = key := by
        cases key
        exact congrArg DeferredKey.mk hidx.symm
      rw [hkey, fresh] at hdecl
      cases hdecl
    · rw [decide_eq_false hidx] at heq'
      cases heq'
  · cases heq'

/-- **A fresh cell is a member of no stored list of cells**: on every element of a list that
fits the earlier world, the test answers `false`. -/
theorem fresh_cell_not_member {w : World} {key : RefKey} (fresh : w.Ρ key = none) {v : Val}
    {A : Ty} (hv : Fits w v (.list (.refOf A))) :
    ∃ xs, Val.asList? v = some xs ∧
      ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.cell key, x] = some (Val.bool false) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  refine ⟨xs, hxs, fun x hx => ?_⟩
  obtain ⟨k', rfl, t', hdecl, _⟩ := fits_refOf_inv (hall x hx)
  have hne : ¬ key = k' := fun e => by
    rw [e, hdecl] at fresh
    cases fresh
  rw [sameHandle_cells, decide_eq_false hne]

/-- **A fresh Deferred cell is a member of no stored list of Deferred cells.** -/
theorem fresh_promise_not_member {w : World} {key : DeferredKey} (fresh : w.«Π» key = none)
    {v : Val} {A E : Ty} (hv : Fits w v (.list (.deferredOf A E))) :
    ∃ xs, Val.asList? v = some xs ∧
      ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.promise key, x] = some (Val.bool false) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  refine ⟨xs, hxs, fun x hx => ?_⟩
  obtain ⟨k', rfl, a', e', hdecl, _⟩ := fits_deferredOf_inv (hall x hx)
  have hne : ¬ key = k' := fun e => by
    rw [e, hdecl] at fresh
    cases fresh
  rw [sameHandle_promises, decide_eq_false hne]

/-- **A later world keeps a list's membership and each element's**: the decoded elements are the
value's own, read with no world, and each fits at the later world (`fits_mono`). The identity
test reads no world, so every answer it gave is its answer there. -/
theorem list_later {w w' : World} (ord : w.leHost w') {v : Val} {H : Ty}
    (hv : Fits w v (.list H)) :
    Fits w' v (.list H) ∧ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w' x H := by
  have hv' := fits_mono ord hv
  exact ⟨hv', (fits_list_iff w' v H).mp hv'⟩

/-- The laws of a handle's identity in a term (decisions row 229; the design's F4), over `Fits`
and the world's order. -/
structure HandleIdentityLaws : Prop where
  /-- **The test.** One kind byte compares the two keys, and two kinds refuse. It reads no
  payload, no cell and no world. -/
  eval : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      if kind = kind' then some (Val.bool (decide (index = index'))) else none
  /-- **Law 1 and the decision of law 2**, at `refOf`: total at any two payload types, and the
  answer decides the equality of the two keys. -/
  totalRef : ∀ (w : World) (a b : Val) (A B : Ty), Fits w a (.refOf A) → Fits w b (.refOf B) →
    ∃ k k', a = Val.cell k ∧ b = Val.cell k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  /-- The same at `deferredOf`. -/
  totalDeferred : ∀ (w : World) (a b : Val) (A E B F : Ty), Fits w a (.deferredOf A E) →
    Fits w b (.deferredOf B F) →
      ∃ k k', a = Val.promise k ∧ b = Val.promise k' ∧
        NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  /-- **Law 2, reflexive.** -/
  refl : ∀ (kind : UInt8) (index : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind index] = some (Val.bool true)
  /-- **Law 2, symmetric.** -/
  symm : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      NativeAtom.eval .sameHandle [.handle kind' index', .handle kind index]
  /-- **Law 3, the allocation.** The cell that `refMake` answers is undeclared before it. -/
  allocRef : ∀ (w : World), CellsTyped w → ∀ (value : Val) (state : Stores) (key : RefKey),
    syncOpStep (.refMake value) w.state = some (state, Val.cell key) → w.Ρ key = none
  /-- The same for `deferredMake`. -/
  allocDeferred : ∀ (w : World), CellsTyped w → ∀ (state : Stores) (key : DeferredKey),
    syncOpStep .deferredMake w.state = some (state, Val.promise key) → w.«Π» key = none
  /-- **Law 3, a fresh cell.** It is the same handle as no handle of a value that fits the
  earlier world. -/
  freshRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.cell key, .handle kind index] ≠ some (Val.bool true)
  /-- The same for a fresh Deferred cell. -/
  freshDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.promise key, .handle kind index] ≠ some (Val.bool true)
  /-- **Law 3, a stored list.** A fresh cell is a member of no stored list of cells. -/
  notMemberRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (A : Ty),
    Fits w v (.list (.refOf A)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.cell key, x] = some (Val.bool false)
  /-- The same for a fresh Deferred cell. -/
  notMemberDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none →
    ∀ (v : Val) (A E : Ty), Fits w v (.list (.deferredOf A E)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.promise key, x] = some (Val.bool false)
  /-- **Law 4.** A later world keeps a list's membership and each element's. The test reads no
  world (`eval`), so a later world keeps every answer. -/
  later : ∀ (w w' : World), w.leHost w' → ∀ (v : Val) (H : Ty), Fits w v (.list H) →
    Fits w' v (.list H) ∧ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w' x H
  /-- **Law 5.** The handles of a term's answer are handles of its environment, a fold's
  answer included. It needs successful evaluation and no typing. -/
  contained : ∀ (term : Term) (env : List Val) (v : Val), evalTerm env term = some v →
    Store.Val.handles v ⊆ env.flatMap Store.Val.handles

/-- **The laws of a handle's identity hold** (the claim `handle-identity-laws`). Each field is
one theorem: `sameHandle_eval`, the two totality theorems, `sameHandle_refl`,
`sameHandle_symm`, the two allocation facts, the two freshness theorems and their two list
forms, `list_later`, and `RawHandles.evalTerm_handles` with its fold case.

It establishes no correspondence in a target: that two handles have equal keys exactly when
their host objects are one object is each target's relation. Its consumer is the Queue's
withdrawal by identity (decisions row 229). -/
@[semantics "store-typing" (requirement := R4)]
theorem handle_identity_laws : HandleIdentityLaws where
  eval := sameHandle_eval
  totalRef := fun _ _ _ _ _ ha hb => sameHandle_total_ref ha hb
  totalDeferred := fun _ _ _ _ _ _ _ ha hb => sameHandle_total_deferred ha hb
  refl := sameHandle_refl
  symm := sameHandle_symm
  allocRef := fun _ cells _ _ _ step => refMake_fresh cells step
  allocDeferred := fun _ cells _ _ step => deferredMake_fresh cells step
  freshRef := fun _ _ fresh _ _ hv kind index hmem => sameHandle_fresh_cell fresh hv kind index hmem
  freshDeferred := fun _ _ fresh _ _ hv kind index hmem =>
    sameHandle_fresh_promise fresh hv kind index hmem
  notMemberRef := fun _ _ fresh _ _ hv => fresh_cell_not_member fresh hv
  notMemberDeferred := fun _ _ fresh _ _ _ hv => fresh_promise_not_member fresh hv
  later := fun _ _ ord _ _ hv => list_later ord hv
  contained := RawHandles.evalTerm_handles

end Effect4.Program.Typed
