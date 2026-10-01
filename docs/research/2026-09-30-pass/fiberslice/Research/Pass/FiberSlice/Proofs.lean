import Research.Pass.FiberSlice.Core
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.TypeAlgebra

/-! Task 3: the slice's theorems that hold of the runtime check alone, proved on the prototype.
None depends on M6 or DI-57: they are about the executable admission and the session steps.
Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false

namespace Research.Pass.FiberSlice.Proofs
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Effect4.Api.HostSession (Session Result Reply Key BoundCall readReply)

/-! ## 1. The connector: the new admission is the old one plus a clause -/

/-- The prototype refuses whatever the old admission refuses, with the same reason. -/
theorem admitD_of_admit (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (d : NativeDecision) (why : Refusal) (h : admit table m d = some why) :
    admitD program table m d = some (.admit why) := by
  unfold admitD
  rw [h]

/-- What the prototype admits, the old admission admits. -/
theorem admit_of_admitD (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (d : NativeDecision) (h : admitD program table m d = none) : admit table m d = none := by
  cases hold : admit table m d with
  | none => rfl
  | some why =>
    rw [admitD_of_admit program table m d why hold] at h
    cases h

theorem envelope_of_envelopeD (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (h : EnvelopeD program table m r) : Envelope table m r :=
  ⟨h.1, h.2.1, admit_of_admitD program table m _ h.2.2⟩

/-- An accepted reply is accepted by the old check, with the same decision. -/
theorem acceptReply_of_acceptReplyD (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (d : NativeDecision) (h : acceptReplyD program table m r = some d) :
    acceptReply table m r = some d := by
  unfold acceptReplyD at h
  split at h
  · rename_i henv
    rw [acceptReply_of_envelope table m r (envelope_of_envelopeD program table m r henv)]
    exact h
  · cases h

theorem envelopeD_of_acceptReplyD (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (d : NativeDecision) (h : acceptReplyD program table m r = some d) :
    EnvelopeD program table m r ∧ d = .answerAsync r.fiber r.token r.completion := by
  unfold acceptReplyD at h
  split at h
  · rename_i henv
    exact ⟨henv, (Option.some.inj h).symm⟩
  · cases h

/-- At most once, carried over: once the old check refuses (the park is gone), so does the
prototype. -/
theorem acceptReplyD_none_of_acceptReply (program : NativeEff) (table : RowTable)
    (m : NativeMachine) (r : RecordedReply) (h : acceptReply table m r = none) :
    acceptReplyD program table m r = none := by
  cases hd : acceptReplyD program table m r with
  | none => rfl
  | some d =>
    rw [acceptReply_of_acceptReplyD program table m r d hd] at h
    cases h

/-! ## 2. Receipt: an accepted submit establishes the envelope at the receipt state -/

theorem preflightD_envelope {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : preflightD s reply = .ok decision) :
    ∃ bound, s.active.find? (fun b => b.key == reply.key) = some bound ∧
      reply.callId = bound.call.callId ∧
      EnvelopeD program table s.machine (bound.record reply) ∧
      decision = .answerAsync bound.call.fiber bound.token reply.completion := by
  unfold preflightD at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i bound hfind
        split at h
        · cases h
        · rename_i hcall
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i d hd
              obtain ⟨henv, rfl⟩ := envelopeD_of_acceptReplyD program table s.machine _ d hd
              refine ⟨bound, hfind, Decidable.of_not_not hcall, henv, ?_⟩
              cases h
              rfl

theorem submitD_receipt {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (h : (submitD s reply).phase = .preflight) :
    ∃ bound, s.active.find? (fun b => b.key == reply.key) = some bound ∧
      EnvelopeD program table s.machine (bound.record reply) := by
  unfold submitD at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i decision hpre
      obtain ⟨bound, hfind, _, henv, _⟩ := preflightD_envelope s reply decision hpre
      exact ⟨bound, hfind, henv⟩

/-- Receipt stores and does not run: the machine is unchanged by an accepted submit. -/
theorem submitD_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) : (submitD s reply).session.machine = s.machine := by
  unfold submitD
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rfl

/-! ## 3. Application: an applied reply was admitted at the application-time machine

`applyReplyD` re-runs the whole preflight on the stored reply against the machine it is about to
step, so the envelope (with the declaration clause) holds at application time, not only at
receipt: unrelated allocation between the two cannot smuggle a stale verdict in. -/

theorem applyReplyD_applied {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (applyReplyD s key fuel).phase = .applied) :
    ∃ reply bound, readReply s.pending key = some reply ∧
      s.active.find? (fun b => b.key == reply.key) = some bound ∧
      EnvelopeD program table s.machine (bound.record reply) := by
  unfold applyReplyD at h
  split at h
  · cases h
  · split at h
    · rename_i _ reply _ hread
      split at h
      · cases h
      · rename_i decision hpre
        obtain ⟨bound', hfind', _, henv, _⟩ := preflightD_envelope s reply decision hpre
        exact ⟨reply, bound', hread, hfind', henv⟩
    · cases h

/-! ## 4. The combined judgment against the old shape check -/

theorem firstRefusal_none {α : Type} (f : α → Nat → Option FitRefusal) :
    ∀ (xs : List α) (i : Nat), firstRefusal f xs i = none → ∀ x ∈ xs, ∃ j, f x j = none
  | [], _, _, x, hx => nomatch hx
  | y :: ys, i, h, x, hx => by
    unfold firstRefusal at h
    split at h
    · cases h
    · rename_i hy
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨i, hy⟩
      · exact firstRefusal_none f ys (i + 1) h x hx

/-- The connector in the direction that holds: what the combined judgment admits has the old
judgment's shape. The converse is false (the forged fiber). -/
theorem fitsAt_hasTy (decl : FiberId → Option EffTy) (allocated : List String) :
    ∀ (ty : Ty) (p : List Nat) (v : Val), fitsAt decl allocated p v ty = none →
      Val.hasTy v ty allocated = true := by
  intro ty
  induction ty with
  | fiberOf a e =>
    intro p v h
    unfold fitsAt at h
    split at h
    · simp only [Val.hasTy]
    · cases h
  | option inner ih =>
    intro p v h
    unfold fitsAt at h
    split at h
    · simp only [Val.hasTy]
    · rename_i x
      simp only [Val.hasTy]
      exact ih _ _ h
    · cases h
  | prod ta tb iha ihb =>
    intro p v h
    unfold fitsAt at h
    split at h
    · rename_i x y
      split at h
      · cases h
      · rename_i hx
        simp only [Val.hasTy, Bool.and_eq_true]
        exact ⟨iha _ _ hx, ihb _ _ h⟩
    · cases h
  | except error value ihe ihv =>
    intro p v h
    unfold fitsAt at h
    split at h
    · simp only [Val.hasTy]
      exact ihe _ _ h
    · simp only [Val.hasTy]
      exact ihv _ _ h
    · cases h
  | exitOf a e iha ihe =>
    intro p v h
    unfold fitsAt at h
    split at h
    · simp only [Val.hasTy]
      exact iha _ _ h
    · split at h
      · assumption
      · cases h
    · cases h
  | list inner ih =>
    intro p v h
    unfold fitsAt at h
    split at h
    · rename_i hs
      split at h
      · rename_i ids hids
        have hall := firstRefusal_none _ ids 0 h
        simp only [Val.hasTy, hids, List.all_eq_true]
        intro id hid
        obtain ⟨j, hj⟩ := hall id hid
        exact ih _ _ hj
      · cases h
    · rename_i values
      have hall := firstRefusal_none _ values 0 h
      simp only [Val.hasTy, List.all_eq_true]
      intro x hx
      obtain ⟨j, hj⟩ := hall x hx
      exact ih _ _ hj
    · cases h
  | union l r ihl ihr =>
    intro p v h
    unfold fitsAt at h
    split at h
    · rename_i hl
      simp only [Val.hasTy, Bool.or_eq_true]
      exact Or.inl (ihl _ _ hl)
    · split at h
      · rename_i hr
        simp only [Val.hasTy, Bool.or_eq_true]
        exact Or.inr (ihr _ _ hr)
      · cases h
  | never | unit | nat | int | string | bool | handle _ | causeOf _ | lit _ | refOf _
  | deferredOf _ _ | var _ | unknown =>
    intro p v h
    unfold fitsAt at h
    split at h
    · assumption
    · cases h

theorem fits_hasTy (decl : FiberId → Option EffTy) (allocated : List String) (v : Val) (ty : Ty)
    (h : fits decl allocated v ty = true) : Val.hasTy v ty allocated = true :=
  fitsAt_hasTy decl allocated ty [] v (Option.isNone_iff_eq_none.mp h)

/-- The fiber clause, exactly: a value fits `fiberOf a e` when it is a fiber handle whose
declaration fits by covariance; an undeclared fiber only at the top. -/
theorem fitsAt_fiberOf (decl : FiberId → Option EffTy) (allocated : List String) (p : List Nat)
    (v : Val) (a e : Ty) :
    fitsAt decl allocated p v (.fiberOf a e) = none ↔
      ∃ id, v = Value.fiber id ∧ declFits (decl ⟨id⟩) a e = true := by
  constructor
  · intro h
    unfold fitsAt at h
    split at h
    · rename_i id
      split at h
      · rename_i hd
        exact ⟨id, rfl, hd⟩
      · cases h
    · cases h
  · rintro ⟨id, rfl, hd⟩
    unfold fitsAt
    simp only [hd, if_true]

/-! ## 5. Nothing else changes: on fiber-free values the combined judgment is the old one -/

/-- No handle of the fiber kind anywhere in the value. -/
def noFiber (v : Val) : Bool := (Store.Val.handles v).all fun h => h.1 != 1

theorem noFiber_some (x : Val) (h : noFiber (.some x) = true) : noFiber x = true := h

theorem noFiber_of_mem_list (xs : List Val) (h : noFiber (.list xs) = true) :
    ∀ x ∈ xs, noFiber x = true := by
  intro x hx
  unfold noFiber at h ⊢
  have hl : Store.Val.handles (.list xs) = xs.flatMap Store.Val.handles := by
    show Store.Val.handlesList xs = _
    exact Store.Val.handlesList_eq_flatMap xs
  rw [hl, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro k hk
  exact h k (List.mem_flatMap.mpr ⟨x, hx, hk⟩)

theorem noFiber_of_mem_ctor (i : Nat) (xs : List Val) (h : noFiber (.ctor i xs) = true) :
    ∀ x ∈ xs, noFiber x = true := by
  intro x hx
  unfold noFiber at h ⊢
  have hl : Store.Val.handles (.ctor i xs) = xs.flatMap Store.Val.handles := by
    show Store.Val.handlesList xs = _
    exact Store.Val.handlesList_eq_flatMap xs
  rw [hl, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro k hk
  exact h k (List.mem_flatMap.mpr ⟨x, hx, hk⟩)

theorem noFiber_fiber (n : Nat) : noFiber (Value.fiber n) = false := rfl

/-- A fiber-free snapshot names no fiber. -/
theorem snapshot_nil_of_noFiber (hs : Val) (ids : List FiberId)
    (hsnap : Val.snapshot? (Value.fiberSnapshot hs) = some ids)
    (h : noFiber (Value.fiberSnapshot hs) = true) : ids = [] := by
  have hexact : hs = (Store.Image.list Value.fiberHandle).toVal ids :=
    (Store.Image.list Value.fiberHandle).ofVal_exact hsnap
  cases ids with
  | nil => rfl
  | cons id rest =>
    exfalso
    have hmem : Value.fiber id.value ∈ (id :: rest).map Value.fiberHandle.toVal :=
      List.mem_map.mpr ⟨id, List.mem_cons_self, rfl⟩
    have hhs : noFiber hs = true := noFiber_of_mem_ctor 3 [hs] h hs List.mem_cons_self
    rw [hexact] at hhs
    have hin : ∀ x ∈ (id :: rest).map Value.fiberHandle.toVal, noFiber x = true :=
      noFiber_of_mem_list _ hhs
    have := hin _ hmem
    rw [noFiber_fiber] at this
    cases this

theorem firstRefusal_of_all_none {α : Type} (f : α → Nat → Option FitRefusal) :
    ∀ (xs : List α) (i : Nat), (∀ x ∈ xs, ∀ j, f x j = none) → firstRefusal f xs i = none
  | [], _, _ => rfl
  | y :: ys, i, h => by
    unfold firstRefusal
    rw [h y List.mem_cons_self i]
    exact firstRefusal_of_all_none f ys (i + 1) fun x hx j => h x (List.mem_cons_of_mem y hx) j

/-- On a value with no fiber handle, the combined judgment admits whatever the old one admits,
whatever the registry says. With `fitsAt_hasTy` the two agree exactly there. -/
theorem fitsAt_none_of_hasTy (decl : FiberId → Option EffTy) (allocated : List String) :
    ∀ (ty : Ty) (p : List Nat) (v : Val), Val.hasTy v ty allocated = true → noFiber v = true →
      fitsAt decl allocated p v ty = none := by
  intro ty
  induction ty with
  | fiberOf a e =>
    intro p v hty hnf
    unfold Val.hasTy at hty
    split at hty
    · rename_i n
      rw [noFiber_fiber] at hnf
      cases hnf
    · cases hty
  | option inner ih =>
    intro p v hty hnf
    unfold fitsAt
    unfold Val.hasTy at hty
    split at hty
    · rfl
    · rename_i x
      exact ih _ _ hty (noFiber_some x hnf)
    · cases hty
  | prod ta tb iha ihb =>
    intro p v hty hnf
    unfold fitsAt
    unfold Val.hasTy at hty
    split at hty
    · rename_i x y
      rw [Bool.and_eq_true] at hty
      have hx := noFiber_of_mem_list _ hnf x List.mem_cons_self
      have hy := noFiber_of_mem_list _ hnf y (List.mem_cons_of_mem x List.mem_cons_self)
      simp only [iha _ _ hty.1 hx, ihb _ _ hty.2 hy]
    · cases hty
  | except error value ihe ihv =>
    intro p v hty hnf
    unfold fitsAt
    unfold Val.hasTy at hty
    split at hty
    · rename_i err
      exact ihe _ _ hty (noFiber_of_mem_ctor 0 [err] hnf err List.mem_cons_self)
    · rename_i val
      exact ihv _ _ hty (noFiber_of_mem_ctor 1 [val] hnf val List.mem_cons_self)
    · cases hty
  | exitOf a e iha ihe =>
    intro p v hty hnf
    unfold Val.hasTy at hty
    split at hty
    · rename_i x
      simp only [fitsAt]
      exact iha _ _ hty (noFiber_of_mem_ctor 0 [x] hnf x List.mem_cons_self)
    · rename_i written
      have hfull : Val.hasTy (.ctor 1 [written]) (.exitOf a e) allocated = true := by
        simp only [Val.hasTy]
        exact hty
      simp only [fitsAt, hfull, if_true]
    · cases hty
  | list inner ih =>
    intro p v hty hnf
    unfold fitsAt
    unfold Val.hasTy at hty
    split at hty
    · rename_i hs
      split at hty
      · rename_i ids hids
        rw [hids, snapshot_nil_of_noFiber hs ids hids hnf]
        rfl
      · cases hty
    · rename_i values
      apply firstRefusal_of_all_none
      intro x hx j
      rw [List.all_eq_true] at hty
      exact ih _ _ (hty x hx) (noFiber_of_mem_list values hnf x hx)
    · cases hty
  | union l r ihl ihr =>
    intro p v hty hnf
    unfold Val.hasTy at hty
    rw [Bool.or_eq_true] at hty
    unfold fitsAt
    rcases hty with hl | hr
    · rw [ihl _ _ hl hnf]
    · rw [ihr _ _ hr hnf]
      split
      · rfl
      · rfl
  | never | unit | nat | int | string | bool | handle _ | causeOf _ | lit _ | refOf _
  | deferredOf _ _ | var _ | unknown =>
    intro p v hty _
    unfold fitsAt
    simp only [hty, if_true]

/-! ## 6. The admission: exact agreement off fibers, membership at receipt -/

/-- The declaration clause is the only difference: when the old check admits, the prototype
answers the clause's refusal. -/
theorem admitD_of_admit_none (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (h : admit table m (.answerAsync fiber token answer) = none) :
    admitD program table m (.answerAsync fiber token answer) =
      (declClause program table m (.answerAsync fiber token answer)).map
        (.handleDecl fiber token) := by
  unfold admitD
  rw [h]

/-- A prepared value is the host's value or a fresh external handle. -/
theorem externalValue_result (ty : Ty) (allocated allocated' : List String) (value result : Val)
    (h : externalValue ty allocated value = some (allocated', result)) :
    result = value ∨ ∃ index, result = Value.external index := by
  unfold externalValue at h
  split at h
  · split at h
    · rename_i index _
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Or.inr ⟨index, rfl⟩
    · cases h
  · split at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Or.inl rfl
    · cases h

theorem noFiber_prepared (ty : Ty) (allocated allocated' : List String) (value result : Val)
    (h : externalValue ty allocated value = some (allocated', result))
    (hv : noFiber value = true) : noFiber result = true := by
  rcases externalValue_result ty allocated allocated' value result h with rfl | ⟨index, rfl⟩
  · exact hv
  · rfl

/-- An answer the declaration clause cannot touch: no fiber handle in a success value, or in the
delayed cell's present contents. -/
def AnswerFiberFree (m : NativeMachine) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit (.success v) => noFiber v = true
  | .ofExit (.failure _) => True
  | .ofRefGet cell => ∀ v, m.state.refs[cell.index]? = some v → noFiber v = true

/-- **Nothing else changes.** On an answer with no fiber handle the prototype's verdict is the
old one, refusal reason included. -/
theorem admitD_eq_of_fiberFree (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (hfree : AnswerFiberFree m answer) :
    admitD program table m (.answerAsync fiber token answer) =
      (admit table m (.answerAsync fiber token answer)).map .admit := by
  cases hold : admit table m (.answerAsync fiber token answer) with
  | some why => exact admitD_of_admit program table m _ why hold
  | none =>
    rw [admitD_of_admit_none program table m fiber token answer hold]
    obtain ⟨i, request, row, hreq, hrow, hans⟩ := admitted_row table m fiber token answer hold
    show Option.map _ (declClause program table m (.answerAsync fiber token answer)) = none
    simp only [declClause, hreq, hrow]
    cases answer with
    | ofExit ex =>
      cases ex with
      | success v =>
        cases hv : externalValue row.answer m.state.externals.allocated v with
        | none => simp only [admitAnswer, hv, Option.isNone_none, if_true, reduceCtorEq] at hans
        | some converted =>
          obtain ⟨allocated, result⟩ := converted
          have htyped := externalValue_typed _ _ _ _ _ hv
          have hnf := noFiber_prepared _ _ _ _ _ hv hfree
          simp only [hv, fitsAt_none_of_hasTy _ allocated row.answer [] result htyped hnf,
            Option.map_none]
      | failure c => rfl
    | ofRefGet cell =>
      cases hc : m.state.refs[cell.index]? with
      | none => simp only [admitAnswer, hc, reduceCtorEq] at hans
      | some v =>
        have htyped : Val.hasTy v row.answer m.state.externals.allocated = true := by
          cases hb : Val.hasTy v row.answer m.state.externals.allocated with
          | true => rfl
          | false => simp only [admitAnswer, hc, hb, Bool.not_false, if_true, reduceCtorEq] at hans
        simp only [hc, fitsAt_none_of_hasTy _ _ row.answer [] v htyped (hfree v hc),
          Option.map_none]

/-- **Membership at receipt.** An accepted envelope's success value, prepared in the extended
allocation table, fits the row's answer type under the derived fiber declarations. -/
theorem envelopeD_fits (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (v : Val) (henv : EnvelopeD program table m r)
    (hc : r.completion = .ofExit (.success v)) :
    ∃ i row allocated prepared, r.op = .external i ∧
      requestOf m r.fiber r.token = some (r.op, r.request) ∧
      externalRow table i = some row ∧
      externalValue row.answer m.state.externals.allocated v = some (allocated, prepared) ∧
      fits (fiberDecl (nativeSignature table) program m) allocated prepared row.answer = true := by
  obtain ⟨_, hreq, hadm⟩ := henv
  rw [hc] at hadm
  have hold := admit_of_admitD program table m _ hadm
  obtain ⟨i, request, row, allocated, prepared, hreq', hrow, hext, _⟩ :=
    external_answer_typed table m r.fiber r.token v hold
  rw [hreq] at hreq'
  obtain ⟨hop, _⟩ := Prod.mk.inj (Option.some.inj hreq')
  refine ⟨i, row, allocated, prepared, hop, hreq, hrow, hext, ?_⟩
  rw [admitD_of_admit_none program table m r.fiber r.token _ hold] at hadm
  cases hcl : declClause program table m (.answerAsync r.fiber r.token (.ofExit (.success v))) with
  | some why =>
    rw [hcl] at hadm
    cases hadm
  | none =>
    rw [hop] at hreq
    simp only [declClause, hreq, hrow, hext] at hcl
    exact Option.isNone_iff_eq_none.mpr hcl

/-! ## 7. Toward the typed guarantee: the check transfers to any narrower fiber table

`fitsAt` is parametric in the declaration table, and the proof world's `Γ` has the same type
(`Laws/Program/Typed/World.lean:48`). So "the runtime check implies the proof world's fiber
clause" is a monotonicity statement, proved here; its one premise — the world's declarations are
at most the registry's — is the fiber part of `RegistryAgrees`, which the typed state (M6) owes. -/

/-- A table at most as wide as the registry at every declared fiber. -/
def Narrower (Γ decl : FiberId → Option EffTy) : Prop :=
  ∀ id d, decl id = some d →
    ∃ g, Γ id = some g ∧ g.answer.sub d.answer = true ∧ g.error.sub d.error = true

theorem declFits_narrower (x y : Option EffTy) (a e : Ty)
    (hxy : ∀ d, x = some d →
      ∃ g, y = some g ∧ g.answer.sub d.answer = true ∧ g.error.sub d.error = true)
    (h : declFits x a e = true) : declFits y a e = true := by
  cases x with
  | some d =>
    obtain ⟨g, rfl, ha, he⟩ := hxy d rfl
    simp only [declFits, Bool.and_eq_true] at h ⊢
    exact ⟨Ty.sub_trans _ _ _ ha h.1, Ty.sub_trans _ _ _ he h.2⟩
  | none =>
    cases y with
    | none => exact h
    | some g =>
      simp only [declFits, Bool.and_eq_true] at h ⊢
      exact ⟨Ty.sub_trans _ _ _ (Ty.sub_unknown _) h.1, Ty.sub_trans _ _ _ (Ty.sub_unknown _) h.2⟩

/-- What fits under the registry fits under every narrower table (the refusal's location is
free: only the verdict is compared). -/
theorem fitsAt_narrower (decl Γ : FiberId → Option EffTy) (allocated : List String)
    (hn : Narrower Γ decl) :
    ∀ (ty : Ty) (p q : List Nat) (v : Val), fitsAt decl allocated p v ty = none →
      fitsAt Γ allocated q v ty = none := by
  intro ty
  induction ty with
  | fiberOf a e =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · rename_i id
      split at h
      · rename_i hd
        have hg : declFits (Γ ⟨id⟩) a e = true :=
          declFits_narrower _ _ a e (fun d hd' => hn ⟨id⟩ d hd') hd
        simp only [fitsAt, hg, if_true]
      · cases h
    · cases h
  | option inner ih =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · simp only [fitsAt]
    · rename_i x
      have hx := ih _ (q ++ [0]) _ h
      simp only [fitsAt, hx]
    · cases h
  | prod ta tb iha ihb =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · split at h
      · cases h
      · rename_i x y _ hx
        have hx' := iha _ (q ++ [0]) _ hx
        have hy' := ihb _ (q ++ [1]) _ h
        simp only [fitsAt, hx', hy']
    · cases h
  | except error value ihe ihv =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · rename_i err
      have he := ihe _ (q ++ [0]) _ h
      simp only [fitsAt, he]
    · rename_i val
      have hv := ihv _ (q ++ [0]) _ h
      simp only [fitsAt, hv]
    · cases h
  | exitOf a e iha ihe =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · rename_i x
      have hx := iha _ (q ++ [0]) _ h
      simp only [fitsAt, hx]
    · rename_i w
      split at h
      · rename_i hw
        simp only [fitsAt, hw, if_true]
      · cases h
    · cases h
  | list inner ih =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · rename_i hs
      split at h
      · rename_i ids hids
        have hall : ∀ id ∈ ids, ∀ j,
            fitsAt Γ allocated (q ++ [0, j]) (Value.fiber id.value) inner = none := by
          intro id hid j
          obtain ⟨k, hk⟩ := firstRefusal_none _ ids 0 h id hid
          exact ih _ _ _ hk
        simp only [fitsAt, hids]
        exact firstRefusal_of_all_none _ ids 0 hall
      · cases h
    · rename_i values
      have hall : ∀ x ∈ values, ∀ j, fitsAt Γ allocated (q ++ [j]) x inner = none := by
        intro x hx j
        obtain ⟨k, hk⟩ := firstRefusal_none _ _ 0 h x hx
        exact ih _ _ _ hk
      simp only [fitsAt]
      exact firstRefusal_of_all_none _ values 0 hall
    · cases h
  | union l r ihl ihr =>
    intro p q v h
    unfold fitsAt at h
    split at h
    · rename_i hl
      have hl' := ihl _ q _ hl
      simp only [fitsAt, hl']
    · split at h
      · rename_i hr
        have hr' := ihr _ q _ hr
        simp only [fitsAt, hr']
        split
        · rfl
        · rfl
      · cases h
  | never | unit | nat | int | string | bool | handle _ | causeOf _ | lit _ | refOf _
  | deferredOf _ _ | var _ | unknown =>
    intro p q v h
    unfold fitsAt at h ⊢
    split at h
    · rename_i hty
      rw [if_pos hty]
    · cases h

theorem fits_narrower (decl Γ : FiberId → Option EffTy) (allocated : List String)
    (hn : Narrower Γ decl) (v : Val) (ty : Ty) (h : fits decl allocated v ty = true) :
    fits Γ allocated v ty = true :=
  Option.isNone_iff_eq_none.mpr
    (fitsAt_narrower decl Γ allocated hn ty [] [] v (Option.isNone_iff_eq_none.mp h))

/-- **Receipt membership in the proof world's terms.** Given the fiber part of
`RegistryAgrees` for a table `Γ` (the one M6-dependent premise), an accepted success value fits
the row's answer type under `Γ` itself. -/
theorem envelopeD_fits_table (program : NativeEff) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) (v : Val) (Γ : FiberId → Option EffTy)
    (hagree : Narrower Γ (fiberDecl (nativeSignature table) program m))
    (henv : EnvelopeD program table m r) (hc : r.completion = .ofExit (.success v)) :
    ∃ i row allocated prepared, r.op = .external i ∧
      requestOf m r.fiber r.token = some (r.op, r.request) ∧
      externalRow table i = some row ∧
      externalValue row.answer m.state.externals.allocated v = some (allocated, prepared) ∧
      fits Γ allocated prepared row.answer = true := by
  obtain ⟨i, row, allocated, prepared, hop, hreq, hrow, hext, hfits⟩ :=
    envelopeD_fits program table m r v henv hc
  exact ⟨i, row, allocated, prepared, hop, hreq, hrow, hext,
    fits_narrower _ Γ allocated hagree prepared row.answer hfits⟩

/-! ## 8. Declarations move only with origins

A fiber's declaration reads only its origin record and the program, so two machines that agree
on every fiber's origin agree on every declaration. That origins never change and fibers are
never removed is the origin ledger's lookup contract (its user 2), not proved here. -/

theorem fiberDecl_congr (sig : Signature NativeOp) (root : NativeEff) (m m' : NativeMachine)
    (h : ∀ id, (m.fiber? id).map (·.origin) = (m'.fiber? id).map (·.origin)) (id : FiberId) :
    fiberDecl sig root m id = fiberDecl sig root m' id := by
  have hid := h id
  unfold fiberDecl
  cases hm : m.fiber? id with
  | none =>
    cases hm' : m'.fiber? id with
    | none => rfl
    | some f' =>
      rw [hm, hm'] at hid
      cases hid
  | some f =>
    cases hm' : m'.fiber? id with
    | none =>
      rw [hm, hm'] at hid
      cases hid
    | some f' =>
      rw [hm, hm'] at hid
      simp only [Option.map_some, Option.some.injEq] at hid
      simp only [hid]

#print axioms admitD_of_admit
#print axioms admit_of_admitD
#print axioms envelope_of_envelopeD
#print axioms acceptReply_of_acceptReplyD
#print axioms envelopeD_of_acceptReplyD
#print axioms acceptReplyD_none_of_acceptReply
#print axioms preflightD_envelope
#print axioms submitD_receipt
#print axioms submitD_machine
#print axioms applyReplyD_applied
#print axioms firstRefusal_none
#print axioms fitsAt_hasTy
#print axioms fits_hasTy
#print axioms fitsAt_fiberOf
#print axioms noFiber_some
#print axioms noFiber_of_mem_list
#print axioms noFiber_of_mem_ctor
#print axioms noFiber_fiber
#print axioms snapshot_nil_of_noFiber
#print axioms firstRefusal_of_all_none
#print axioms fitsAt_none_of_hasTy
#print axioms admitD_of_admit_none
#print axioms externalValue_result
#print axioms noFiber_prepared
#print axioms admitD_eq_of_fiberFree
#print axioms envelopeD_fits
#print axioms declFits_narrower
#print axioms fitsAt_narrower
#print axioms fits_narrower
#print axioms envelopeD_fits_table
#print axioms fiberDecl_congr

end Research.Pass.FiberSlice.Proofs
