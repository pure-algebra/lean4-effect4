import Effect4.Program.AdmitIn
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.TyDecls

/-!
# Laws of reply admission under a declaration table

The readers are `Program/AdmitIn.lean`'s; the plan is
`docs/research/2026-10-16-usability-scope/wiring-plan.md`, increment W2b.

- **Conservativity** (`wiring_admission_conservative`): at the empty table each reader is its
  original, by definition, so every law of `Laws/Program/Admit.lean` holds there unchanged.
- **Data or one allocation** (`externalValueIn_internalFree`): an accepted conversion keeps the
  value and the allocation table, or mints exactly the next external handle at a handle column.
  A handle column names no declared type: the signature refuses it (decisions row 406 (1)).
- **An admitted success is a member** (`external_answer_typedIn`): the converted value is a member
  of the parked row's answer column under the table, in the resulting allocation table.
- **An admitted failure fits** (`external_error_typedIn`): each typed failure's value is a member
  of the row's error column under the table, and no reason dies with a reserved defect
  (`admitIn_failure_reservedFree`).

Placement of the claims (`AGENTS.md`, five points), shared by every theorem below:

1. Concept `host-session-protocol` (reply admission), with `store-typing`'s judgment
   (membership under a table), of `docs/core/semantics.md`. Property: an admitted reply is a
   member of its row's columns, and the empty table changes no admission.
2. Questions: the proposed registry claims `wiring-admission-conservative`
   (`wiring_admission_conservative`, compatibility), `wiring-admission-sound`
   (`external_answer_typedIn`, preservation) and `wiring-no-allocation-at-name`
   (`externalValueIn_internalFree`, safety).
3. Reach: one decision at one parked call; `MemberIn` at the prepared allocation table. Decisions
   rows 191, 400 and 406 (1) bound it.
4. Does not establish: `AnswerOk` or `Fits`; anything of the machine's preparation, which still
   reads the row's column with no table (`prepareExternalAnswer`); any session law. No caller
   reads these readers yet.
5. Unlocks: the session's reply check under a table (the plan's W4); R6's host lane at declared
   types.
-/

set_option autoImplicit false

namespace Effect4.Program
open Effect4 Effect4.Machine

/-! ## At the empty table each reader is its original -/

/-- **Conservativity** (the claim `wiring-admission-conservative`): at the empty table the
conversion, the error check, the answer check, the decision check,
the recorded reply, the instance check and the row protocol's check are their originals, by
definition. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem wiring_admission_conservative :
    (∀ (ty : Ty) (allocated : List String) (v : Val),
      externalValueIn [] ty allocated v = externalValue ty allocated v) ∧
    (∀ ty : Ty, errAdmitsIn [] ty = errAdmits ty) ∧
    (∀ (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat)
        (answer : Completion Val Err Defect FiberId Ann),
      admitAnswerIn [] row m fiber token answer = admitAnswer row m fiber token answer) ∧
    (∀ (table : RowTable) (m : NativeMachine) (d : NativeDecision),
      admitIn [] table m d = admit table m d) ∧
    (∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
      acceptReplyIn [] table m r = acceptReply table m r) ∧
    (∀ (c : CallInstance NativeOp) (m : NativeMachine) (fiber : FiberId) (token : Nat)
        (answer : Completion Val Err Defect FiberId Ann),
      admitInstanceIn [] c m fiber token answer = admitInstance c m fiber token answer) ∧
    (∀ (table : RowTable) (instanceAt : List Nat → Option (CallInstance NativeOp))
        (m : NativeMachine) (r : RecordedReply),
      acceptAtInstanceIn [] table instanceAt m r = acceptAtInstance table instanceAt m r) ∧
    (∀ (table : RowTable) (i : Nat) (answer : Completion Val Err Defect FiberId Ann)
        (allocated : List String),
      externalAdmitsIn [] table i answer allocated = externalAdmits table i answer allocated) :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-! ## The conversion -/

/-- A host handle is no reference, so no table unfolds it (decisions row 406 (1)). -/
theorem TyDecls.unfold?_handle (decls : TyDecls) (n : String) : decls.unfold? (.handle n) = none :=
  rfl

/-- A data conversion keeps the value and the allocation table, and the value is a member that
holds no handle. -/
theorem dataValueIn_some {decls : TyDecls} {ty : Ty} {allocated allocated' : List String}
    {value result : Val} (h : dataValueIn decls ty allocated value = some (allocated', result)) :
    allocated' = allocated ∧ result = value ∧ result.handles = [] ∧
      MemberIn decls allocated' result ty := by
  unfold dataValueIn at h
  split at h
  · rename_i ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hm, hf⟩ := Bool.and_eq_true_iff.mp ha
    exact ⟨rfl, rfl, List.isEmpty_iff.mp hf, hasTyIn_iff.mp hm⟩
  · cases h

/-- **Data or one allocation** (the claim `wiring-no-allocation-at-name`, decisions row 406 (1)):
an accepted conversion keeps a handle-free value and the allocation table, or mints exactly the
external handle at the next index of a handle column. A declared name's column is `app n []`, so
its value is data; the signature refuses a handle at a declared name. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem externalValueIn_internalFree {decls : TyDecls} {ty : Ty}
    {allocated allocated' : List String} {value result : Val}
    (h : externalValueIn decls ty allocated value = some (allocated', result)) :
    (allocated' = allocated ∧ result = value ∧ result.handles = []) ∨
      ∃ target, ty = .handle target ∧
        externalHandleTarget target = true ∧ value = .nat allocated.length ∧
        allocated' = allocated ++ [target] ∧ result = Value.external allocated.length := by
  cases decls with
  | nil =>
    rcases externalValue_internalFree ty allocated allocated' value result h with
      hd | ⟨target, h1, h2, h3, h4, h5⟩
    · exact Or.inl hd
    · exact Or.inr ⟨target, h1, h2, h3, h4, h5⟩
  | cons d ds =>
    simp only [externalValueIn] at h
    split at h
    · rename_i target index
      split at h
      · rename_i ha
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨ht, hi⟩ := Bool.and_eq_true_iff.mp ha
        have hi : index = allocated.length := beq_iff_eq.mp hi
        subst hi
        exact Or.inr ⟨target, rfl, ht, rfl, rfl, rfl⟩
      · cases h
    · obtain ⟨h1, h2, h3, _⟩ := dataValueIn_some h
      exact Or.inl ⟨h1, h2, h3⟩

/-- **A conversion under a table returns a member** of the column under the table, in the
resulting allocation table. A minted handle is a member of its handle column, as
`externalValue_typed` shows for the original. -/
theorem externalValueIn_typed {decls : TyDecls} {ty : Ty} {allocated allocated' : List String}
    {value result : Val} (h : externalValueIn decls ty allocated value = some (allocated', result)) :
    MemberIn decls allocated' result ty := by
  cases decls with
  | nil => exact memberIn_nil.mpr (externalValue_typed _ _ _ _ _ h)
  | cons d ds =>
    simp only [externalValueIn] at h
    split at h
    · rename_i target index
      split at h
      · rename_i ha
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hv : externalValue (.handle target) allocated (.nat index) =
            some (allocated ++ [target], Value.external index) := by
          show (if externalHandleTarget target && index == allocated.length then
            some (allocated ++ [target], Value.external index) else none) = _
          rw [if_pos ha]
        exact memberIn_of_hasTy (TyDecls.unfold?_handle _ target) rfl
          (externalValue_typed _ _ _ _ _ hv)
      · cases h
    · exact (dataValueIn_some h).2.2.2

/-! ## The decision check -/

/-- A successful decision check under a table identifies the row of the actual guard token. -/
theorem admittedIn_row (decls : TyDecls) (table : RowTable) (m : NativeMachine) (fiber : FiberId)
    (token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (h : admitIn decls table m (.answerAsync fiber token answer) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧ admitAnswerIn decls row m fiber token answer = none := by
  cases decls with
  | nil => exact admitted_row table m fiber token answer h
  | cons d ds =>
    simp only [admitIn] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · exact ⟨_, _, _, by assumption, by assumption, h⟩
            · cases h
          · cases h

/-- An accepted success converts under the table. -/
theorem admitAnswerIn_success_converts {decls : TyDecls} {row : Row} {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {v : Val}
    (h : admitAnswerIn decls row m fiber token (.ofExit (.success v)) = none) :
    (externalValueIn decls row.answer m.state.externals.allocated v).isNone = false := by
  cases decls with
  | nil =>
    change (if (externalValue row.answer m.state.externals.allocated v).isNone then
      some (Refusal.answerType fiber token row.answer)
      else if !mintedIn m v then some (.deadHandle fiber token) else none) = none at h
    split at h
    · cases h
    · rename_i hn
      exact Bool.eq_false_iff.mpr hn
  | cons d ds =>
    change (if (externalValueIn (d :: ds) row.answer m.state.externals.allocated v).isNone then
      some (Refusal.answerType fiber token row.answer)
      else if !mintedIn m v then some (.deadHandle fiber token) else none) = none at h
    split at h
    · cases h
    · rename_i hn
      exact Bool.eq_false_iff.mpr hn

/-- **An admitted success is a member** (the claim `wiring-admission-sound`): the decision check
under a table returns a conversion whose output, a freshly minted handle included, is a member of
the parked row's answer column under the table, in the resulting allocation table. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem external_answer_typedIn (decls : TyDecls) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (value : Val)
    (h : admitIn decls table m (.answerAsync fiber token (.ofExit (.success value))) = none) :
    ∃ i request row allocated result, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧
      externalValueIn decls row.answer m.state.externals.allocated value =
        some (allocated, result) ∧
      MemberIn decls allocated result row.answer := by
  obtain ⟨i, request, row, hp, hr, ha⟩ := admittedIn_row decls table m fiber token _ h
  have hc := admitAnswerIn_success_converts ha
  cases hv : externalValueIn decls row.answer m.state.externals.allocated value with
  | none =>
    rw [hv] at hc
    cases hc
  | some converted =>
    obtain ⟨allocated, result⟩ := converted
    exact ⟨i, request, row, allocated, result, hp, hr, hv, externalValueIn_typed hv⟩

/-! ## The failure branch -/

/-- A typed failure that the error check under a table admits carries a value that is a member
of the error column under the table. -/
theorem errAdmitsIn_fail {decls : TyDecls} {ty : Ty} {e : Err} {ann : ReasonAnnotations Ann}
    (h : errAdmitsIn decls ty (.fail e ann) = true) :
    ∃ x, valOfErr e = some x ∧ MemberIn decls [] x ty := by
  cases decls with
  | nil =>
    change errAdmits ty (.fail e ann) = true at h
    rw [errAdmits_eq_reasonAdmits] at h
    simp only [reasonAdmits] at h
    split at h
    · rename_i x hx
      exact ⟨x, hx, memberIn_nil.mpr h⟩
    · cases h
  | cons d ds =>
    simp only [errAdmitsIn, reasonAdmits] at h
    split at h
    · rename_i x hx
      exact ⟨x, hx, hasTyIn_iff.mp h⟩
    · cases h

/-- An accepted failure's reasons all pass the error check under the table, and none dies with a
reserved defect. -/
theorem admitAnswerIn_failure {decls : TyDecls} {row : Row} {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {c : CauseV}
    (h : admitAnswerIn decls row m fiber token (.ofExit (.failure c)) = none) :
    c.reasons.any reservedDie = false ∧ c.reasons.all (errAdmitsIn decls row.error) = true := by
  cases decls with
  | nil =>
    change (if c.reasons.any reservedDie then some (Refusal.reservedDefect fiber token)
      else if c.reasons.all (errAdmits row.error) then (none : Option Refusal)
      else some (.errorType fiber token row.error)) = none at h
    split at h
    · cases h
    · rename_i hany
      split at h
      · rename_i hall
        exact ⟨Bool.eq_false_iff.mpr hany, hall⟩
      · cases h
  | cons d ds =>
    change (if c.reasons.any reservedDie then some (Refusal.reservedDefect fiber token)
      else if c.reasons.all (errAdmitsIn (d :: ds) row.error) then (none : Option Refusal)
      else some (.errorType fiber token row.error)) = none at h
    split at h
    · cases h
    · rename_i hany
      split at h
      · rename_i hall
        exact ⟨Bool.eq_false_iff.mpr hany, hall⟩
      · cases h

/-- **An admitted failure fits** the parked row's error column under the table: every typed
failure of the cause carries a value that is a member of the column. Defects and interruptions
are admitted at every error column, as on the original path (`external_error_typed`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem external_error_typedIn (decls : TyDecls) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (c : CauseV)
    (h : admitIn decls table m (.answerAsync fiber token (.ofExit (.failure c))) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧
      ∀ r ∈ c.reasons, ∀ (e : Err) (ann : ReasonAnnotations Ann), r = .fail e ann →
        ∃ x, valOfErr e = some x ∧ MemberIn decls [] x row.error := by
  obtain ⟨i, request, row, hp, hr, ha⟩ := admittedIn_row decls table m fiber token _ h
  refine ⟨i, request, row, hp, hr, fun r hr' e ann hre => ?_⟩
  subst hre
  exact errAdmitsIn_fail (List.all_eq_true.mp (admitAnswerIn_failure ha).2 _ hr')

/-- **An accepted failure carries no reserved defect** under a table (decisions row 191). -/
theorem admitIn_failure_reservedFree (decls : TyDecls) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (c : CauseV)
    (h : admitIn decls table m (.answerAsync fiber token (.ofExit (.failure c))) = none) :
    c.reasons.any reservedDie = false := by
  obtain ⟨_, _, _, _, _, ha⟩ := admittedIn_row decls table m fiber token _ h
  exact (admitAnswerIn_failure ha).1

end Effect4.Program
