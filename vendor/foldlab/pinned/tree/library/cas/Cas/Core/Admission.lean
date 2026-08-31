import Cas.Core.Store
import Cas.Core.Address

/-!
# Store admission

The CAS-002 judgment: a node enters the store only when every reference
resolves at its declared kind. Errors are clause-named and mirror the
runtime's `CasError` family member for member — `dangling` carries the
missing address, `wrongKind` the offending reference's address with its
declared and resident tags. `AdmissionError.Condemns` states what each
clause asserts; the checker is sound (a returned error's clause holds of
the input) and complete (a condemned input is rejected).

`put` is the admission-checked transition in the Plebeia shape: fresh and
occupied addresses are separated, and the occupied case is characterized —
a no-op exactly when the resident equals the incoming node, an explicit
conflict carrying the distinct occupant otherwise. The address function is
a plain function argument; no theorem assumes it injective, and the
conflict case is surfaced, never argued away. Hash-lattice Level 0
throughout.
-/

namespace Cas

/-- Clause-named admission errors, mirroring the runtime error family:
`dangling` carries the missing address, `wrongKind` the offending
reference's address, declared tag, and resident tag. -/
inductive AdmissionError where
  | dangling (missing : Addr32)
  | wrongKind (ref : Addr32) (expected actual : UInt8)
  deriving DecidableEq

/-- Every reference resolves, at its declared kind. -/
def RefsOk (σ : Store) (rs : List Ref) : Prop :=
  ∀ r ∈ rs, ∃ m, σ r.addr = some m ∧ m.tag = r.expectedTag

/-- What each clause condemns. A `dangling` error asserts a reference to an
unbound address; a `wrongKind` error asserts a reference whose declared tag
disagrees with the resident node's tag. -/
def AdmissionError.Condemns (σ : Store) : AdmissionError → List Ref → Prop
  | .dangling a, rs => ∃ r ∈ rs, r.addr = a ∧ σ a = none
  | .wrongKind a exp act, rs =>
      ∃ r ∈ rs, r.addr = a ∧ r.expectedTag = exp ∧
        ∃ m, σ a = some m ∧ m.tag = act ∧ act ≠ exp

/-- The reference check: scan in order; the first failing reference names
its clause. -/
def checkRefs (σ : Store) : List Ref → Except AdmissionError Unit
  | [] => .ok ()
  | r :: rs =>
    match σ r.addr with
    | none => .error (.dangling r.addr)
    | some m =>
      if m.tag = r.expectedTag then checkRefs σ rs
      else .error (.wrongKind r.addr r.expectedTag m.tag)

/-- The check accepts exactly the reference lists that resolve at their
declared kinds. -/
theorem checkRefs_ok_iff {σ : Store} {rs : List Ref} :
    checkRefs σ rs = .ok () ↔ RefsOk σ rs := by
  induction rs with
  | nil => simp [checkRefs, RefsOk]
  | cons r rs ih =>
    simp only [RefsOk, List.forall_mem_cons]
    cases hm : σ r.addr with
    | none =>
      simp only [checkRefs, hm]
      constructor
      · intro h; exact nomatch h
      · rintro ⟨⟨m, hm', _⟩, _⟩
        exact nomatch hm'
    | some m =>
      by_cases htag : m.tag = r.expectedTag
      · simp only [checkRefs, hm, if_pos htag]
        constructor
        · intro h; exact ⟨⟨m, rfl, htag⟩, ih.mp h⟩
        · rintro ⟨_, h⟩; exact ih.mpr h
      · simp only [checkRefs, hm, if_neg htag]
        constructor
        · intro h; exact nomatch h
        · rintro ⟨⟨m', hm', htag'⟩, _⟩
          injection hm' with he
          subst he
          exact absurd htag' htag

/-- A condemned reference list never checks out. -/
theorem AdmissionError.Condemns.not_refsOk {σ : Store} {e : AdmissionError} {rs : List Ref}
    (h : e.Condemns σ rs) : ¬ RefsOk σ rs := by
  intro hok
  cases e with
  | dangling a =>
    simp only [AdmissionError.Condemns] at h
    obtain ⟨t, ht, hta, hnone⟩ := h
    obtain ⟨m, hm, _⟩ := hok t ht
    rw [hta, hnone] at hm
    exact nomatch hm
  | wrongKind a exp act =>
    simp only [AdmissionError.Condemns] at h
    obtain ⟨t, ht, hta, hexp, m, hm, hact, hne⟩ := h
    obtain ⟨m', hm', htag'⟩ := hok t ht
    rw [hta, hm] at hm'
    injection hm' with he
    subst he
    exact hne (by rw [← hact, htag', hexp])

/-- Soundness: a returned error's clause holds of the checked list. -/
theorem checkRefs_error_condemns {σ : Store} {rs : List Ref}
    {e : AdmissionError} (h : checkRefs σ rs = .error e) :
    e.Condemns σ rs := by
  induction rs with
  | nil => exact nomatch h
  | cons r rs ih =>
    cases hm : σ r.addr with
    | none =>
      simp only [checkRefs, hm] at h
      injection h with he
      subst he
      exact ⟨r, List.mem_cons_self, rfl, hm⟩
    | some m =>
      by_cases htag : m.tag = r.expectedTag
      · simp only [checkRefs, hm, if_pos htag] at h
        cases e with
        | dangling a =>
          obtain ⟨t, ht, hta, hnone⟩ := ih h
          exact ⟨t, List.mem_cons_of_mem r ht, hta, hnone⟩
        | wrongKind a exp act =>
          obtain ⟨t, ht, hta, hexp, m', hm', hact, hne⟩ := ih h
          exact ⟨t, List.mem_cons_of_mem r ht, hta, hexp, m', hm', hact, hne⟩
      · simp only [checkRefs, hm, if_neg htag] at h
        injection h with he
        subst he
        exact ⟨r, List.mem_cons_self, rfl, rfl, m, hm, rfl, htag⟩

/-- Completeness: a condemned reference list is rejected (with the first
failing clause found, not necessarily the condemning one). -/
theorem checkRefs_complete {σ : Store} {rs : List Ref}
    (h : ∃ e, AdmissionError.Condemns σ e rs) :
    ∃ e', checkRefs σ rs = .error e' := by
  obtain ⟨e, he⟩ := h
  cases hc : checkRefs σ rs with
  | ok u =>
    cases u
    exact absurd (checkRefs_ok_iff.mp hc) he.not_refsOk
  | error e' => exact ⟨e', rfl⟩

/-- The admission judgment at the node level: the node's references,
checked against the store. -/
def admitNode (σ : Store) (n : Node) : Except AdmissionError Unit :=
  checkRefs σ n.refs

theorem admitNode_error_condemns {σ : Store} {n : Node} {e : AdmissionError}
    (h : admitNode σ n = .error e) : e.Condemns σ n.refs :=
  checkRefs_error_condemns h

theorem admitNode_complete {σ : Store} {n : Node}
    (h : ∃ e, AdmissionError.Condemns σ e n.refs) :
    ∃ e', admitNode σ n = .error e' :=
  checkRefs_complete h

/-! ## The admission-checked transition -/

/-- What a put did. `fresh` binds an unbound address and returns the
successor store; `duplicate` finds the identical node already resident and
changes nothing; `conflict` finds a DIFFERENT resident at the incoming
node's address and surfaces it — the explicit collision witness of the
Level-0 characterization. -/
inductive PutOutcome where
  | fresh (a : Addr32) (σ' : Store)
  | duplicate (a : Addr32)
  | conflict (a : Addr32) (occupant : Node)

/-- Admission-checked put: reject on a failing reference clause; otherwise
bind the node's address if fresh, and characterize the occupied case as
duplicate or conflict. -/
def put (H : Bytes → Addr32) (σ : Store) (n : AdmittedNode) :
    Except AdmissionError PutOutcome :=
  match checkRefs σ n.val.refs with
  | .error e => .error e
  | .ok _ =>
    match σ (addr H n) with
    | none => .ok (.fresh (addr H n) (σ.set (addr H n) n.val))
    | some m =>
      if m = n.val then .ok (.duplicate (addr H n))
      else .ok (.conflict (addr H n) m)

/-- Put rejects exactly when admission rejects. -/
theorem put_error_iff {H : Bytes → Addr32} {σ : Store} {n : AdmittedNode}
    {e : AdmissionError} :
    put H σ n = .error e ↔ checkRefs σ n.val.refs = .error e := by
  cases hc : checkRefs σ n.val.refs with
  | error e' => simp [put, hc]
  | ok u =>
    cases u
    cases hm : σ (addr H n) with
    | none => simp [put, hc, hm]
    | some m => by_cases hmn : m = n.val <;> simp [put, hc, hm, hmn]

/-- The fresh case: the address was unbound, the node's references check
out, and the successor store binds the node at its address. -/
theorem put_fresh_spec {H : Bytes → Addr32} {σ : Store} {n : AdmittedNode}
    {a : Addr32} {σ' : Store} (h : put H σ n = .ok (.fresh a σ')) :
    RefsOk σ n.val.refs ∧ σ a = none ∧ a = addr H n ∧
      σ' = σ.set a n.val := by
  cases hc : checkRefs σ n.val.refs with
  | error e => simp [put, hc] at h
  | ok u =>
    cases u
    cases hm : σ (addr H n) with
    | none =>
      simp only [put, hc] at h
      simp only [hm, Except.ok.injEq, PutOutcome.fresh.injEq] at h
      obtain ⟨ha, hσ'⟩ := h
      subst ha
      exact ⟨checkRefs_ok_iff.mp hc, hm, rfl, hσ'.symm⟩
    | some m => by_cases hmn : m = n.val <;> simp [put, hc, hm, hmn] at h

/-- The duplicate case: the identical node was already resident at its
address; the store is unchanged. -/
theorem put_duplicate_spec {H : Bytes → Addr32} {σ : Store}
    {n : AdmittedNode} {a : Addr32} (h : put H σ n = .ok (.duplicate a)) :
    RefsOk σ n.val.refs ∧ a = addr H n ∧ σ a = some n.val := by
  cases hc : checkRefs σ n.val.refs with
  | error e => simp [put, hc] at h
  | ok u =>
    cases u
    cases hm : σ (addr H n) with
    | none => simp [put, hc, hm] at h
    | some m =>
      by_cases hmn : m = n.val
      · simp only [put, hc] at h
        simp only [hm, if_pos hmn, Except.ok.injEq,
          PutOutcome.duplicate.injEq] at h
        subst h
        exact ⟨checkRefs_ok_iff.mp hc, rfl, by rw [hm, hmn]⟩
      · simp [put, hc, hm, hmn] at h

/-- The conflict case, characterized and never argued away: a DIFFERENT
node is resident at the incoming node's address. The witness is explicit —
two distinct nodes, one address — and no injectivity of the address
function is assumed anywhere. -/
theorem put_conflict_spec {H : Bytes → Addr32} {σ : Store}
    {n : AdmittedNode} {a : Addr32} {occ : Node}
    (h : put H σ n = .ok (.conflict a occ)) :
    RefsOk σ n.val.refs ∧ a = addr H n ∧ σ a = some occ ∧ occ ≠ n.val := by
  cases hc : checkRefs σ n.val.refs with
  | error e => simp [put, hc] at h
  | ok u =>
    cases u
    cases hm : σ (addr H n) with
    | none => simp [put, hc, hm] at h
    | some m =>
      by_cases hmn : m = n.val
      · simp [put, hc, hm, hmn] at h
      · simp only [put, hc] at h
        simp only [hm, if_neg hmn, Except.ok.injEq,
          PutOutcome.conflict.injEq] at h
        obtain ⟨ha, hocc⟩ := h
        subst ha
        subst hocc
        exact ⟨checkRefs_ok_iff.mp hc, rfl, hm, hmn⟩

/-- Get after fresh put: the successor store resolves the bound address to
the node just admitted. -/
theorem put_fresh_get {H : Bytes → Addr32} {σ : Store} {n : AdmittedNode}
    {a : Addr32} {σ' : Store} (h : put H σ n = .ok (.fresh a σ')) :
    σ' a = some n.val := by
  obtain ⟨_, _, _, hσ'⟩ := put_fresh_spec h
  subst hσ'
  exact Store.set_same σ a n.val

/-- Fresh put preserves store well-formedness: the incoming node's
references resolve by admission, and no resident reference can point at a
fresh address in a closed store. -/
theorem put_fresh_closed {H : Bytes → Addr32} {σ : Store} {n : AdmittedNode}
    {a : Addr32} {σ' : Store} (hσ : Store.Closed σ)
    (h : put H σ n = .ok (.fresh a σ')) : Store.Closed σ' := by
  obtain ⟨hok, hfresh, _ha, hσ'⟩ := put_fresh_spec h
  subst hσ'
  intro b nb hb r hr
  by_cases hba : b = a
  · rw [hba, Store.set_same] at hb
    injection hb with hb
    subst hb
    obtain ⟨m, hm, htag⟩ := hok r hr
    have hra : r.addr ≠ a := by
      intro heq
      rw [heq, hfresh] at hm
      exact nomatch hm
    exact ⟨m, by rw [Store.set_other σ n.val hra]; exact hm, htag⟩
  · rw [Store.set_other σ n.val hba] at hb
    obtain ⟨m, hm, htag⟩ := hσ b nb hb r hr
    have hra : r.addr ≠ a := hσ.not_referenced hfresh b nb hb r hr
    exact ⟨m, by rw [Store.set_other σ n.val hra]; exact hm, htag⟩

end Cas
