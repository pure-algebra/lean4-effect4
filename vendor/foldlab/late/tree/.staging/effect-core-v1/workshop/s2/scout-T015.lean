import Cas.Core.Admission

/-!
# Effect Core v1 — slice EC1-S2 scout probe for `EC1-T015`

Scout artifact ONLY. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Diagnostic.lean`. The file borrows
`library/cas`'s environment; it is not in any lake target.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T015.lean
```

The DAG row under scout is

```text
EC1-T015  first_diagnostic_complete :
            FirstReject r path code -> check r = error (diagnostic path code)
```

`EC1-CE031` already refuted this row's PREVIOUS (per-condemning-clause) form.
`R16` then ruled the checker first-error. Three questions remain, and this file
answers all three at the estate's own admission scale (`Cas.checkRefs`), which
is the only shipped fail-fast checker in the corpus:

| § | Question | Finding |
|---|---|---|
| 2 | Is the row VACUOUS? | Yes, if `FirstReject` is spelled through the checker: the proof term is `id`. |
| 3 | Is the row's LITERAL signature satisfiable? | No. `(path, code)` does not determine the diagnostic; no `diagnostic : Path -> Code -> Diagnostic` exists. |
| 4 | Is the CHECKER-FREE restatement substantive? | Yes, and it is an `iff`. A rival fail-fast checker that is sound and existentially complete still violates it. |
| 5 | Does the restatement resurrect `EC1-CE031`? | No. The `CE031` witness still has a condemning clause that is never reported. |

Section 1 gives the checker-free `FirstReject` the rest of the file uses.
Every theorem's `#print axioms` receipt is at the foot.
-/

namespace EffectCoreScoutT015

open Cas

/-! ## 0. Witnesses

Reused verbatim from `workshop/counterexamples/LocalAnchors.lean`
(`EC1-CE031`) so the two files talk about the same store. -/

def a1 : Addr32 := ⟨List.replicate 32 1, by simp⟩
def a2 : Addr32 := ⟨List.replicate 32 2, by simp⟩

/-! ## 1. `FirstReject`, stated WITHOUT naming the checker

This is the load-bearing definitional choice for `EC1-T015`. `Bad` and
`clause` are read off the reference list and the store; `checkRefs` does not
appear. -/

/-- A reference position is BAD when it fails to resolve at its declared
kind — the negation of the per-position half of `Cas.RefsOk`. -/
def Bad (σ : Store) (r : Ref) : Prop :=
  ¬ ∃ m, σ r.addr = some m ∧ m.tag = r.expectedTag

/-- The clause a BAD position produces. Total; its value at a good position is
never consulted. -/
def clause (σ : Store) (r : Ref) : AdmissionError :=
  match σ r.addr with
  | none => .dangling r.addr
  | some m => .wrongKind r.addr r.expectedTag m.tag

/-- FIRST REJECT: the list splits at a bad position, every EARLIER position is
good, and `e` is that position's clause. Purely a statement about the
reference list. -/
def FirstReject (σ : Store) (rs : List Ref) (e : AdmissionError) : Prop :=
  ∃ pre r post,
    rs = pre ++ r :: post ∧ (∀ x ∈ pre, ¬ Bad σ x) ∧ Bad σ r ∧ e = clause σ r

theorem not_bad_of_resolves {σ : Store} {r : Ref} {m : Node}
    (hm : σ r.addr = some m) (ht : m.tag = r.expectedTag) : ¬ Bad σ r := by
  intro hb
  exact hb ⟨m, hm, ht⟩

theorem bad_of_none {σ : Store} {r : Ref} (hm : σ r.addr = none) : Bad σ r := by
  rintro ⟨m, hm', -⟩
  rw [hm] at hm'
  exact nomatch hm'

theorem bad_of_wrongTag {σ : Store} {r : Ref} {m : Node}
    (hm : σ r.addr = some m) (ht : m.tag ≠ r.expectedTag) : Bad σ r := by
  rintro ⟨m', hm', ht'⟩
  rw [hm] at hm'
  injection hm' with he
  exact ht (he ▸ ht')

/-- PER-CLAUSE REFLECTION. `Bad` is decidable on its own, without the checker.
This is what makes `PROOF-DAG.md` §16's Checker route — "structural recursion
plus decidable per-clause reflection" — available at this scale, and it is the
property every `ProgramWF` clause owes before `EC1-T011`/`EC1-T012` may be
attempted. -/
instance instDecidableBad (σ : Store) (r : Ref) : Decidable (Bad σ r) :=
  match hm : σ r.addr with
  | none => isTrue (bad_of_none hm)
  | some m =>
    if ht : m.tag = r.expectedTag then isFalse (not_bad_of_resolves hm ht)
    else isTrue (bad_of_wrongTag hm ht)

/-! ## 2. The vacuity trap

If `FirstReject` is defined THROUGH the checker — "the first reject is whatever
the checker returns" — then `EC1-T015` is a tautology over a Lean function, the
exact defect that already deleted two rows from this packet. The proof term
below is `id`. -/

/-- The tempting checker-relative spelling. -/
def FirstRejectByChecker (σ : Store) (rs : List Ref) (e : AdmissionError) : Prop :=
  checkRefs σ rs = .error e

/-- `EC1-T015` under the checker-relative spelling: proved by `id`. This is the
vacuity finding, exhibited rather than asserted. -/
theorem T015_is_vacuous_under_checker_relative_firstReject
    (σ : Store) (rs : List Ref) (e : AdmissionError) :
    FirstRejectByChecker σ rs e → checkRefs σ rs = .error e :=
  id

/-! ## 3. The DAG's LITERAL signature is not satisfiable

The row's conclusion is `check r = error (diagnostic path code)`: the returned
diagnostic is a function of the path and the clause code ALONE. The estate's own
diagnostic family refutes that — `wrongKind` carries `expected` and `actual`
beyond its address, and two raw inputs can reject at the same address with the
same code and different payload. -/

/-- The clause code, i.e. the row's `code` component. -/
inductive Code where
  | dangling
  | wrongKind
  deriving DecidableEq

def errCode : AdmissionError → Code
  | .dangling _ => .dangling
  | .wrongKind _ _ _ => .wrongKind

/-- The row's `path` component: the address the clause names. -/
def errPath : AdmissionError → Addr32
  | .dangling a => a
  | .wrongKind a _ _ => a

def sA : Store := Store.empty.set a2 ⟨0, 7, [], []⟩
def sB : Store := Store.empty.set a2 ⟨0, 9, [], []⟩
def rsAB : List Ref := [⟨3, a2⟩]

theorem sA_a2 : sA a2 = some ⟨0, 7, [], []⟩ := by
  simp [sA, Store.set]

theorem sB_a2 : sB a2 = some ⟨0, 9, [], []⟩ := by
  simp [sB, Store.set]

theorem checkA : checkRefs sA rsAB = .error (.wrongKind a2 3 7) := by
  have h : sA (Ref.addr (⟨3, a2⟩ : Ref)) = some ⟨0, 7, [], []⟩ := sA_a2
  simp only [rsAB, checkRefs, h]
  rfl

theorem checkB : checkRefs sB rsAB = .error (.wrongKind a2 3 9) := by
  have h : sB (Ref.addr (⟨3, a2⟩ : Ref)) = some ⟨0, 9, [], []⟩ := sB_a2
  simp only [rsAB, checkRefs, h]
  rfl

theorem firstRejectA : FirstReject sA rsAB (.wrongKind a2 3 7) :=
  ⟨[], ⟨3, a2⟩, [], rfl, by simp,
    bad_of_wrongTag sA_a2 (by decide),
    by show _ = clause sA ⟨3, a2⟩
       simp only [clause]
       rw [sA_a2]⟩

theorem firstRejectB : FirstReject sB rsAB (.wrongKind a2 3 9) :=
  ⟨[], ⟨3, a2⟩, [], rfl, by simp,
    bad_of_wrongTag sB_a2 (by decide),
    by show _ = clause sB ⟨3, a2⟩
       simp only [clause]
       rw [sB_a2]⟩

/-- **The literal `EC1-T015` signature has no witness.** No function from
`(path, code)` to a diagnostic can be the checker's output: two reference lists
reject at the same address under the same clause code with different payloads.
The row must quantify over the whole diagnostic value. -/
theorem no_diagnostic_from_path_and_code :
    ¬ ∃ diagnostic : Addr32 → Code → AdmissionError,
        ∀ (σ : Store) (rs : List Ref) (p : Addr32) (c : Code),
          (∃ e, FirstReject σ rs e ∧ errPath e = p ∧ errCode e = c) →
            checkRefs σ rs = .error (diagnostic p c) := by
  rintro ⟨diagnostic, hd⟩
  have hA := hd sA rsAB a2 Code.wrongKind ⟨_, firstRejectA, rfl, rfl⟩
  have hB := hd sB rsAB a2 Code.wrongKind ⟨_, firstRejectB, rfl, rfl⟩
  rw [checkA] at hA
  rw [checkB] at hB
  rw [← hB] at hA
  injection hA with h
  injection h with _ _ h7
  exact absurd h7 (by decide)

/-! ## 4. The checker-free restatement, and the proof that it has content

`checkRefs_firstReject_iff` is the statement I would actually prove for
`EC1-T015`. It packages `R16`'s admissible pair in one `iff`, in the estate's
own `checkRefs_ok_iff` house shape: left-to-right is first-error SOUNDNESS,
right-to-left is first-error COMPLETENESS. -/

theorem checkRefs_firstReject_iff (σ : Store) :
    ∀ (rs : List Ref) (e : AdmissionError),
      checkRefs σ rs = .error e ↔ FirstReject σ rs e := by
  intro rs
  induction rs with
  | nil =>
    intro e
    constructor
    · intro h
      simp [checkRefs] at h
    · rintro ⟨pre, r, post, hsplit, -, -, -⟩
      cases pre <;> simp at hsplit
  | cons r rs ih =>
    intro e
    cases hm : σ r.addr with
    | none =>
      have hbad : Bad σ r := bad_of_none hm
      have hcl : clause σ r = .dangling r.addr := by
        simp only [clause]; rw [hm]
      have hchk : checkRefs σ (r :: rs) = .error (.dangling r.addr) := by
        simp only [checkRefs, hm]
      constructor
      · intro h
        rw [hchk] at h
        exact ⟨[], r, rs, rfl, by simp, hbad, by rw [hcl, ← Except.error.inj h]⟩
      · rintro ⟨pre, r', post, hsplit, hpre, hbad', he⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          rw [hchk, he, ← hsplit.1, hcl]
        | cons x pre' =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          have hx : ¬ Bad σ x := hpre x List.mem_cons_self
          rw [hsplit.1] at hbad
          exact absurd hbad hx
    | some m =>
      by_cases htag : m.tag = r.expectedTag
      · have hgood : ¬ Bad σ r := not_bad_of_resolves hm htag
        have hchk : checkRefs σ (r :: rs) = checkRefs σ rs := by
          simp only [checkRefs, hm, if_pos htag]
        constructor
        · intro h
          rw [hchk] at h
          obtain ⟨pre, r', post, hsplit, hpre, hbad', he⟩ := (ih e).mp h
          refine ⟨r :: pre, r', post, by rw [List.cons_append, hsplit], ?_, hbad', he⟩
          intro x hx
          rcases List.mem_cons.mp hx with hxr | hxp
          · exact hxr ▸ hgood
          · exact hpre x hxp
        · rintro ⟨pre, r', post, hsplit, hpre, hbad', he⟩
          rw [hchk]
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            exact absurd (hsplit.1 ▸ hbad') hgood
          | cons x pre' =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            refine (ih e).mpr ⟨pre', r', post, hsplit.2, ?_, hbad', he⟩
            intro y hy
            exact hpre y (List.mem_cons_of_mem x hy)
      · have hbad : Bad σ r := bad_of_wrongTag hm htag
        have hcl : clause σ r = .wrongKind r.addr r.expectedTag m.tag := by
          simp only [clause]; rw [hm]
        have hchk :
            checkRefs σ (r :: rs) = .error (.wrongKind r.addr r.expectedTag m.tag) := by
          simp only [checkRefs, hm, if_neg htag]
        constructor
        · intro h
          rw [hchk] at h
          exact ⟨[], r, rs, rfl, by simp, hbad, by rw [hcl, ← Except.error.inj h]⟩
        · rintro ⟨pre, r', post, hsplit, hpre, hbad', he⟩
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            rw [hchk, he, ← hsplit.1, hcl]
          | cons x pre' =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            have hx : ¬ Bad σ x := hpre x List.mem_cons_self
            rw [hsplit.1] at hbad
            exact absurd hbad hx

instance : DecidableEq (Except AdmissionError Unit)
  | .ok (), .ok () => isTrue rfl
  | .ok (), .error _ => isFalse (fun h => by cases h)
  | .error _, .ok () => isFalse (fun h => by cases h)
  | .error a, .error b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun he => h (Except.error.inj he))

/-- The rejection judgment is DECIDED by the checker, not merely reflected by
it — the shape `EC1-T012` wants, obtained here as a corollary rather than
assumed. -/
instance instDecidableFirstReject (σ : Store) (rs : List Ref) (e : AdmissionError) :
    Decidable (FirstReject σ rs e) :=
  decidable_of_iff _ (checkRefs_firstReject_iff σ rs e)

/-! ### 4b. The rival checker — proof that the restatement is not vacuous

`checkRefsKindFirst` uses the SAME clause vocabulary and the SAME fail-fast
discipline, and differs only in SCAN ORDER: every wrong-kind position outranks
every dangling one. It satisfies `R16`'s admissible pair — first-error soundness
and existential rejection completeness — and still violates
`checkRefs_firstReject_iff`. So the canonical-order premise in the row's
"Depends on" column is load-bearing, not decoration. -/

def wrongKindHere (σ : Store) (r : Ref) : Bool :=
  match σ r.addr with
  | none => false
  | some m => !(m.tag == r.expectedTag)

theorem wrongKindHere_spec {σ : Store} {r : Ref} (h : wrongKindHere σ r = true) :
    ∃ m, σ r.addr = some m ∧ m.tag ≠ r.expectedTag := by
  cases hm : σ r.addr with
  | none => rw [wrongKindHere, hm] at h; exact nomatch h
  | some m =>
    rw [wrongKindHere, hm] at h
    refine ⟨m, rfl, ?_⟩
    simpa using h

def checkRefsKindFirst (σ : Store) (rs : List Ref) : Except AdmissionError Unit :=
  match rs.find? (wrongKindHere σ) with
  | some r => .error (clause σ r)
  | none => checkRefs σ rs

/-- The rival is SOUND in the estate's own sense: what it reports condemns the
input. -/
theorem checkRefsKindFirst_error_condemns {σ : Store} {rs : List Ref}
    {e : AdmissionError} (h : checkRefsKindFirst σ rs = .error e) :
    e.Condemns σ rs := by
  cases hf : rs.find? (wrongKindHere σ) with
  | none =>
    have hval : checkRefsKindFirst σ rs = checkRefs σ rs := by
      simp only [checkRefsKindFirst, hf]
    rw [hval] at h
    exact checkRefs_error_condemns h
  | some r =>
    have hval : checkRefsKindFirst σ rs = .error (clause σ r) := by
      simp only [checkRefsKindFirst, hf]
    rw [hval] at h
    obtain ⟨m, hm, hne⟩ := wrongKindHere_spec (List.find?_some hf)
    have hmem : r ∈ rs := List.mem_of_find?_eq_some hf
    have hcl : clause σ r = .wrongKind r.addr r.expectedTag m.tag := by
      simp only [clause]; rw [hm]
    have hee : e = clause σ r := (Except.error.inj h).symm
    rw [hee, hcl]
    exact ⟨r, hmem, rfl, rfl, m, hm, rfl, fun hc => hne (hc ▸ rfl)⟩

/-- The rival is EXISTENTIALLY COMPLETE in the estate's own sense: a condemned
input is rejected. -/
theorem checkRefsKindFirst_complete {σ : Store} {rs : List Ref}
    (h : ∃ e, AdmissionError.Condemns σ e rs) :
    ∃ e', checkRefsKindFirst σ rs = .error e' := by
  unfold checkRefsKindFirst
  cases hf : rs.find? (wrongKindHere σ) with
  | some r => exact ⟨clause σ r, rfl⟩
  | none => exact checkRefs_complete h

/-! ### 4c. The disagreement, on the `EC1-CE031` witness -/

def sigma : Store := Store.empty.set a2 ⟨0, 7, [], []⟩
def refs : List Ref := [⟨1, a1⟩, ⟨3, a2⟩]

theorem sigma_a1 : sigma a1 = none := by
  simp [sigma, Store.set, Store.empty, a1, a2]

theorem sigma_a2 : sigma a2 = some ⟨0, 7, [], []⟩ := by
  simp [sigma, Store.set]

/-- The canonical checker reports the FIRST failing position. Same fact as
`LocalAnchors.checker_reports_only_the_first`, re-elaborated here so this file
stands alone. -/
theorem canonical_reports_dangling : checkRefs sigma refs = .error (.dangling a1) := by
  show (match sigma a1 with
        | none => Except.error (AdmissionError.dangling a1)
        | some m => if m.tag = (1 : UInt8) then checkRefs sigma [⟨3, a2⟩]
                    else .error (.wrongKind a1 1 m.tag)) = _
  rw [sigma_a1]

theorem rival_reports_wrongKind :
    checkRefsKindFirst sigma refs = .error (.wrongKind a2 3 7) := by
  have hf : refs.find? (wrongKindHere sigma) = some ⟨3, a2⟩ := by
    show (if wrongKindHere sigma ⟨1, a1⟩ then some (⟨1, a1⟩ : Ref)
          else if wrongKindHere sigma ⟨3, a2⟩ then some (⟨3, a2⟩ : Ref)
          else none) = _
    rw [show wrongKindHere sigma ⟨1, a1⟩ = false by
          rw [wrongKindHere]; rw [show sigma (Ref.addr ⟨1, a1⟩) = none from sigma_a1],
        show wrongKindHere sigma ⟨3, a2⟩ = true by
          rw [wrongKindHere]; rw [show sigma (Ref.addr ⟨3, a2⟩) = some ⟨0, 7, [], []⟩ from sigma_a2]
          rfl]
    rfl
  have hcl : clause sigma ⟨3, a2⟩ = .wrongKind a2 3 7 := by
    simp only [clause]
    rw [show sigma (Ref.addr ⟨3, a2⟩) = some ⟨0, 7, [], []⟩ from sigma_a2]
  have hval : checkRefsKindFirst sigma refs = .error (clause sigma ⟨3, a2⟩) := by
    simp only [checkRefsKindFirst, hf]
  rw [hval, hcl]

/-- **The restatement has content.** The rival satisfies first-error soundness
and existential rejection completeness, yet its output is not the first reject.
`EC1-T015`, once `FirstReject` is checker-free, genuinely excludes it. -/
theorem rival_violates_firstReject : ¬ FirstReject sigma refs (.wrongKind a2 3 7) := by
  intro h
  have := (checkRefs_firstReject_iff sigma refs (.wrongKind a2 3 7)).mpr h
  rw [canonical_reports_dangling] at this
  injection this with hc
  exact absurd hc (by decide)

/-! ## 5. `EC1-CE031` still stands under the restatement

The restated row does NOT smuggle back the refuted per-condemning-clause
reading: on the same witness, a second clause still condemns the input and is
still not the reported diagnostic. -/

theorem wrongKind_still_condemns :
    AdmissionError.Condemns sigma (.wrongKind a2 3 7) refs :=
  ⟨⟨3, a2⟩, by simp [refs], rfl, rfl, ⟨0, 7, [], []⟩,
    show sigma a2 = some ⟨0, 7, [], []⟩ from sigma_a2, rfl, by decide⟩

/-- `EC1-CE031` is untouched: a condemning clause that first-error completeness
does not, and must not, promise. -/
theorem ce031_survives_the_restatement :
    AdmissionError.Condemns sigma (.wrongKind a2 3 7) refs
      ∧ ¬ FirstReject sigma refs (.wrongKind a2 3 7) :=
  ⟨wrongKind_still_condemns, rival_violates_firstReject⟩

end EffectCoreScoutT015

/-! ## Axiom receipts -/

#print axioms EffectCoreScoutT015.T015_is_vacuous_under_checker_relative_firstReject
#print axioms EffectCoreScoutT015.no_diagnostic_from_path_and_code
#print axioms EffectCoreScoutT015.checkRefs_firstReject_iff
#print axioms EffectCoreScoutT015.checkRefsKindFirst_error_condemns
#print axioms EffectCoreScoutT015.checkRefsKindFirst_complete
#print axioms EffectCoreScoutT015.canonical_reports_dangling
#print axioms EffectCoreScoutT015.rival_reports_wrongKind
#print axioms EffectCoreScoutT015.rival_violates_firstReject
#print axioms EffectCoreScoutT015.ce031_survives_the_restatement
