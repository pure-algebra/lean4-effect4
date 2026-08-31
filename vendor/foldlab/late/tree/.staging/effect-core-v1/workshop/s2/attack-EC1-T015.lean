import T015

/-!
# Attack on `EC1-T015` — breaker witnesses

Adversarial file for the landed `T015.lean`. This file `import`s the REAL
`EffectCoreT015` declarations (compiled to an `.olean` in the reviewer's
scratchpad) rather than copying them, so every result below is about the
theorem as landed, not a restatement of it.

Run from `library/cas`:

```
lake env sh -c "lean --root=<s2dir> -o <scratch>/T015.olean <s2dir>/T015.lean"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:<scratch> lean <s2dir>/attack-EC1-T015.lean"
```

No `sorry`, no `axiom`, no `native_decide`, no `#eval` used as a claim.
`#print axioms` for every result is at the foot.

## What is attacked

* §A1 — the RESIDUAL VACUITY. `T015.lean` §5 exhibits one vacuity trap and
  argues that a DECLARED `scan` escapes it. It does not. For EVERY
  `check : Raw -> Except Diag Payload` there is a `Clauses` record whose scan
  is the checker's own answer, so `first_diagnostic_iff` applies to every
  checker whatsoever. The row constrains `check` only once the packet FIXES
  `C`, which it does not (`PROOF-DAG.md:107-121` declares no `scan`).
* §A2 — `EC1-F81` FLIPS GREEN. Instantiating §A1 at the file's own rival
  checker: on `Mini.w`, which carries two independent defects, `EC1-T015` as
  landed CERTIFIES the LATER-in-canonical-order diagnostic as the first
  reject. F81 stays red only relative to a fixed `C`.
* §A3 — `Pos := Path` is not available. `T015.lean:§1` says the intended
  instantiation is `Pos := Path`. Two `Clauses` with the SAME `scan` and the
  SAME `Bad` and different `clauseAt` both satisfy the row and report
  different diagnostics, so freezing the scan order — the ruling the report
  asks the coordinator for — does not determine the diagnostic.
* §A4 — the decidability obligation the row does not claim but does incur.
* §A5 — what genuinely SURVIVES: F81 red at a fixed `C`, diagnostic
  uniqueness, and the CAS reuse receipt.
-/

namespace AttackT015

open EffectCoreT015

/-! ## A1. The residual vacuity: every checker inhabits the hypothesis

`T015.lean` §5 proves `T015_is_vacuous_under_checker_relative_firstReject`
(proof term `id`) and concludes: *"This is why `scan` must be a declared
object."* The inference is wrong. `scan` being a FIELD of a record the caller
supplies is not the same as `scan` being FIXED by the packet. Below, the record
is reverse-engineered from the checker: `Pos := Diag`, and the scan order is
literally "the answer the checker gave". -/

section Universal

variable {Raw Diag Payload : Type}

/-- The `Clauses` record built FROM an arbitrary checker. Every field is
first-order and total; `badB` is constantly `true`, so per-clause reflection is
discharged by `rfl`. -/
def reverseEngineered (check : Raw → Except Diag Payload) : Clauses Raw Diag Diag where
  scan := fun r => match check r with
    | .error d => [d]
    | .ok _ => []
  badB := fun _ _ => true
  Bad := fun _ _ => True
  badB_iff := fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩
  clauseAt := fun _ d => d

/-- On a rejected input the reverse-engineered scanner reproduces the
checker's diagnostic exactly. -/
theorem reverse_scan_error {check : Raw → Except Diag Payload} {r : Raw} {d₀ : Diag}
    (h : check r = .error d₀) : checkClauses (reverseEngineered check) r = .error d₀ := by
  show checkFrom (reverseEngineered check) r ((reverseEngineered check).scan r) = _
  have hs : (reverseEngineered check).scan r = [d₀] := by
    show (match check r with | .error d => [d] | .ok _ => []) = [d₀]
    rw [h]
  rw [hs]
  rfl

/-- On an accepted input it accepts. -/
theorem reverse_scan_ok {check : Raw → Except Diag Payload} {r : Raw} {p : Payload}
    (h : check r = .ok p) : checkClauses (reverseEngineered check) r = .ok () := by
  show checkFrom (reverseEngineered check) r ((reverseEngineered check).scan r) = _
  have hs : (reverseEngineered check).scan r = [] := by
    show (match check r with | .error d => [d] | .ok _ => []) = []
    rw [h]
  rw [hs]
  rfl

/-- The reverse-engineered scanner COMPUTES the checker's error branch. -/
theorem reverse_errorBranch (check : Raw → Except Diag Payload) :
    ErrorBranchIsClauseScan (reverseEngineered check) check := by
  intro r d
  cases h : check r with
  | error d₀ =>
    -- the two sides live in `Except Diag Payload` and `Except Diag Unit`
    rw [reverse_scan_error h]
    constructor
    · intro he; rw [Except.error.inj he]
    · intro he; rw [Except.error.inj he]
  | ok p =>
    rw [reverse_scan_ok h]
    constructor
    · intro he; exact nomatch he
    · intro he; exact nomatch he

/-- **THE BREAK.** `EC1-T015` as landed places NO constraint on `check`.

For every checker there exists a `Clauses` record making the landed
`first_diagnostic_iff` hold of it verbatim. So the row's content is entirely in
the `C` the packet has never declared; the theorem itself excludes no checker.

This is the SAME defect `T015.lean` §5 exhibits and claims to have escaped —
`FirstReject` is again "whatever the checker said", laundered through a scan
order chosen after the fact. -/
theorem row_constrains_no_checker (check : Raw → Except Diag Payload) :
    ∃ C : Clauses Raw Diag Diag, ∀ r d, check r = .error d ↔ FirstReject C r d :=
  ⟨reverseEngineered check,
    fun r d => first_diagnostic_iff (reverse_errorBranch check) r d⟩

end Universal

/-! ## A2. `EC1-F81` flips green under the landed statement

`EC1-F81`: one raw program, two independent defects, demand the LATER
diagnostic. The brief requires this falsifier to stay RED.

`Mini.w = ⟨[7,7], [(1,2)]⟩` has exactly two independent defects in two
different clause families: a duplicate id at `.idAt 1` and a type mismatch at
`.typAt 0`. In the canonical order the duplicate is FIRST. The file's own rival
checker reports the type mismatch — the LATER defect.

Feeding that rival through §A1 produces a `Clauses` record under which
`EC1-T015` certifies the LATER diagnostic as the first reject. -/

namespace F81

open EffectCoreT015.Mini

/-- The rival, packaged as a checker in `EC1-D024`'s `Except` shape. -/
def rivalCheck (r : Raw) : Except Diag Unit :=
  checkClauses (C.withScan kindFirstOrder) r

/-- The rival answers with the LATER of `w`'s two defects. -/
theorem rivalCheck_reports_the_later :
    rivalCheck w = .error (.typeMismatch (.typAt 0) 1 2) :=
  rival_reports_mismatch

/-- The canonical checker answers with the EARLIER defect. -/
theorem canonical_reports_the_earlier :
    checkClauses C w = .error (.dupId (.idAt 1) 7) :=
  canonical_reports_dup

/-- Both defects are real, and they are independent (different clause
families, different tables). -/
theorem two_independent_defects :
    C.Bad w (.idAt 1) ∧ C.Bad w (.typAt 0) :=
  ⟨w_idAt1_bad, w_typAt0_bad⟩

/-- **`EC1-F81` IS GREEN under the landed statement.**

`EC1-T015` as landed certifies the LATER diagnostic of a two-defect program as
`FirstReject`, while the canonical order's `FirstReject` rejects it. The row
therefore does not pin the reported diagnostic of a two-defect program; the
undeclared `C` does. -/
theorem f81_is_green :
    rivalCheck w = .error (.typeMismatch (.typAt 0) 1 2)
      ∧ FirstReject (reverseEngineered rivalCheck) w (.typeMismatch (.typAt 0) 1 2)
      ∧ ¬ FirstReject C w (.typeMismatch (.typAt 0) 1 2) :=
  ⟨rivalCheck_reports_the_later,
   (first_diagnostic_iff (reverse_errorBranch rivalCheck) w _).mp
     rivalCheck_reports_the_later,
   rival_violates_firstReject⟩

/-- And it is green in the strong sense: the reverse-engineered order is a
LEGITIMATE `Clauses` record — total, first-order, with per-clause reflection
discharged — not a degenerate one the packet could rule out by shape. -/
theorem f81_witness_is_a_real_clauses_record :
    (reverseEngineered rivalCheck).scan w = [Diag.typeMismatch (.typAt 0) 1 2]
      ∧ (reverseEngineered rivalCheck).badB w (.typeMismatch (.typAt 0) 1 2) = true :=
  ⟨rfl, rfl⟩

end F81

/-! ## A3. `Pos := Path` is not available, and freezing `scan` is not enough

`T015.lean` §1 states the intended instantiation is `Pos := Path`. The report's
compatibility section then asks the coordinator to rule on the clause ORDER,
calling it "the one real divergence risk".

Both are wrong in the same way. `clauseAt : Raw -> Pos -> Diag` is a FUNCTION
of the position, so at most ONE clause may fire per position. When two of the
twelve `ALGEBRA.md` clauses can condemn the same table row — which is what
`Pos := Path` means — the tie-break lives in `clauseAt`, where `scan` cannot
see it. Freezing the scan order does not freeze the answer. -/

namespace TieBreak

/-- One raw input, one position, two rival diagnostics for it. -/
inductive Diag where
  | dupHere
  | mismatchHere
  deriving DecidableEq

/-- Clause record A: at the shared position, the duplicate clause wins. -/
def A : Clauses Unit Unit Diag where
  scan := fun _ => [()]
  badB := fun _ _ => true
  Bad := fun _ _ => True
  badB_iff := fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩
  clauseAt := fun _ _ => .dupHere

/-- Clause record B: same scan, same judgment, the mismatch clause wins. -/
def B : Clauses Unit Unit Diag where
  scan := fun _ => [()]
  badB := fun _ _ => true
  Bad := fun _ _ => True
  badB_iff := fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩
  clauseAt := fun _ _ => .mismatchHere

theorem same_scan : A.scan = B.scan := rfl
theorem same_badB : A.badB = B.badB := rfl
theorem same_Bad : A.Bad = B.Bad := rfl

/-- **Freezing the scan order does not determine the diagnostic.** Two records
agreeing on `scan`, `badB` and `Bad` report different diagnostics, and both
satisfy the landed row. -/
theorem order_does_not_determine_the_diagnostic :
    A.scan = B.scan ∧ A.Bad = B.Bad
      ∧ FirstReject A () .dupHere
      ∧ FirstReject B () .mismatchHere
      ∧ ¬ FirstReject A () .mismatchHere := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact (checkClauses_error_iff A () _).mp rfl
  · exact (checkClauses_error_iff B () _).mp rfl
  · intro h
    have hx := (checkClauses_error_iff A () _).mpr h
    exact absurd (Except.error.inj (hx.symm.trans (rfl : checkClauses A () = .error Diag.dupHere)))
      (by decide)

end TieBreak

/-! ## A4. The decidability obligation the row incurs without claiming it

The report states, correctly, that it makes no decidability claim: `badB` is a
FIELD. But `badB_iff` means any `Clauses` instance for `EC1-D021 ProgramWF`
DECIDES every one of the twelve clauses. So the row's instance obligation is at
least as strong as the condition `PROOF-DAG.md:221` attaches to
`EC1-T011`/`EC1-T012`, and `EC1-T015` falls under the same prohibition through
its instance even though its statement is silent. -/

/-- A `Clauses` record decides its own per-clause judgment. -/
instance clausesDecides {Raw Pos Diag : Type} (C : Clauses Raw Pos Diag)
    (r : Raw) (p : Pos) : Decidable (C.Bad r p) :=
  decidable_of_iff _ (C.badB_iff r p)

/-- Stated as a theorem, so the obligation is on the record and not on a
typeclass search: a `Clauses` instance for a family of judgments makes every
member of the family decidable. -/
theorem clauses_forces_decidability {Raw Pos Diag : Type}
    (C : Clauses Raw Pos Diag) (r : Raw) (p : Pos) :
    C.Bad r p ∨ ¬ C.Bad r p := by
  cases h : C.badB r p with
  | true => exact Or.inl (bad_of_decide h)
  | false => exact Or.inr (not_bad_of_decide h)

/-! ## A5. What genuinely survives

The core induction is real content, and the following all hold. They are
re-derived here from the landed declarations, not asserted. -/

namespace Survives

open EffectCoreT015.Mini

/-- `EC1-F81` stays RED relative to a FIXED clause record. This is what the
landed file actually establishes, and it is worth having. -/
theorem f81_red_at_fixed_C :
    ¬ FirstReject C w (.typeMismatch (.typAt 0) 1 2) :=
  rival_violates_firstReject

/-- The diagnostic is UNIQUE at a fixed record — a corollary of the landed
`iff` that the file does not state, and the property a "the diagnostic" reading
needs. -/
theorem diagnostic_unique {Raw Pos Diag : Type} (C : Clauses Raw Pos Diag)
    (r : Raw) (d₁ d₂ : Diag)
    (h₁ : FirstReject C r d₁) (h₂ : FirstReject C r d₂) : d₁ = d₂ := by
  have e₁ := (checkClauses_error_iff C r d₁).mpr h₁
  have e₂ := (checkClauses_error_iff C r d₂).mpr h₂
  exact Except.error.inj (e₁.symm.trans e₂)

/-- No accumulating reading is smuggled in: at the fixed record, `w`'s second
condemning clause is real, scanned, and NOT reported. `EC1-CE031` holds. -/
theorem ce031_holds :
    C.Bad w (.typAt 0) ∧ ¬ FirstReject C w (C.clauseAt w (.typAt 0)) :=
  ⟨w_typAt0_bad, rival_violates_firstReject⟩

/-- The CAS reuse receipt is genuine: the estate's shipped checker really is
the scanner, and the row at CAS scale follows. Re-checked here against the
landed declaration. -/
theorem cas_receipt_holds (σ : Cas.Store) (rs : List Cas.Ref) (e : Cas.AdmissionError) :
    Cas.checkRefs σ rs = .error e ↔ FirstReject (CasBridge.casClauses σ) rs e :=
  CasBridge.checkRefs_firstReject_iff σ rs e

/-- The literal DAG conclusion really has no witness: two inputs, same
position, same code, different payload. Re-checked. -/
theorem literal_row_refuted :
    checkClauses C wA = .error (.typeMismatch (.typAt 0) 1 2)
      ∧ checkClauses C wB = .error (.typeMismatch (.typAt 0) 1 3)
      ∧ dpos (Diag.typeMismatch (.typAt 0) 1 2) = dpos (Diag.typeMismatch (.typAt 0) 1 3)
      ∧ dcode (Diag.typeMismatch (.typAt 0) 1 2) = dcode (Diag.typeMismatch (.typAt 0) 1 3) :=
  ⟨checkA, checkB, rfl, rfl⟩

end Survives

end AttackT015

/-! ## Axiom receipts -/

#print axioms AttackT015.reverse_errorBranch
#print axioms AttackT015.row_constrains_no_checker
#print axioms AttackT015.F81.rivalCheck_reports_the_later
#print axioms AttackT015.F81.canonical_reports_the_earlier
#print axioms AttackT015.F81.two_independent_defects
#print axioms AttackT015.F81.f81_is_green
#print axioms AttackT015.F81.f81_witness_is_a_real_clauses_record
#print axioms AttackT015.TieBreak.same_scan
#print axioms AttackT015.TieBreak.same_Bad
#print axioms AttackT015.TieBreak.order_does_not_determine_the_diagnostic
#print axioms AttackT015.clauses_forces_decidability
#print axioms AttackT015.Survives.f81_red_at_fixed_C
#print axioms AttackT015.Survives.diagnostic_unique
#print axioms AttackT015.Survives.ce031_holds
#print axioms AttackT015.Survives.cas_receipt_holds
#print axioms AttackT015.Survives.literal_row_refuted
