import Cas.Core.Admission

/-!
# `EC1-T015` — first-error diagnostic completeness, implemented

Slice `EC1-S2` (admission boundary), row `EC1-T015`. Implementer artifact.
Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Diagnostic.lean`; that module is
still a reserved empty boundary (verified by reading it). This file borrows
`library/cas`'s environment and is in no lake target.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/T015.lean
```

## The DAG row

```text
EC1-T015  first_diagnostic_complete :
            FirstReject r path code -> check r = error (diagnostic path code)
          Depends on: canonical checker order;
                      existing checkRefs_error_condemns / checkRefs_complete shape
```

`EC1-CE031` (`VERIFIED-KERNEL`) already killed this row's earlier
per-condemning-clause form. `R16` then ruled checker semantics FIRST-ERROR,
with first-error soundness plus EXISTENTIAL rejection completeness as the
admissible pair. The row stays first-error here; §8.5 is the kernel receipt
that `EC1-CE031` is not resurrected.

## Lean skill stage

`lean-algebraic-systems` — the row is about a checker, i.e. an interpreter over
a declared scan order, not a data invariant. Its proof-tool routing table sends
"pure recursive interpreter/fold" to "structural induction and simp lemmas for
constructors", which is the route taken in §2 and is also `PROOF-DAG.md:518`'s
Checker row verbatim: *structural recursion plus decidable per-clause
reflection*. Its gate asks for constructor/step equations (§1), interpreter
preservation laws (§2–§3), the observable the theorem names (§3: the WHOLE
diagnostic), and deliberately invalid inputs (§8).

## What is proved, and how it differs from the row

The signature as written fails twice, and both failures are exhibited, not
asserted:

* it is VACUOUS if `FirstReject` is spelled through the checker (§5: proof term
  `id`);
* it is FALSE if read literally, because `error (diagnostic path code)` makes
  the returned diagnostic a function of position and clause code alone, while
  the diagnostic family carries payload beyond those two (§7, §8.4).

What IS proved is the two-sided, whole-diagnostic form:

```text
first_diagnostic_iff : check r = .error d  <->  FirstReject C r d
```

over a scan order `C.scan` DECLARED independently of the checker. Every
declaration the statement needs is in §1 and is first-order.

The theorem is stated over an abstract `Raw`, so it assumes NOTHING from slice
`EC1-S1`: `EC1-D020 RawProgram`'s eventual shape is irrelevant to first-error
completeness. What the row does need is three declarations, two of which the
packet does not have.

## Compatibility with the seven sibling rows

Six sibling agents are building `check` in `Admission/Check.lean` right now.
This file does not build a second checker. It isolates the ONLY property of
`check` that `EC1-T015` uses (§4, `ErrorBranchIsClauseScan`: the error branch is
the clause scan) and proves the row for EVERY `check` with that property,
whatever its `ok`-branch payload — `Sigma CheckedProgram` or otherwise. §9 then
proves the estate's own shipped `Cas.checkRefs` IS an instance of the scanner,
so no second CAS checker is minted either.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` used as a claim.
`#print axioms` for every theorem is at the foot.
-/

namespace EffectCoreT015

/-! ## 1. The carrier: a declared scan order and per-clause reflection

Three declarations. `scan` is a TOTAL function on the raw input and is what
makes the row non-vacuous: the DAG's dependency column says "canonical checker
order", and without `scan` as a separate object that phrase has no referent.
`badB`/`Bad`/`badB_iff` is `PROOF-DAG.md:518`'s "decidable per-clause
reflection" spelled out. `clauseAt` is payload-carrying by construction — its
codomain is the whole `Diag`, never a `(position, code)` pair. -/

/-- A fail-fast clause checker's DATA, with `check` nowhere in sight.

At the intended home this is instantiated with `Pos := Path`,
`Diag := EC1-D022 Diagnostic`, `Raw := EC1-D020 RawProgram`, `scan` the frozen
traversal of the twelve `ALGEBRA.md` §4.3 clauses, and one `badB`/`clauseAt`
pair per clause. -/
structure Clauses (Raw Pos Diag : Type) where
  /-- The canonical scan order. DECLARED, not read off any checker's recursion. -/
  scan : Raw → List Pos
  /-- The per-clause decision. -/
  badB : Raw → Pos → Bool
  /-- The per-clause judgment the decision reflects. -/
  Bad : Raw → Pos → Prop
  /-- Per-clause reflection. -/
  badB_iff : ∀ r p, badB r p = true ↔ Bad r p
  /-- The diagnostic a bad position produces. Total; its value at a good
  position is never consulted. -/
  clauseAt : Raw → Pos → Diag

section Generic

variable {Raw Pos Diag Payload : Type}

/-- Fail-fast scan of an explicit position list. Structural recursion, one
step per position — the §16 Checker route. -/
def checkFrom (C : Clauses Raw Pos Diag) (r : Raw) : List Pos → Except Diag Unit
  | [] => .ok ()
  | p :: ps => if C.badB r p then .error (C.clauseAt r p) else checkFrom C r ps

/-! ### Constructor/step equations -/

theorem checkFrom_nil (C : Clauses Raw Pos Diag) (r : Raw) :
    checkFrom C r [] = .ok () := rfl

theorem checkFrom_cons (C : Clauses Raw Pos Diag) (r : Raw) (p : Pos) (ps : List Pos) :
    checkFrom C r (p :: ps)
      = if C.badB r p then .error (C.clauseAt r p) else checkFrom C r ps := rfl

theorem checkFrom_cons_bad {C : Clauses Raw Pos Diag} {r : Raw} {p : Pos}
    (ps : List Pos) (h : C.Bad r p) :
    checkFrom C r (p :: ps) = .error (C.clauseAt r p) := by
  rw [checkFrom_cons, if_pos ((C.badB_iff r p).mpr h)]

theorem checkFrom_cons_good {C : Clauses Raw Pos Diag} {r : Raw} {p : Pos}
    (ps : List Pos) (h : ¬ C.Bad r p) :
    checkFrom C r (p :: ps) = checkFrom C r ps := by
  refine (checkFrom_cons C r p ps).trans (if_neg ?_)
  intro hb
  exact h ((C.badB_iff r p).mp hb)

/-! ### Per-clause reflection, used in place of `by_cases`

Splitting on the abstract `C.Bad r p` would need excluded middle; splitting on
the `Bool` decision does not. Every proof below therefore cases on `C.badB`,
which is why no theorem in this file reports `Classical.choice`. That is not
cosmetic: `PROOF-DAG.md:221` prohibits `EC1-T011`/`EC1-T012` if a clause goes
undecidable, and a `Classical.choice` receipt is the only kernel-visible sign
that the prohibition has been breached. -/

theorem bad_of_decide {C : Clauses Raw Pos Diag} {r : Raw} {p : Pos}
    (h : C.badB r p = true) : C.Bad r p := (C.badB_iff r p).mp h

theorem not_bad_of_decide {C : Clauses Raw Pos Diag} {r : Raw} {p : Pos}
    (h : C.badB r p = false) : ¬ C.Bad r p := fun hb =>
  Bool.noConfusion (h.symm.trans ((C.badB_iff r p).mpr hb))

/-! ## 2. `FirstReject`, stated WITHOUT naming the checker

This is the load-bearing definitional choice. The list splits at a bad
position; every EARLIER position in the DECLARED order is good; the diagnostic
is that position's clause. `checkFrom` does not appear. -/

/-- First reject within an explicit position list. -/
def FirstRejectIn (C : Clauses Raw Pos Diag) (r : Raw) (ps : List Pos) (d : Diag) : Prop :=
  ∃ pre p post,
    ps = pre ++ p :: post ∧ (∀ q ∈ pre, ¬ C.Bad r q) ∧ C.Bad r p ∧ d = C.clauseAt r p

/-- Acceptance, in the estate's `checkRefs_ok_iff` house shape. Not this row;
stated because the `Except` two-arm split below needs it, and because it is the
clause-layer half `EC1-T010`/`EC1-T011` will want. -/
theorem checkFrom_ok_iff (C : Clauses Raw Pos Diag) (r : Raw) :
    ∀ ps : List Pos, checkFrom C r ps = .ok () ↔ ∀ q ∈ ps, ¬ C.Bad r q := by
  intro ps
  induction ps with
  | nil =>
    constructor
    · intro _ q hq; exact absurd hq (by simp)
    · intro _; exact checkFrom_nil C r
  | cons p ps ih =>
    cases hdec : C.badB r p with
    | true =>
      have hb : C.Bad r p := bad_of_decide hdec
      rw [checkFrom_cons_bad ps hb]
      constructor
      · intro h; exact nomatch h
      · intro h; exact absurd hb (h p List.mem_cons_self)
    | false =>
      have hb : ¬ C.Bad r p := not_bad_of_decide hdec
      rw [checkFrom_cons_good ps hb]
      constructor
      · intro h q hq
        rcases List.mem_cons.mp hq with hqp | hq'
        · exact hqp ▸ hb
        · exact ih.mp h q hq'
      · intro h
        exact ih.mpr fun q hq => h q (List.mem_cons_of_mem p hq)

/-- **The core result.** First-error SOUNDNESS (left to right) and first-error
COMPLETENESS (right to left) in one `iff`, over the WHOLE diagnostic. Proved by
structural induction on the position list plus per-clause reflection. -/
theorem checkFrom_error_iff (C : Clauses Raw Pos Diag) (r : Raw) :
    ∀ (ps : List Pos) (d : Diag),
      checkFrom C r ps = .error d ↔ FirstRejectIn C r ps d := by
  intro ps
  induction ps with
  | nil =>
    intro d
    constructor
    · intro h; exact nomatch h
    · rintro ⟨pre, p, post, hsplit, -, -, -⟩
      cases pre <;> simp at hsplit
  | cons p ps ih =>
    intro d
    cases hdec : C.badB r p with
    | true =>
      have hb : C.Bad r p := bad_of_decide hdec
      rw [checkFrom_cons_bad ps hb]
      constructor
      · intro h
        exact ⟨[], p, ps, rfl, by simp, hb, (Except.error.inj h).symm⟩
      · rintro ⟨pre, p', post, hsplit, hpre, hbad', hd⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          rw [hd, ← hsplit.1]
        | cons x pre' =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          exact absurd (hsplit.1 ▸ hb) (hpre x List.mem_cons_self)
    | false =>
      have hb : ¬ C.Bad r p := not_bad_of_decide hdec
      rw [checkFrom_cons_good ps hb]
      constructor
      · intro h
        obtain ⟨pre, p', post, hsplit, hpre, hbad', hd⟩ := (ih d).mp h
        refine ⟨p :: pre, p', post, by rw [List.cons_append, hsplit], ?_, hbad', hd⟩
        intro q hq
        rcases List.mem_cons.mp hq with hqp | hq'
        · exact hqp ▸ hb
        · exact hpre q hq'
      · rintro ⟨pre, p', post, hsplit, hpre, hbad', hd⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          exact absurd (hsplit.1 ▸ hbad') hb
        | cons x pre' =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          exact (ih d).mpr ⟨pre', p', post, hsplit.2,
            fun q hq => hpre q (List.mem_cons_of_mem x hq), hbad', hd⟩

/-! ## 3. The row, at the clause layer -/

/-- The clause checker: the fail-fast scan of the DECLARED order. -/
def checkClauses (C : Clauses Raw Pos Diag) (r : Raw) : Except Diag Unit :=
  checkFrom C r (C.scan r)

/-- `EC1-T015`'s subject, checker-free. -/
def FirstReject (C : Clauses Raw Pos Diag) (r : Raw) (d : Diag) : Prop :=
  FirstRejectIn C r (C.scan r) d

/-- `EC1-T015` at the clause layer. -/
theorem checkClauses_error_iff (C : Clauses Raw Pos Diag) (r : Raw) (d : Diag) :
    checkClauses C r = .error d ↔ FirstReject C r d :=
  checkFrom_error_iff C r (C.scan r) d

theorem checkClauses_ok_iff (C : Clauses Raw Pos Diag) (r : Raw) :
    checkClauses C r = .ok () ↔ ∀ q ∈ C.scan r, ¬ C.Bad r q :=
  checkFrom_ok_iff C r (C.scan r)

instance instDecEqExceptUnit [DecidableEq Diag] : DecidableEq (Except Diag Unit)
  | .ok (), .ok () => isTrue rfl
  | .ok (), .error _ => isFalse (fun h => by cases h)
  | .error _, .ok () => isFalse (fun h => by cases h)
  | .error a, .error b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun he => h (Except.error.inj he))

/-- The rejection judgment is DECIDED by the checker, not merely reflected by
it. Obtained as a corollary; not assumed as a premise. -/
instance instDecidableFirstReject [DecidableEq Diag]
    (C : Clauses Raw Pos Diag) (r : Raw) (d : Diag) : Decidable (FirstReject C r d) :=
  decidable_of_iff _ (checkClauses_error_iff C r d)

/-! ## 4. The row at `EC1-D024 check`'s own codomain

`R15`/`EC1-CE033` fix `check`'s codomain to the partial arm
`Except Diagnostic (Sigma CheckedProgram)`. The row is about the ERROR branch
only, so it is independent of whatever the six sibling agents make the payload.
That independence is stated and proved here rather than guessed at. -/

/-- The only property of `check` that `EC1-T015` uses. -/
def ErrorBranchIsClauseScan (C : Clauses Raw Pos Diag)
    (check : Raw → Except Diag Payload) : Prop :=
  ∀ r d, check r = .error d ↔ checkClauses C r = .error d

/-- **`EC1-T015`, RESTATED AND PROVED.**

`check r = .error d ↔ FirstReject C r d`, quantified over the WHOLE diagnostic
`d` and over a scan order declared independently of `check`.

Divergence from the DAG signature, exactly: the implication became an `iff`
(both directions are owed, and the estate's house shape `checkRefs_ok_iff`
packages them as one); and `error (diagnostic path code)` became `.error d`,
because §7 proves no `diagnostic : Pos -> Code -> Diag` exists. -/
theorem first_diagnostic_iff {C : Clauses Raw Pos Diag}
    {check : Raw → Except Diag Payload} (hcheck : ErrorBranchIsClauseScan C check)
    (r : Raw) (d : Diag) :
    check r = .error d ↔ FirstReject C r d :=
  (hcheck r d).trans (checkClauses_error_iff C r d)

/-- The DAG's `path` view survives only as a PROJECTION, and only because
`clauseAt` stamps the position into the diagnostic. -/
theorem first_diagnostic_path {C : Clauses Raw Pos Diag}
    {check : Raw → Except Diag Payload} (hcheck : ErrorBranchIsClauseScan C check)
    (dpos : Diag → Pos) (hstamp : ∀ r p, dpos (C.clauseAt r p) = p)
    (r : Raw) (d : Diag) (h : check r = .error d) :
    ∃ p, FirstReject C r d ∧ dpos d = p ∧ d = C.clauseAt r p := by
  obtain ⟨pre, p, post, hsplit, hpre, hbad, hd⟩ := (first_diagnostic_iff hcheck r d).mp h
  exact ⟨p, ⟨pre, p, post, hsplit, hpre, hbad, hd⟩, by rw [hd, hstamp], hd⟩

/-- A concrete inhabitant of the hypothesis, in `EC1-D024`'s codomain shape:
partial by construction (`R15`), payload built on the `ok` branch only. The
payload type and its constructor are abstract, so nothing here commits to
`EC1-D023 CheckedProgram`. -/
def checkOf (C : Clauses Raw Pos Diag) (mk : Raw → Payload) (r : Raw) :
    Except Diag Payload :=
  match checkClauses C r with
  | .error d => .error d
  | .ok _ => .ok (mk r)

theorem checkOf_errorBranch (C : Clauses Raw Pos Diag) (mk : Raw → Payload) :
    ErrorBranchIsClauseScan C (checkOf C mk) := by
  intro r d
  constructor
  · intro h
    cases hc : checkClauses C r with
    | error d' =>
      have hval : checkOf C mk r = Except.error d' := by simp only [checkOf, hc]
      rw [hval] at h
      rw [Except.error.inj h]
    | ok u =>
      have hval : checkOf C mk r = Except.ok (mk r) := by simp only [checkOf, hc]
      rw [hval] at h
      exact nomatch h
  · intro h
    simp only [checkOf, h]

/-- The `ok` branch does carry the evidence a proof-carrying payload needs, so
nothing is lost by keeping `mk` non-dependent above. Constructing
`CheckedProgram` from this is `EC1-T010`/`EC1-T013`'s business, not this row's. -/
theorem ok_gives_evidence {C : Clauses Raw Pos Diag} {r : Raw}
    (h : checkClauses C r = .ok ()) : ∀ q ∈ C.scan r, ¬ C.Bad r q :=
  (checkClauses_ok_iff C r).mp h

/-! ## 5. The vacuity trap, exhibited

If `FirstReject` is spelled THROUGH the checker, `EC1-T015` is a tautology over
a Lean function — the defect that already deleted rows from this packet. The
proof term is `id`. This is why `scan` must be a declared object. -/

/-- The tempting checker-relative spelling. -/
def FirstRejectByChecker (check : Raw → Except Diag Payload) (r : Raw) (d : Diag) : Prop :=
  check r = .error d

/-- `EC1-T015` under the checker-relative spelling: proved by `id`, with no
`Clauses`, no scan order, and no reflection. -/
theorem T015_is_vacuous_under_checker_relative_firstReject
    (check : Raw → Except Diag Payload) (r : Raw) (d : Diag) :
    FirstRejectByChecker check r d → check r = .error d :=
  id

/-! ## 6. `R16`'s admissible pair — and the proof that it is not enough

`R16` rules the admissible pair to be first-error soundness plus EXISTENTIAL
rejection completeness. Both are proved generically here. §8.3 then exhibits a
rival checker that satisfies the whole pair and still reports a different
diagnostic, so the pair is NECESSARY but NOT SUFFICIENT — the declared scan
order is what closes the gap. `R16` does not say this. -/

/-- First-error soundness, generic: what is reported is a real violation at a
real scanned position. Strengthens the estate's `checkRefs_error_condemns`,
which only says the clause condemns SOMEWHERE. -/
theorem checkClauses_error_sound {C : Clauses Raw Pos Diag} {r : Raw} {d : Diag}
    (h : checkClauses C r = .error d) :
    ∃ p ∈ C.scan r, C.Bad r p ∧ d = C.clauseAt r p := by
  obtain ⟨pre, p, post, hsplit, -, hbad, hd⟩ := (checkClauses_error_iff C r d).mp h
  exact ⟨p, by rw [hsplit]; exact List.mem_append_right pre List.mem_cons_self, hbad, hd⟩

/-- Existential rejection completeness, generic. -/
theorem checkClauses_complete {C : Clauses Raw Pos Diag} {r : Raw}
    (h : ∃ p ∈ C.scan r, C.Bad r p) : ∃ d, checkClauses C r = .error d := by
  cases hc : checkClauses C r with
  | error d => exact ⟨d, rfl⟩
  | ok u =>
    obtain ⟨p, hp, hbad⟩ := h
    cases u
    exact absurd hbad ((checkClauses_ok_iff C r).mp hc p hp)

/-- Same clauses, different declared order. -/
def Clauses.withScan (C : Clauses Raw Pos Diag) (s : Raw → List Pos) :
    Clauses Raw Pos Diag :=
  { C with scan := s }

theorem withScan_scan (C : Clauses Raw Pos Diag) (s : Raw → List Pos) :
    (C.withScan s).scan = s := rfl

theorem withScan_Bad (C : Clauses Raw Pos Diag) (s : Raw → List Pos) :
    (C.withScan s).Bad = C.Bad := rfl

theorem withScan_clauseAt (C : Clauses Raw Pos Diag) (s : Raw → List Pos) :
    (C.withScan s).clauseAt = C.clauseAt := rfl

/-- A rival that reorders the SAME clauses over the SAME positions satisfies
`R16`'s admissible pair in full, stated against the CANONICAL position set. -/
theorem rival_satisfies_R16 (C : Clauses Raw Pos Diag) (s : Raw → List Pos)
    (hmem : ∀ r q, q ∈ s r ↔ q ∈ C.scan r) :
    (∀ r d, checkClauses (C.withScan s) r = .error d →
        ∃ p ∈ C.scan r, C.Bad r p ∧ d = C.clauseAt r p)
      ∧ (∀ r, (∃ p ∈ C.scan r, C.Bad r p) →
            ∃ d, checkClauses (C.withScan s) r = .error d) := by
  constructor
  · intro r d h
    obtain ⟨p, hp, hbad, hd⟩ := checkClauses_error_sound h
    exact ⟨p, (hmem r p).mp hp, hbad, hd⟩
  · intro r h
    obtain ⟨p, hp, hbad⟩ := h
    exact checkClauses_complete ⟨p, (hmem r p).mpr hp, hbad⟩

/-! ## 7. The DAG's LITERAL conclusion has no witness

`check r = error (diagnostic path code)` makes the returned diagnostic a
function of the position and the clause code ALONE. Refuted whenever the
diagnostic family carries payload beyond those two — which the estate's own
family does (`AdmissionError.wrongKind ref expected actual`). -/

theorem no_diagnostic_from_pos_and_code {Code : Type} {C : Clauses Raw Pos Diag}
    (dpos : Diag → Pos) (dcode : Diag → Code)
    {r₁ r₂ : Raw} {d₁ d₂ : Diag}
    (h₁ : checkClauses C r₁ = .error d₁) (h₂ : checkClauses C r₂ = .error d₂)
    (hpos : dpos d₁ = dpos d₂) (hcode : dcode d₁ = dcode d₂) (hne : d₁ ≠ d₂) :
    ¬ ∃ diagnostic : Pos → Code → Diag,
        ∀ r d, checkClauses C r = .error d → d = diagnostic (dpos d) (dcode d) := by
  rintro ⟨f, hf⟩
  exact hne (((hf r₁ d₁ h₁).trans (by rw [hpos, hcode])).trans (hf r₂ d₂ h₂).symm)

end Generic

/-! ## 8. A multi-clause instance

Everything above is one clause family wide only if `Bad` is. It is not: `Bad`
and `clauseAt` are arbitrary, so the twelve `ALGEBRA.md` §4.3 clauses are the
intended instance. This section exercises the theorem at TWO clause families
over TWO tables, with a payload-carrying diagnostic and a frozen clause order,
to show the widening is real and to supply the negative witnesses.

`Mini` is a deliberately small stand-in and is NOT proposed as `EC1-D020`. -/

namespace Mini

/-- Stand-in for `EC1-D020 RawProgram`: two tables, one per clause family. -/
structure Raw where
  ids : List Nat
  typs : List (Nat × Nat)
  deriving DecidableEq

/-- Stand-in for the MISSING `Path` declaration: a clause family plus a table
row. `EC1-T015`'s signature names `path` and no `EC1-D0xx` row declares it. -/
inductive Pos where
  | idAt (i : Nat)
  | typAt (i : Nat)
  deriving DecidableEq

/-- Stand-in for `EC1-D022 Diagnostic`, PAYLOAD-CARRYING in the shape of
`Cas.AdmissionError.wrongKind ref expected actual`. -/
inductive Diag where
  | dupId (pos : Pos) (key : Nat)
  | typeMismatch (pos : Pos) (expected actual : Nat)
  deriving DecidableEq

/-- The clause CODE — the row's second index. -/
inductive Code where
  | dup
  | mismatch
  deriving DecidableEq

def dpos : Diag → Pos
  | .dupId p _ => p
  | .typeMismatch p _ _ => p

def dcode : Diag → Code
  | .dupId _ _ => .dup
  | .typeMismatch _ _ _ => .mismatch

/-- First-order accessor, hand-rolled so the file depends on no list API. -/
def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth as n

/-- `occursBefore l k i = true` exactly when `k` occurs among the first `i`
entries of `l`. -/
def occursBefore : List Nat → Nat → Nat → Bool
  | [], _, _ => false
  | _ :: _, _, 0 => false
  | x :: xs, k, n + 1 => if x = k then true else occursBefore xs k n

/-- Clause 1 surrogate (`IdsWF`: duplicate-free) and clause 2 surrogate
(`TypesWF`: declared and actual agree exactly). -/
def decideClause (r : Raw) : Pos → Bool
  | .idAt i =>
      match nth r.ids i with
      | none => false
      | some k => occursBefore r.ids k i
  | .typAt i =>
      match nth r.typs i with
      | none => false
      | some q => if q.1 = q.2 then false else true

def diagAt (r : Raw) : Pos → Diag
  | .idAt i => .dupId (.idAt i) ((nth r.ids i).getD 0)
  | .typAt i =>
      .typeMismatch (.typAt i) ((nth r.typs i).getD (0, 0)).1 ((nth r.typs i).getD (0, 0)).2

def idPositions : List Nat → Nat → List Pos
  | [], _ => []
  | _ :: xs, i => .idAt i :: idPositions xs (i + 1)

def typPositions : List (Nat × Nat) → Nat → List Pos
  | [], _ => []
  | _ :: xs, i => .typAt i :: typPositions xs (i + 1)

/-- The CANONICAL order: clause 1 before clause 2. -/
def canonicalOrder (r : Raw) : List Pos := idPositions r.ids 0 ++ typPositions r.typs 0

/-- The RIVAL order: clause 2 before clause 1. Same clauses, same positions. -/
def kindFirstOrder (r : Raw) : List Pos := typPositions r.typs 0 ++ idPositions r.ids 0

theorem kindFirstOrder_mem (r : Raw) (q : Pos) : q ∈ kindFirstOrder r ↔ q ∈ canonicalOrder r := by
  simp only [kindFirstOrder, canonicalOrder, List.mem_append]
  exact Or.comm

def C : Clauses Raw Pos Diag where
  scan := canonicalOrder
  badB := decideClause
  Bad := fun r p => decideClause r p = true
  badB_iff := fun _ _ => Iff.rfl
  clauseAt := diagAt

theorem dpos_diagAt (r : Raw) (p : Pos) : dpos (C.clauseAt r p) = p := by
  cases p <;> rfl

/-! ### 8.1 The witness: a raw with TWO condemning clauses -/

/-- `ids` repeats `7` at row 1; `typs` row 0 declares `1` and carries `2`. -/
def w : Raw := ⟨[7, 7], [(1, 2)]⟩

theorem scan_w : C.scan w = [.idAt 0, .idAt 1, .typAt 0] := rfl

theorem w_idAt1_bad : C.Bad w (.idAt 1) := rfl

theorem w_typAt0_bad : C.Bad w (.typAt 0) := rfl

theorem w_idAt0_good : ¬ C.Bad w (.idAt 0) := by
  show ¬ (decideClause w (Pos.idAt 0) = true)
  decide

/-! ### 8.2 The canonical checker reports the first reject -/

theorem canonical_reports_dup :
    checkClauses C w = .error (.dupId (.idAt 1) 7) := rfl

theorem firstReject_w : FirstReject C w (.dupId (.idAt 1) 7) :=
  (checkClauses_error_iff C w _).mp canonical_reports_dup

/-! ### 8.3 The rival reports a different diagnostic -/

theorem rival_reports_mismatch :
    checkClauses (C.withScan kindFirstOrder) w = .error (.typeMismatch (.typAt 0) 1 2) := rfl

/-- The rival satisfies `R16`'s admissible pair in full. -/
theorem rival_is_R16_admissible :
    (∀ r d, checkClauses (C.withScan kindFirstOrder) r = .error d →
        ∃ p ∈ C.scan r, C.Bad r p ∧ d = C.clauseAt r p)
      ∧ (∀ r, (∃ p ∈ C.scan r, C.Bad r p) →
            ∃ d, checkClauses (C.withScan kindFirstOrder) r = .error d) :=
  rival_satisfies_R16 C kindFirstOrder kindFirstOrder_mem

/-- **The restated row has content.** The rival is sound and existentially
complete, and its answer is NOT the first reject of the canonical order. So
`R16`'s pair does not determine the reported diagnostic; the DECLARED scan
order does. -/
theorem rival_violates_firstReject :
    ¬ FirstReject C w (.typeMismatch (.typAt 0) 1 2) := by
  intro h
  have hx := (checkClauses_error_iff C w _).mpr h
  rw [canonical_reports_dup] at hx
  exact absurd (Except.error.inj hx) (by decide)

/-! ### 8.4 The DAG's literal signature, refuted at the multi-clause scale

Two raw inputs reject at the SAME position under the SAME clause code with
DIFFERENT payloads. -/

def wA : Raw := ⟨[], [(1, 2)]⟩
def wB : Raw := ⟨[], [(1, 3)]⟩

theorem checkA : checkClauses C wA = .error (.typeMismatch (.typAt 0) 1 2) := rfl
theorem checkB : checkClauses C wB = .error (.typeMismatch (.typAt 0) 1 3) := rfl

/-- **No `diagnostic : Path -> Code -> Diagnostic` exists.** `EC1-T015` must
quantify over the whole diagnostic; `path` and `code` are projections recovered
afterwards, never the theorem's index. -/
theorem no_diagnostic_from_path_and_code :
    ¬ ∃ diagnostic : Pos → Code → Diag,
        ∀ r d, checkClauses C r = .error d → d = diagnostic (dpos d) (dcode d) :=
  no_diagnostic_from_pos_and_code dpos dcode checkA checkB rfl rfl (by decide)

/-! ### 8.5 `EC1-CE031` is NOT resurrected

On the witness a SECOND clause still condemns the input and is still not the
reported diagnostic. First-error completeness does not, and must not, promise
it. -/

theorem ce031_survives_the_restatement :
    (C.Bad w (.typAt 0) ∧ (Pos.typAt 0) ∈ C.scan w)
      ∧ ¬ FirstReject C w (C.clauseAt w (.typAt 0)) := by
  refine ⟨⟨w_typAt0_bad, by rw [scan_w]; decide⟩, ?_⟩
  show ¬ FirstReject C w (Diag.typeMismatch (Pos.typAt 0) 1 2)
  exact rival_violates_firstReject

/-! ### 8.6 The `path` corollary at the instance -/

theorem path_corollary (d : Diag) (h : checkOf C (fun r => r) w = .error d) :
    ∃ p, FirstReject C w d ∧ dpos d = p ∧ d = C.clauseAt w p :=
  first_diagnostic_path (checkOf_errorBranch C (fun r => r)) dpos dpos_diagAt w d h

end Mini

/-! ## 9. The estate's shipped checker is an INSTANCE, not a rival

Reuse, never mint. `Cas.checkRefs` (`library/cas/Cas/Core/Admission.lean:49`) is
the corpus's only shipped fail-fast checker. It is exhibited here as a
`Clauses` instance, and §9 proves the scanner computes exactly it. The scout
probe proved a bespoke `checkRefs_firstReject_iff` by its own induction; here the
same statement falls out of the generic theorem, which is the receipt that no
second CAS checker was minted. -/

namespace CasBridge

open Cas

/-- The per-position decision, reflecting the negation of `Cas.RefsOk`'s
per-position half (`Admission.lean:35`). -/
def casBadB (σ : Store) (r : Ref) : Bool :=
  match σ r.addr with
  | none => true
  | some m => if m.tag = r.expectedTag then false else true

/-- The per-position judgment. -/
def casBad (σ : Store) (r : Ref) : Prop :=
  ¬ ∃ m, σ r.addr = some m ∧ m.tag = r.expectedTag

/-- The clause a bad position produces — exactly `checkRefs`'s two arms. -/
def casClause (σ : Store) (r : Ref) : AdmissionError :=
  match σ r.addr with
  | none => .dangling r.addr
  | some m => .wrongKind r.addr r.expectedTag m.tag

/-- Per-clause reflection at the estate's own clause pair. -/
theorem casBadB_iff (σ : Store) (r : Ref) : casBadB σ r = true ↔ casBad σ r := by
  cases hm : σ r.addr with
  | none =>
    constructor
    · intro _
      rintro ⟨m, hm', -⟩
      rw [hm] at hm'
      exact nomatch hm'
    · intro _
      show casBadB σ r = true
      simp only [casBadB, hm]
  | some m =>
    refine Decidable.byCases (p := m.tag = r.expectedTag) (fun ht => ?_) (fun ht => ?_)
    · constructor
      · intro h
        rw [show casBadB σ r = false by simp only [casBadB, hm, if_pos ht]] at h
        exact nomatch h
      · intro h
        exact absurd ⟨m, hm, ht⟩ h
    · constructor
      · intro _
        rintro ⟨m', hm', ht'⟩
        rw [hm] at hm'
        injection hm' with he
        subst he
        exact ht ht'
      · intro _
        show casBadB σ r = true
        simp only [casBadB, hm, if_neg ht]

/-- Constructive converse; no `Classical.choice` is used or needed, because the
clause is decidable. -/
theorem not_casBad_resolves {σ : Store} {r : Ref} (h : ¬ casBad σ r) :
    ∃ m, σ r.addr = some m ∧ m.tag = r.expectedTag := by
  cases hm : σ r.addr with
  | none =>
    refine absurd ?_ h
    rintro ⟨m, hm', -⟩
    rw [hm] at hm'
    exact nomatch hm'
  | some m =>
    refine Decidable.byCases (p := m.tag = r.expectedTag) (fun ht => ?_) (fun ht => ?_)
    · exact ⟨m, rfl, ht⟩
    · refine absurd ?_ h
      rintro ⟨m', hm', ht'⟩
      rw [hm] at hm'
      injection hm' with he
      subst he
      exact ht ht'

def casClauses (σ : Store) : Clauses (List Ref) Ref AdmissionError where
  scan := fun rs => rs
  badB := fun _ r => casBadB σ r
  Bad := fun _ r => casBad σ r
  badB_iff := fun _ r => casBadB_iff σ r
  clauseAt := fun _ r => casClause σ r

/-- **The shipped checker IS the scanner.** `Cas.checkRefs` computes
`checkFrom` at the identity scan order. -/
theorem checkRefs_eq_checkFrom (σ : Store) (rs : List Ref) :
    ∀ ps : List Ref, checkRefs σ ps = checkFrom (casClauses σ) rs ps := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [checkFrom_cons]
    cases hm : σ p.addr with
    | none =>
      have hb : (casClauses σ).badB rs p = true := by
        show casBadB σ p = true
        simp only [casBadB, hm]
      rw [if_pos hb]
      show checkRefs σ (p :: ps) = .error (casClause σ p)
      simp only [checkRefs, hm, casClause]
    | some m =>
      refine Decidable.byCases (p := m.tag = p.expectedTag) (fun ht => ?_) (fun ht => ?_)
      · have hb : (casClauses σ).badB rs p = false := by
          show casBadB σ p = false
          simp only [casBadB, hm, if_pos ht]
        rw [if_neg (by rw [hb]; simp)]
        show checkRefs σ (p :: ps) = _
        simp only [checkRefs, hm, if_pos ht]
        exact ih
      · have hb : (casClauses σ).badB rs p = true := by
          show casBadB σ p = true
          simp only [casBadB, hm, if_neg ht]
        rw [if_pos hb]
        show checkRefs σ (p :: ps) = .error (casClause σ p)
        simp only [checkRefs, hm, if_neg ht, casClause]

/-- `EC1-T015` at the estate's admission scale, derived from the generic
theorem rather than re-proved. -/
theorem checkRefs_firstReject_iff (σ : Store) (rs : List Ref) (e : AdmissionError) :
    checkRefs σ rs = .error e ↔ FirstReject (casClauses σ) rs e := by
  rw [checkRefs_eq_checkFrom σ rs rs]
  exact checkFrom_error_iff (casClauses σ) rs rs e

/-- The estate's own acceptance theorem (`Admission.lean:60`
`checkRefs_ok_iff`) also falls out, which is the check that `casBad` really is
the negation of `RefsOk`'s per-position half and not a lookalike. -/
theorem checkRefs_ok_iff_via_scanner (σ : Store) (rs : List Ref) :
    checkRefs σ rs = .ok () ↔ RefsOk σ rs := by
  rw [checkRefs_eq_checkFrom σ rs rs]
  exact (checkFrom_ok_iff (casClauses σ) rs rs).trans
    ⟨fun h r hr => not_casBad_resolves (h r hr), fun h r hr hb => hb (h r hr)⟩

end CasBridge

end EffectCoreT015

/-! ## Axiom receipts

Every theorem in the file, in declaration order. -/

#print axioms EffectCoreT015.checkFrom_nil
#print axioms EffectCoreT015.checkFrom_cons
#print axioms EffectCoreT015.checkFrom_cons_bad
#print axioms EffectCoreT015.checkFrom_cons_good
#print axioms EffectCoreT015.bad_of_decide
#print axioms EffectCoreT015.not_bad_of_decide
#print axioms EffectCoreT015.checkFrom_ok_iff
#print axioms EffectCoreT015.checkFrom_error_iff
#print axioms EffectCoreT015.checkClauses_error_iff
#print axioms EffectCoreT015.checkClauses_ok_iff
#print axioms EffectCoreT015.first_diagnostic_iff
#print axioms EffectCoreT015.first_diagnostic_path
#print axioms EffectCoreT015.checkOf_errorBranch
#print axioms EffectCoreT015.ok_gives_evidence
#print axioms EffectCoreT015.T015_is_vacuous_under_checker_relative_firstReject
#print axioms EffectCoreT015.checkClauses_error_sound
#print axioms EffectCoreT015.checkClauses_complete
#print axioms EffectCoreT015.withScan_scan
#print axioms EffectCoreT015.withScan_Bad
#print axioms EffectCoreT015.withScan_clauseAt
#print axioms EffectCoreT015.rival_satisfies_R16
#print axioms EffectCoreT015.no_diagnostic_from_pos_and_code
#print axioms EffectCoreT015.Mini.kindFirstOrder_mem
#print axioms EffectCoreT015.Mini.dpos_diagAt
#print axioms EffectCoreT015.Mini.scan_w
#print axioms EffectCoreT015.Mini.w_idAt1_bad
#print axioms EffectCoreT015.Mini.w_typAt0_bad
#print axioms EffectCoreT015.Mini.w_idAt0_good
#print axioms EffectCoreT015.Mini.canonical_reports_dup
#print axioms EffectCoreT015.Mini.firstReject_w
#print axioms EffectCoreT015.Mini.rival_reports_mismatch
#print axioms EffectCoreT015.Mini.rival_is_R16_admissible
#print axioms EffectCoreT015.Mini.rival_violates_firstReject
#print axioms EffectCoreT015.Mini.checkA
#print axioms EffectCoreT015.Mini.checkB
#print axioms EffectCoreT015.Mini.no_diagnostic_from_path_and_code
#print axioms EffectCoreT015.Mini.ce031_survives_the_restatement
#print axioms EffectCoreT015.Mini.path_corollary
#print axioms EffectCoreT015.CasBridge.casBadB_iff
#print axioms EffectCoreT015.CasBridge.not_casBad_resolves
#print axioms EffectCoreT015.CasBridge.checkRefs_eq_checkFrom
#print axioms EffectCoreT015.CasBridge.checkRefs_firstReject_iff
#print axioms EffectCoreT015.CasBridge.checkRefs_ok_iff_via_scanner
