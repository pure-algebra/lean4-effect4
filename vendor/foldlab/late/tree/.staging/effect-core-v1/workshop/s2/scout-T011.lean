import Cas.Core.Admission

/-!
# Effect Core v1 — scout probe for `EC1-T011` (`check_complete`)

Slice `EC1-S2`, the admission boundary. SCOUT ARTEFACT ONLY: nothing here is
proposed for `library/` or for `formal/effect-core-v1/`. It settles six
questions the packet leaves open about the row

```text
EC1-T011  check_complete : ProgramWF r -> exists p, check r = ok <a,p>
```

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T011.lean
```

The carriers `RawProgram`, `ProgramWF`, `Diagnostic`, `CheckedProgram`, `AER`
and `check` (`EC1-D020`–`D024`) do not exist yet — `formal/effect-core-v1/
EffectCore/Admission/Check.lean` is an empty reserved boundary and §17 items 1
and 3 are still OPEN. So every result below is proved of an ARBITRARY checker
of the declared *shape*

```text
run : Raw -> Except D ((a : Alph) x Chk a)
```

which is exactly `EC1-D024`'s `check : RawProgram -> Except Diagnostic (Sigma
CheckedProgram)`. A shape-level theorem transfers to the real checker the
moment `check` has that type, and no sooner. Nothing here claims anything about
the twelve `ProgramWF` clauses of `ALGEBRA.md` §4.3 themselves; §5 and §7 state
what the *architecture* demands of them, not what they are.

| § | Question | Answer |
|---|---|---|
| 1 | Is the DAG signature well-formed? | No — `a` is free. Both closures are settled here. |
| 2 | Is `T011` independent of `T010`/`T012`? | No. One lemma, two corollaries. |
| 3 | Does the trio need decidability as a premise? | No — it *implies* a decision procedure. |
| 4 | Is `T016` vacuous? | Yes, under the only `SynthAER` the D-list can supply. |
| 5 | Does the estate anchor point the right way? | No — `checkRefs_complete` is REJECTION completeness. |
| 6 | What does first-error cost per clause? | Each clause must be decided on its prefix sublanguage. |
| 7 | How does a conjunct fail to be a clause? | By being universally true, or by respecting the semantics. |

No `sorry`, no `axiom`, no `native_decide`, no `#eval`. `#print axioms`
receipts at the foot.
-/

namespace ScoutT011

/-- `∃!` is Mathlib notation and `library/cas` carries no Mathlib, so the
packet's `exists!` rows are spelled here by hand. Worth recording: three DAG
rows (`T004`, `T008`, `T016`) are stated with a connective this toolchain
cannot parse. -/
def ExistsUnique' {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ## §1 — the DAG signature has a free variable

`exists p, check r = ok <a,p>` binds `p` and leaves `a` free. There are exactly
two closures, and they are the two extremes: one is content-free, the other is
false. -/

section Shape

variable {Alph D : Type} {Chk : Alph → Type}

/-- **The `∃a` closure carries no alphabet content.** Binding `a` alongside `p`
turns `EC1-T011`'s conclusion into bare acceptance — "the checker said ok" —
with nothing said about which `AER` came back. Every claim about the synthesized
alphabet is therefore owed entirely by `EC1-T016`/`EC1-T017`, not by this row. -/
theorem exists_alph_closure_is_bare_acceptance
    (e : Except D ((a : Alph) × Chk a)) :
    (∃ (a : Alph) (p : Chk a), e = .ok ⟨a, p⟩) ↔ (∃ x, e = .ok x) := by
  constructor
  · rintro ⟨a, p, h⟩; exact ⟨⟨a, p⟩, h⟩
  · rintro ⟨⟨a, p⟩, h⟩; exact ⟨a, p, h⟩

/-- **The `∀a` closure is false.** A `check` answer names ONE alphabet, so a
row quantifying `a` universally outside the existential is refuted by any two
distinct alphabets. This is the reading a reader of the DAG table takes if the
free `a` is understood as implicitly universally bound at the front, which is
the Lean convention for a free variable in a theorem statement. -/
theorem forall_alph_closure_is_false
    (a₀ a₁ : Alph) (hne : a₀ ≠ a₁) (x : Chk a₀) :
    ¬ ∀ a : Alph, ∃ p : Chk a,
        (Except.ok ⟨a₀, x⟩ : Except D ((a : Alph) × Chk a)) = .ok ⟨a, p⟩ := by
  intro h
  obtain ⟨p, hp⟩ := h a₁
  injection hp with hs
  exact hne (congrArg Sigma.fst hs)

/-- The `∀a` reading is not refuted only in degenerate models: a two-element
alphabet index with an inhabited fibre suffices, and `Bool` supplies one. -/
theorem forall_alph_closure_is_false_concretely :
    ¬ ∀ a : Bool, ∃ _p : Unit,
        (Except.ok ⟨false, ()⟩ : Except Unit ((_ : Bool) × Unit)) = .ok ⟨a, ()⟩ :=
  forall_alph_closure_is_false (Chk := fun _ => Unit) (D := Unit) false true (by decide) ()

end Shape

/-! ## §2 — one lemma, two corollaries

`EC1-D024` fixes `check`'s shape. Over that shape, `EC1-T010`, `EC1-T011` and
`EC1-T012` are not three independent obligations. -/

/-- The declared shape of `EC1-D021` + `EC1-D024`. -/
structure Checker (Raw Alph D : Type) (Chk : Alph → Type) where
  /-- `EC1-D021 ProgramWF`. -/
  WF : Raw → Prop
  /-- `EC1-D024 check`. -/
  run : Raw → Except D ((a : Alph) × Chk a)

namespace Checker

variable {Raw Alph D : Type} {Chk : Alph → Type} (S : Checker Raw Alph D Chk)

/-- `EC1-T010 check_sound`. -/
def Sound : Prop := ∀ r a (p : Chk a), S.run r = .ok ⟨a, p⟩ → S.WF r

/-- `EC1-T011 check_complete`, alphabet existentially closed (§1). -/
def AcceptComplete : Prop := ∀ r, S.WF r → ∃ (a : Alph) (p : Chk a), S.run r = .ok ⟨a, p⟩

/-- `EC1-T012 check_error_iff`. -/
def ErrorIff : Prop := ∀ r, (∃ d, S.run r = .error d) ↔ ¬ S.WF r

/-- The single content-bearing statement: acceptance agrees with the judgment.
This is `EC1-K10`'s first three equations collapsed. -/
def Agrees : Prop := ∀ r, (∃ x, S.run r = .ok x) ↔ S.WF r

/-- Acceptance and rejection exhaust the checker's answers. -/
theorem ok_or_error (r : Raw) :
    (∃ x, S.run r = .ok x) ∨ (∃ d, S.run r = .error d) := by
  cases h : S.run r with
  | ok x => exact Or.inl ⟨x, rfl⟩
  | error d => exact Or.inr ⟨d, rfl⟩

theorem not_ok_and_error {r : Raw}
    (ho : ∃ x, S.run r = .ok x) (he : ∃ d, S.run r = .error d) : False := by
  obtain ⟨x, hx⟩ := ho
  obtain ⟨d, hd⟩ := he
  rw [hx] at hd
  cases hd

/-- **`Agrees` is exactly `T010 ∧ T011`.** -/
theorem agrees_iff_sound_and_acceptComplete : S.Agrees ↔ (S.Sound ∧ S.AcceptComplete) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r a p hp; exact (h r).mp ⟨⟨a, p⟩, hp⟩
    · intro r hwf
      obtain ⟨⟨a, p⟩, hx⟩ := (h r).mpr hwf
      exact ⟨a, p, hx⟩
  · rintro ⟨hs, hc⟩ r
    constructor
    · rintro ⟨⟨a, p⟩, hx⟩; exact hs r a p hx
    · intro hwf
      obtain ⟨a, p, hx⟩ := hc r hwf
      exact ⟨⟨a, p⟩, hx⟩

/-- **`EC1-T012` is a corollary of `EC1-T010` + `EC1-T011`** — no new content. -/
theorem errorIff_of_sound_acceptComplete (hs : S.Sound) (hc : S.AcceptComplete) : S.ErrorIff := by
  have hag : S.Agrees := (S.agrees_iff_sound_and_acceptComplete).mpr ⟨hs, hc⟩
  intro r
  constructor
  · intro he hwf; exact S.not_ok_and_error ((hag r).mpr hwf) he
  · intro hwf
    rcases S.ok_or_error r with ho | he
    · exact absurd ((hag r).mp ho) hwf
    · exact he

/-- **`EC1-T011` is a corollary of `EC1-T010` + `EC1-T012`** — also no new
content. Together with the previous theorem this pins the admission bundle:
the three rows contain ONE theorem and two derivations. Which two are declared
corollaries is a presentation choice; that only one is independent is not. -/
theorem acceptComplete_of_sound_errorIff (_hs : S.Sound) (he : S.ErrorIff) : S.AcceptComplete := by
  intro r hwf
  rcases S.ok_or_error r with ho | herr
  · obtain ⟨⟨a, p⟩, hx⟩ := ho; exact ⟨a, p, hx⟩
  · exact absurd hwf ((he r).mp herr)

/-! ## §3 — the trio does not *need* decidability; it *asserts* it

The DAG lists "decidability of every WF clause" as a dependency of `EC1-T011`
and `EC1-T012`. That is the wrong direction. `check` is a Lean function, so its
answer is already a decision; the rows therefore hand back a decision procedure
for `ProgramWF`. This is why the DAG's prohibition bites: a semantic clause does
not make `T011`/`T012` merely unprovable, it makes them FALSE. -/

/-- The checker's answer, as a Boolean. Computable because `run` is a function. -/
def accepts (r : Raw) : Bool :=
  match S.run r with
  | .ok _ => true
  | .error _ => false

theorem accepts_iff (r : Raw) : S.accepts r = true ↔ ∃ x, S.run r = .ok x := by
  unfold accepts
  cases h : S.run r with
  | ok x =>
    constructor
    · intro _; exact ⟨x, rfl⟩
    · intro _; rfl
  | error d =>
    constructor
    · intro hcon; exact Bool.noConfusion hcon
    · rintro ⟨x, hx⟩; cases hx

/-- **`Agrees` yields a decision procedure for `ProgramWF`**, namely `accepts`.
Nothing classical is used: the instance is built from the checker itself. -/
def decidableWF_of_agrees (h : S.Agrees) (r : Raw) : Decidable (S.WF r) :=
  decidable_of_iff (S.accepts r = true) (Iff.trans (S.accepts_iff r) (h r))

/-- The same, spelled as the Boolean characteristic function the estate's gates
consume. Read the contrapositive: if `ProgramWF` admits no such function, then
`EC1-T010` and `EC1-T011` cannot both hold of any `check` of shape `EC1-D024`. -/
theorem characteristic_function_of_sound_acceptComplete
    (hs : S.Sound) (hc : S.AcceptComplete) :
    ∀ r, S.accepts r = true ↔ S.WF r := by
  have hag : S.Agrees := (S.agrees_iff_sound_and_acceptComplete).mpr ⟨hs, hc⟩
  intro r
  exact Iff.trans (S.accepts_iff r) (hag r)

/-! ## §4 — `SynthAER` read off the checker makes `EC1-T016` vacuous -/

/-- `SynthAER` is used by `EC1-T016`/`EC1-T017` but is NOT in the packet's
declaration list (`PROOF-DAG.md` §2 has no `PROPOSED TERM` for it). The only
`AER` producer the D-list does declare is `check` itself (`EC1-D024`), so this
is the definition the packet forces if nothing further is minted. -/
def SynthAER (r : Raw) (a : Alph) : Prop := ∃ p : Chk a, S.run r = .ok ⟨a, p⟩

/-- **`EC1-T016 aer_synthesis_unique` is a tautology under that reading.** The
uniqueness half consumes no hypothesis about `S` beyond `run` being a function;
the existence half is exactly `EC1-T011`. To be a theorem, `SynthAER` must be an
independently declared synthesis JUDGMENT — an inductive relation over the raw
graph — and `T016` must state that the judgment is deterministic. That is the
shape the anchor lane's model pair (`Cas/Schema/Declarations.lean:288`
`General.row_surjective` with `:297` `General.row_inj`) exhibits. -/
theorem synthAER_unique_is_free (hc : S.AcceptComplete) (r : Raw) (hwf : S.WF r) :
    ScoutT011.ExistsUnique' (S.SynthAER r) := by
  obtain ⟨a, p, hp⟩ := hc r hwf
  refine ⟨a, ⟨p, hp⟩, ?_⟩
  rintro b ⟨q, hq⟩
  rw [hp] at hq
  injection hq with hs
  exact (congrArg Sigma.fst hs).symm

/-- Sharper: the uniqueness half alone needs NO packet hypothesis at all. -/
theorem synthAER_uniqueness_needs_nothing {r : Raw} {a b : Alph}
    (ha : S.SynthAER r a) (hb : S.SynthAER r b) : a = b := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  rw [hp] at hq
  injection hq with hs
  exact congrArg Sigma.fst hs

end Checker

/-! ## §5 — what first-error costs, per clause

`R16` rules the checker first-error over a frozen clause order (`ALGEBRA.md`
§4.3's twelve clauses). This section states the price that architecture puts on
each individual clause. -/

/-- A first-error checker over `n` frozen clauses: `none` accepts, `some i`
names the FIRST failing clause. This is `EC1-CE031`'s shape — the returned
clause is one clause, not a set. -/
structure FirstError (Raw : Type) where
  /-- how many clauses are in the frozen order. -/
  n : Nat
  /-- clause `i` of `ProgramWF`, in the frozen order. -/
  clause : Nat → Raw → Prop
  /-- the checker. -/
  chk : Raw → Option Nat
  /-- it accepts exactly the conjunction. -/
  accepts : ∀ r, chk r = none ↔ ∀ i, i < n → clause i r
  /-- first-error soundness, in the sense `R16` ruled: the reported clause is a
  real violation, and every EARLIER clause held. -/
  first : ∀ r i, chk r = some i → i < n ∧ ¬ clause i r ∧ ∀ j, j < i → clause j r

namespace FirstError

variable {Raw : Type} (F : FirstError Raw)

/-- **The per-clause price.** A first-error checker DECIDES clause `i` on the
sublanguage cut out by clauses `0 .. i-1`, and the decision is computed from
`F.chk` alone — no classical choice, no oracle. Read the contrapositive, which
is the finding this probe exists to sharpen: if clause `i` admits no procedure
on that sublanguage, then NO `F.chk` of this shape exists, and with it neither
`EC1-T011` nor `EC1-T012` nor `EC1-T015`. It is not enough for the twelve-way
conjunction to be decidable by some other route; the frozen order forces each
clause to be decided where it is reached. -/
def clauseDecidableOnPrefix (i : Nat) (hi : i < F.n) (r : Raw)
    (hpre : ∀ j, j < i → F.clause j r) : Decidable (F.clause i r) :=
  match h : F.chk r with
  | none => isTrue ((F.accepts r).mp h i hi)
  | some j =>
    if hji : j < i then absurd (hpre j hji) (F.first r j h).2.1
    else if hij : i < j then isTrue ((F.first r j h).2.2 i hij)
    else
      have hje : j = i := Nat.le_antisymm (Nat.not_lt.mp hij) (Nat.not_lt.mp hji)
      isFalse (hje ▸ (F.first r j h).2.1)

/-- Clause `0` is decided outright: it has no prefix to satisfy first. -/
def clauseZeroDecidable (h0 : 0 < F.n) (r : Raw) : Decidable (F.clause 0 r) :=
  F.clauseDecidableOnPrefix 0 h0 r (fun _ hj => absurd hj (Nat.not_lt_zero _))

/-- And the conjunction itself is decided, everywhere. -/
def wfDecidable (r : Raw) : Decidable (∀ i, i < F.n → F.clause i r) :=
  match h : F.chk r with
  | none => isTrue ((F.accepts r).mp h)
  | some j => isFalse (fun hall => (F.first r j h).2.1 (hall j (F.first r j h).1))

end FirstError

/-! ## §6 — the estate anchor, restated at its own carrier

`Cas/Core/Admission.lean` is the only shipped checker of this family. Its
acceptance-completeness is the `mpr` half of `checkRefs_ok_iff`, NOT
`checkRefs_complete` — the latter is REJECTION completeness (condemned implies
rejected), which anchors `EC1-T012`'s forward direction. The two lemmas below
separate them at the estate's own carrier so the mis-assignment is visible. -/

namespace EstateAnchor

open Cas

/-- The `EC1-T011` direction at the estate carrier: well-formed implies
accepted. It is `checkRefs_ok_iff.mpr`. -/
theorem checkRefs_acceptComplete {σ : Store} {rs : List Ref} (h : RefsOk σ rs) :
    checkRefs σ rs = .ok () :=
  checkRefs_ok_iff.mpr h

/-- The `EC1-T010` direction: accepted implies well-formed. -/
theorem checkRefs_sound {σ : Store} {rs : List Ref} (h : checkRefs σ rs = .ok ()) :
    RefsOk σ rs :=
  checkRefs_ok_iff.mp h

/-- What `checkRefs_complete` actually says — the OTHER completeness. It takes a
condemning clause and returns a rejection, and is silent about acceptance. -/
theorem checkRefs_rejectComplete {σ : Store} {rs : List Ref}
    (h : ∃ e, AdmissionError.Condemns σ e rs) : ∃ e', checkRefs σ rs = .error e' :=
  checkRefs_complete h

/-- The estate carrier instantiates §2's shape with a one-clause `ProgramWF`
and a trivial alphabet, and `Agrees` holds. This is the sanity check that the
abstract section is about the right object. -/
def refsChecker (σ : Store) :
    ScoutT011.Checker (List Ref) Unit AdmissionError (fun _ => Unit) where
  WF := RefsOk σ
  run := fun rs =>
    match checkRefs σ rs with
    | .ok _ => .ok ⟨(), ()⟩
    | .error e => .error e

theorem refsChecker_run_ok {σ : Store} {rs : List Ref} (h : checkRefs σ rs = .ok ()) :
    (refsChecker σ).run rs = .ok ⟨(), ()⟩ := by
  show (match checkRefs σ rs with
        | .ok _ => Except.ok (⟨(), ()⟩ : (_ : Unit) × Unit)
        | .error e => Except.error e) = _
  rw [h]

theorem refsChecker_run_error {σ : Store} {rs : List Ref} {e : AdmissionError}
    (h : checkRefs σ rs = .error e) : (refsChecker σ).run rs = .error e := by
  show (match checkRefs σ rs with
        | .ok _ => Except.ok (⟨(), ()⟩ : (_ : Unit) × Unit)
        | .error e => Except.error e) = _
  rw [h]

theorem refsChecker_agrees (σ : Store) : (refsChecker σ).Agrees := by
  intro rs
  constructor
  · rintro ⟨x, hx⟩
    show RefsOk σ rs
    rw [← checkRefs_ok_iff]
    cases h : checkRefs σ rs with
    | ok u => cases u; rfl
    | error e =>
      exfalso
      rw [refsChecker_run_error h] at hx
      cases hx
  · intro hwf
    exact ⟨⟨(), ()⟩, refsChecker_run_ok (checkRefs_ok_iff.mpr hwf)⟩

/-- Hence `T010`, `T011` and `T012` all hold at the estate carrier — and by §2
they were one fact wearing three hats. -/
theorem refsChecker_errorIff (σ : Store) : (refsChecker σ).ErrorIff := by
  have hag := refsChecker_agrees σ
  exact (refsChecker σ).errorIff_of_sound_acceptComplete
    (((refsChecker σ).agrees_iff_sound_and_acceptComplete).mp hag).1
    (((refsChecker σ).agrees_iff_sound_and_acceptComplete).mp hag).2

end EstateAnchor

/-! ## §7 — the two ways a `ProgramWF` conjunct fails to be a clause

`ALGEBRA.md` §4.3's clause 12, `PresentationWF: normalization does not change
reference meaning`, is the one clause of the twelve whose stated content is a
property of the NORMALIZER rather than of the program. Read as denotational
("`normalizeRaw r` means what `r` means") it is `EC1-T027 alpha_semantics`, a
universally quantified theorem — and §7.1 shows a universally true conjunct
contributes nothing to the judgment. Read as a per-program check ("the
reference-resolution map is transported along the renaming") it is decidable by
recompute-and-compare and is a real clause. §7.2 states the price of the other
reading. -/

namespace ClauseHygiene

variable {Raw : Type}

/-- **§7.1 — a conjunct that is a theorem is a no-op.** If clause `k` holds of
every raw program, the judgment with it and the judgment without it are the same
predicate, so no checker can distinguish them and no diagnostic can name it.
`PresentationWF` under the denotational reading is exactly this. -/
theorem universal_conjunct_is_a_no_op
    (C : Nat → Raw → Prop) (n k : Nat) (huniv : ∀ r, C k r) (r : Raw) :
    (∀ i, i < n → C i r) ↔ (∀ i, i < n → i ≠ k → C i r) := by
  constructor
  · intro h i hi _; exact h i hi
  · intro h i hi
    by_cases hik : i = k
    · exact hik ▸ huniv r
    · exact h i hi hik

/-- **§7.2 — conjuncts closed under an equivalence make acceptance closed under
it.** If every clause respects a relation `R` on raw programs, so does the whole
judgment, and by §2 so does any checker satisfying `Agrees`. Take `R` to be
denotational equality and this is the obstruction the packet must avoid: the
estate's own admission-family recognizers are presentation-sensitive
(`EC1-CE040`: `unreachableTail` and `entryNotZero` are denotationally equal to
the injected table and are still refused), which is `R4` — identity hashes
presentations, not denotations. A semantic clause is therefore not merely
undecidable; it contradicts the boundary the estate already proved. -/
theorem semantic_conjuncts_make_wf_semantic
    (C : Nat → Raw → Prop) (n : Nat) (Rel : Raw → Raw → Prop)
    (hresp : ∀ i, i < n → ∀ r s, Rel r s → C i r → C i s)
    {r s : Raw} (hrs : Rel r s) (hr : ∀ i, i < n → C i r) :
    ∀ i, i < n → C i s :=
  fun i hi => hresp i hi r s hrs (hr i hi)

end ClauseHygiene

end ScoutT011

/-! ## Kernel receipts -/

#print axioms ScoutT011.exists_alph_closure_is_bare_acceptance
#print axioms ScoutT011.forall_alph_closure_is_false
#print axioms ScoutT011.forall_alph_closure_is_false_concretely
#print axioms ScoutT011.Checker.agrees_iff_sound_and_acceptComplete
#print axioms ScoutT011.Checker.errorIff_of_sound_acceptComplete
#print axioms ScoutT011.Checker.acceptComplete_of_sound_errorIff
#print axioms ScoutT011.Checker.accepts_iff
#print axioms ScoutT011.Checker.decidableWF_of_agrees
#print axioms ScoutT011.Checker.characteristic_function_of_sound_acceptComplete
#print axioms ScoutT011.Checker.synthAER_unique_is_free
#print axioms ScoutT011.Checker.synthAER_uniqueness_needs_nothing
#print axioms ScoutT011.FirstError.clauseDecidableOnPrefix
#print axioms ScoutT011.FirstError.clauseZeroDecidable
#print axioms ScoutT011.FirstError.wfDecidable
#print axioms ScoutT011.EstateAnchor.checkRefs_acceptComplete
#print axioms ScoutT011.EstateAnchor.checkRefs_sound
#print axioms ScoutT011.EstateAnchor.checkRefs_rejectComplete
#print axioms ScoutT011.EstateAnchor.refsChecker_agrees
#print axioms ScoutT011.EstateAnchor.refsChecker_errorIff
#print axioms ScoutT011.ClauseHygiene.universal_conjunct_is_a_no_op
#print axioms ScoutT011.ClauseHygiene.semantic_conjuncts_make_wf_semantic
