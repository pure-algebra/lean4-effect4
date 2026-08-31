import Cas.Core.Admission

/-!
# Effect Core v1 — scout probe for `EC1-T013` (`check_erase`), slice `EC1-S2`

Scout artifact only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Check.lean`.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T013.lean
```

The DAG row under scout is

```text
EC1-T013  check_erase : check (erase p) = ok <a, normalizeChecked p>   deps T006, T010
```

Six questions are settled below by making the answer typecheck.

| § | Question | Finding |
|---|---|---|
| 1 | Is `T013` vacuous? | YES, if `normalizeChecked` is read off the checker. |
| 2 | What is `T013`'s real content? | It forces an unlisted companion and idempotence. |
| 3 | What does `erase` non-injectivity cost? | `CheckedProgram` may carry no data absent from its raw. |
| 4 | Does the Sigma index bite? | Yes; `T013` as written already entails `T017`. |
| 5 | Is `T016` vacuous? | YES, for any function-shaped `SynthAER`. |
| 6 | Is any `ProgramWF` clause actually decided? | Clause 1 is, in the kernel, today. |

`EC1-T006` (`normalizeRaw_idempotent`) belongs to slice `EC1-S1`, running
concurrently. It is used below ONLY as a named hypothesis (`erase_normal`),
never proved here.
-/

namespace EffectCoreScoutT013

/-! ## §1 — `EC1-T013` is a tautology under the lazy normalizer

`normalizeChecked` is named in `PROOF-DAG.md:215` and `CONTRACT-PACKET.md:310`
and declared NOWHERE: it is absent from the `EC1-D020`–`D026` term list, which
declares `normalizeRaw` only. Nothing therefore forbids defining it as "whatever
the checker returns on the erasure", and under that definition the row proves
nothing beyond the admission fact `T014` — which the DAG routes THROUGH `T013`. -/

section Vacuity

variable {Raw Chk Diag : Type}

/-- The lazy definition: read the checked normalizer off the checker. -/
def normalizeCheckedLazy (check : Raw → Except Diag Chk) (erase : Chk → Raw)
    (p : Chk) : Chk :=
  match check (erase p) with
  | .ok q => q
  | .error _ => p

/-- VACUITY: for EVERY `check` and EVERY `erase`, once admission of erasures is
assumed, `EC1-T013` holds by computation. All of the row's content sits in the
hypothesis `hadm`, i.e. in `EC1-T014` + `EC1-T011`. -/
theorem T013_is_vacuous_under_the_lazy_normalizer
    (check : Raw → Except Diag Chk) (erase : Chk → Raw)
    (hadm : ∀ p : Chk, ∃ q, check (erase p) = .ok q) :
    ∀ p : Chk, check (erase p) = .ok (normalizeCheckedLazy check erase p) := by
  intro p
  obtain ⟨q, hq⟩ := hadm p
  have hn : normalizeCheckedLazy check erase p = q := by
    show (match check (erase p) with | .ok q => q | .error _ => p) = q
    rw [hq]
  rw [hn, hq]

end Vacuity

/-! ## §2 — the content `EC1-T013` actually carries

With `normalizeChecked` declared independently, `T013` forces a companion the
DAG does not list — call it `erase_check`, "a successful check erases back to
the normalized raw it was given" — and together with the normalized-erasure
invariant (`CONTRACT-PACKET.md:309`) and `EC1-T006` it makes `normalizeChecked`
idempotent for free. That idempotence is the checked-level twin of `T006` and is
an unlisted obligation of the row. -/

section Content

variable {Raw Chk Diag : Type}

/-- `EC1-T013` + `erase_check` + `erase_normal` (which is where `EC1-T006`
enters) ⟹ `normalizeChecked` is idempotent. Not listed anywhere in the DAG. -/
theorem normalizeChecked_idempotent
    (check : Raw → Except Diag Chk) (erase : Chk → Raw)
    (normalizeRaw : Raw → Raw) (normalizeChecked : Chk → Chk)
    (T013 : ∀ p, check (erase p) = .ok (normalizeChecked p))
    (erase_check : ∀ r q, check r = .ok q → erase q = normalizeRaw r)
    (erase_normal : ∀ p : Chk, normalizeRaw (erase p) = erase p) :
    ∀ p, normalizeChecked (normalizeChecked p) = normalizeChecked p := by
  intro p
  have h1 : erase (normalizeChecked p) = erase p := by
    rw [erase_check _ _ (T013 p), erase_normal]
  have h2 := T013 (normalizeChecked p)
  rw [h1] at h2
  have h3 := (T013 p).symm.trans h2
  simpa using h3.symm

end Content

/-! ## §3 — the `hsep` analogue: `erase` non-injectivity is a carrier constraint

`Cas/Lang/Defun.lean:998` `decodeProg_encodeProg` — the estate's only erase /
recover round trip — needs `hsep`, the premise that distinct lines get distinct
addresses, and `Cas/Lang/Defun.lean:1023` EXHIBITS a degenerate address function
where recovery loses a line. The `T013` analogue is sharper: the round trip is
stated with a normalizer instead of a premise, so instead of failing, it silently
CONSTRAINS the carrier. -/

section Fibers

variable {Raw Chk Diag : Type}

/-- `EC1-T013` forces `normalizeChecked` to factor through `erase`: two checked
programs with the same erasure have the same normal form. Consequence for the
carrier: `CheckedProgram` may carry NO data that `erase` discards and `check`
cannot recompute — in particular no client-declared `A/E/R` triple that differs
from the synthesized one. `AERWF` (`ALGEBRA.md` 4.3 clause 11) is exactly the
clause that rescues the row. -/
theorem normalizeChecked_factors_through_erase
    (check : Raw → Except Diag Chk) (erase : Chk → Raw) (normalizeChecked : Chk → Chk)
    (T013 : ∀ p, check (erase p) = .ok (normalizeChecked p))
    (p q : Chk) (h : erase p = erase q) :
    normalizeChecked p = normalizeChecked q := by
  have hp := T013 p
  rw [h] at hp
  simpa using hp.symm.trans (T013 q)

end Fibers

/-! ## §4 — the Sigma index, and why `EC1-T013` already entails `EC1-T017`

`check` returns `Except Diagnostic (Σ aer, CheckedProgram aer)` (`EC1-D024`).
For the DAG's right-hand side `ok ⟨a, normalizeChecked p⟩` to typecheck at all,
`a` must be `p`'s own index. So the row asserts index exactness on the nose —
which is `EC1-T017 checked_aer_exact`. The DAG routes `T017` through `T016`
instead and does not record the entailment. -/

section SigmaIndex

variable {AER Raw Diag : Type} {Chk : AER → Type}

/-- The transport the schematic signature hides: a Sigma equality is never just
two component equalities. Any proof of `T013` needs this step. -/
theorem sigma_ok_ext {a a' : AER} {q : Chk a'} {r : Chk a}
    (h : a' = a) (hq : HEq q r) :
    (Sigma.mk a' q : Σ x, Chk x) = ⟨a, r⟩ := by
  subst h
  rw [eq_of_heq hq]

/-- `EC1-T013` as written entails index exactness — `EC1-T017`'s content. -/
theorem T013_entails_index_exactness
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ {a}, Chk a → Raw)
    (normalizeChecked : ∀ {a}, Chk a → Chk a)
    (T013 : ∀ {a} (p : Chk a), check (erase p) = .ok ⟨a, normalizeChecked p⟩)
    {a : AER} (p : Chk a) {a' : AER} {q : Chk a'}
    (h : check (erase p) = .ok ⟨a', q⟩) : a' = a := by
  rw [T013 p] at h
  have h2 : (⟨a, normalizeChecked p⟩ : Σ x, Chk x) = ⟨a', q⟩ := by simpa using h
  exact (congrArg Sigma.fst h2).symm

end SigmaIndex

/-! ## §5 — `EC1-T016` is vacuous if `SynthAER` is a function

Recorded because the scout brief asks and because it bears on `T013`: `T013`'s
index exactness (§4) is only meaningful if the synthesized index is pinned by
something other than a Lean function's own determinism. -/

theorem exists_unique_over_a_function_is_free
    {α β : Type} (f : α → β) (x : α) :
    ∃ y, f x = y ∧ ∀ z, f x = z → z = y :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- The `ProgramWF` premise of `EC1-T016` is not used. -/
theorem T016_needs_no_wf_premise
    {Raw AER : Type} (synthAER : Raw → AER) (WF : Raw → Prop) :
    ∀ r, WF r → ∃ a, synthAER r = a ∧ ∀ b, synthAER r = b → b = a :=
  fun r _ => exists_unique_over_a_function_is_free synthAER r

/-! ## §6 — one `ProgramWF` clause is genuinely DECIDED, in the kernel, today

`ALGEBRA.md` 4.3 clause 1 `IdsWF`'s reference half is the estate's `RefsOk`, and
`Cas/Core/Admission.lean:60` `checkRefs_ok_iff` turns the shipped fail-fast
checker into a decision procedure with no classical input. This is the SHAPE the
other eleven clauses must reach: a `Bool`/`Except`-valued scan plus an `iff`.

Clause 12 `PresentationWF` ("normalization does not change reference meaning")
cannot reach this shape under a semantic reading of "meaning":
`library/cas/EFFECTS-BACKEND.md` R4 records that semantic equivalence is
undecidable immediately above finite state. R4 is estate law, so the clause must
be restated as an equality of reference-resolution maps. -/

open Cas in
/-- The estate's admission clause is a real decision procedure. -/
def decRefsOk (σ : Cas.Store) (rs : List Cas.Ref) : Decidable (Cas.RefsOk σ rs) :=
  match h : Cas.checkRefs σ rs with
  | .ok () => isTrue (Cas.checkRefs_ok_iff.mp h)
  | .error e =>
      isFalse (fun hr => by
        have hok := Cas.checkRefs_ok_iff.mpr hr
        rw [h] at hok
        simp at hok)

/-- Being decided, the clause is also a two-sided classifier: no `Classical.em`
is imported to case-split on it. -/
theorem refsOk_decidable_split (σ : Cas.Store) (rs : List Cas.Ref) :
    Cas.RefsOk σ rs ∨ ¬ Cas.RefsOk σ rs :=
  match decRefsOk σ rs with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

end EffectCoreScoutT013

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT013.T013_is_vacuous_under_the_lazy_normalizer
#print axioms EffectCoreScoutT013.normalizeChecked_idempotent
#print axioms EffectCoreScoutT013.normalizeChecked_factors_through_erase
#print axioms EffectCoreScoutT013.sigma_ok_ext
#print axioms EffectCoreScoutT013.T013_entails_index_exactness
#print axioms EffectCoreScoutT013.exists_unique_over_a_function_is_free
#print axioms EffectCoreScoutT013.T016_needs_no_wf_premise
#print axioms EffectCoreScoutT013.refsOk_decidable_split
