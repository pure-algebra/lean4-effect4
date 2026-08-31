import Cas.Core.Admission
import Cas.Backend.Canon
import Cas.Lang.Defun

/-!
# Effect Core v1 — packet-local local-anchor counterexamples

This file re-elaborates the four contradiction proofs reported in
`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` from their
original ephemeral scratch sources:

* `check1.lean`: `EC1-T015`, fail-fast diagnostics are not diagnostic-complete;
* `check2.lean`: `EC1-T088`, semantic equality does not determine classification;
* `check3.lean`: `EC1-T100`, arbitrary `PProg` cannot be totally admitted;
* `check4.lean` (namespace `Check5`): `EC1-T002`, row normalization needs a
  duplicate-free premise.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/LocalAnchors.lean
```

The statements below preserve the reported witnesses and conclusions. They do
not claim that every possible future checker, classifier, admission boundary,
or row normalizer has the same limitation.
-/

namespace EffectCoreLocalAnchors

namespace DiagnosticLocal

open Cas

def a1 : Addr32 := ⟨List.replicate 32 1, by simp⟩
def a2 : Addr32 := ⟨List.replicate 32 2, by simp⟩

def sigma : Store := Store.empty.set a2 ⟨0, 7, [], []⟩

def refs : List Ref := [⟨1, a1⟩, ⟨3, a2⟩]

/-- Both clauses condemn the same reference list. -/
theorem both_condemn :
    AdmissionError.Condemns sigma (.dangling a1) refs
      ∧ AdmissionError.Condemns sigma (.wrongKind a2 3 7) refs := by
  refine ⟨⟨⟨1, a1⟩, by simp [refs], rfl, ?_⟩,
          ⟨⟨3, a2⟩, by simp [refs], rfl, rfl, ⟨0, 7, [], []⟩, ?_, rfl,
            by decide⟩⟩
  · show sigma a1 = none
    simp [sigma, Store.set, Store.empty, a1, a2]
  · show sigma a2 = some ⟨0, 7, [], []⟩
    simp [sigma, Store.set]

/-- The shipped checker reports only the first failing clause. -/
theorem checker_reports_only_the_first :
    checkRefs sigma refs = .error (.dangling a1) := by
  show (match sigma a1 with
        | none => Except.error (AdmissionError.dangling a1)
        | some m => if m.tag = (1 : UInt8) then checkRefs sigma [⟨3, a2⟩]
                    else .error (.wrongKind a1 1 m.tag)) = _
  simp [sigma, Store.set, Store.empty, a1, a2]

/-- Counterexample to `EC1-T015` when it is claimed of the shipped fail-fast
checker: a condemning clause exists but is not the returned diagnostic. -/
theorem diagnostic_local_is_false :
    ∃ (σ : Store) (rs : List Ref) (e : AdmissionError),
      AdmissionError.Condemns σ e rs
        ∧ ∀ e', checkRefs σ rs = .error e' → e' ≠ e := by
  refine ⟨sigma, refs, .wrongKind a2 3 7, both_condemn.2, ?_⟩
  intro e' h
  rw [checker_reports_only_the_first] at h
  rw [← Except.error.inj h]
  intro hc
  exact absurd hc (by decide)

end DiagnosticLocal

namespace ClassifierSemEq

open Cas Cas.Lang

def a0 : Addr32 := ⟨List.replicate 32 0, by simp⟩

def p1 : PProg := [.load (.lit a0)]
def p2 : PProg := [.load (.lit a0), .load (.ans 0)]

section

variable (H : Bytes → Addr32)

/-- The two tables have identical direct runs at every starting word. -/
theorem runs_agree (w : Word) : runP H p1 w = runP H p2 w := by
  show runPFrom H [] p1 w = runPFrom H [] p2 w
  cases hf : Word.find w a0 <;>
    simp [p1, p2, runPFrom, PIn.resolve, hf]

theorem obs_equal : ObsEq H (embed p1) (embed p2) :=
  ObsEq_embed_of_runP H (runs_agree H)

end

/-- The existing envelope classifier distinguishes their dataflow. -/
theorem envelopes_differ : PProg.envelope p1 ≠ PProg.envelope p2 := by
  intro h
  have hd : (PProg.envelope p1).dataflow = (PProg.envelope p2).dataflow :=
    congrArg Envelope.dataflow h
  have h1 : (PProg.envelope p1).dataflow = [] := rfl
  have h2 : (PProg.envelope p2).dataflow = [(1, 0)] := rfl
  rw [h1, h2] at hd
  exact absurd hd (by decide)

/-- Counterexample to `EC1-T088`: observational equality at the CAS carrier
does not force equality of a finer structural classification. -/
theorem classifier_semEq_is_false :
    ∃ (p q : PProg),
      (∀ (H : Bytes → Addr32), ObsEq H (embed p) (embed q))
        ∧ PProg.envelope p ≠ PProg.envelope q :=
  ⟨p1, p2, fun H => obs_equal H, envelopes_differ⟩

end ClassifierSemEq

namespace InjectCas

open Cas Cas.Lang

section

variable (H : Bytes → Addr32) (w : Word)

theorem empty_table_refuses :
    runP H [] w = (.refused (.failed "defun: empty program"), w) := rfl

theorem dangling_index_refuses :
    runP H [.load (.ans 0)] w
      = (.refused (.failed "defun: dangling answer index"), w) := rfl

end

theorem dangling_not_closed :
    (PProg.envelope [PLine.load (.ans 0)]).dataflowClosed = false := rfl

/-- Runtime witnesses against the intended meaning-preserving total-domain
formulation of `EC1-T100`: `PProg` contains distinct refusal classes, including
a statically non-closed table. This proposition alone does not refute an
arbitrary type-correct function that ignores its input; the packet row must
state preservation and restrict its domain to admitted tables. -/
theorem injectCas_cannot_be_total :
    ∃ p q : PProg,
      p ≠ q
        ∧ (∀ (H : Bytes → Addr32) (w : Word),
            (runP H p w).1 = .refused (.failed "defun: empty program"))
        ∧ (∀ (H : Bytes → Addr32) (w : Word),
            (runP H q w).1 = .refused (.failed "defun: dangling answer index"))
        ∧ (PProg.envelope q).dataflowClosed = false :=
  ⟨[], [PLine.load (.ans 0)], by simp,
    fun H w => congrArg Prod.fst (empty_table_refuses H w),
    fun H w => congrArg Prod.fst (dangling_index_refuses H w),
    dangling_not_closed⟩

end InjectCas

namespace NormalizeRow

open Cas.Backend Cas.Schema

/-- Counterexample to the premise-free forward direction of `EC1-T002`,
reusing the estate's maintained witness for its shipped keyed-row normalizer. -/
theorem normalizeRow_forward_is_false :
    ¬ ∀ (r s : List ServiceRef), r.Perm s → canonServices r = canonServices s :=
  canonServices_perm_premise_is_necessary

/-- The corresponding positive boundary: duplicate-free keys recover the
existing permutation theorem. -/
theorem normalizeRow_with_nodup (xs : List ServiceRef)
    (hnd : (xs.map (·.key)).Nodup) : (canonServices xs).Perm xs :=
  canonServices_perm_of_nodup_keys hnd

end NormalizeRow

end EffectCoreLocalAnchors

/-! ## Kernel receipts -/

#print axioms EffectCoreLocalAnchors.DiagnosticLocal.diagnostic_local_is_false
#print axioms EffectCoreLocalAnchors.DiagnosticLocal.checker_reports_only_the_first
#print axioms EffectCoreLocalAnchors.ClassifierSemEq.classifier_semEq_is_false
#print axioms EffectCoreLocalAnchors.ClassifierSemEq.runs_agree
#print axioms EffectCoreLocalAnchors.InjectCas.injectCas_cannot_be_total
#print axioms EffectCoreLocalAnchors.NormalizeRow.normalizeRow_forward_is_false
#print axioms EffectCoreLocalAnchors.NormalizeRow.normalizeRow_with_nodup
