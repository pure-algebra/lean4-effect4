import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Lang.Interp

/-!
# `EC1-T004RW` — the imported laws, restated where they have content, and the
# three arms they do not pin

Row under implementation (`../../PROOF-DAG.md:196`):

> `EC1-T004RW` PENDING THEOREM
> existing `RootSig`/`StoreSig` and `WordSig`/`WordedSig` CAS-agreement and
> WF-preservation laws remain imported under alphabet selection
> Depends on: `stepRooted_cas_agrees`, `since_cas_agrees`, corresponding
> preservation theorems

Stage: `$lean-algebraic-systems` — the row is about a step function, its
state, and the arms an extension adds, so it is an operations/interpreter
obligation, not a data-invariant one. The stage gate asks for constructor/step
equations, interpreter preservation laws, invariant preservation, an adequacy
shape naming the observable, and *deliberately invalid* interpreters. All five
appear below; §5 is the invalid-interpreter half and it is the part that
decides the row.

Written 2026-08-31, Lean `leanprover/lean4:v4.33.1`, against `library/cas` at
the working tree. Outside every lake target, exactly like `../exhibits.lean`
and `scout-T004RW.lean`. Adds nothing to `Cas`, moves no byte, promotes no
name.

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/s1/T004RW.lean
```

## What is proved, and how it differs from the DAG row

The DAG row's predicate is "remains imported under alphabet selection".
`Alphabet`, `OpDesc` and `toSig` do not exist — every
`formal/effect-core-v1/EffectCore/Foundation/*.lean` is an empty stub and
`grep -rn Alphabet library/cas/` is empty — and the scout established that the
quantifier is either vacuous (if `toSig` SELECTS a shipped `Sig`, the import is
`rfl`) or unstatable (if it RECONSTRUCTS, no signature morphism exists in the
corpus). So the quantifier is dropped and the facts are stated at the deepest
shipped selection, `WordedSig`, where they are provable and non-vacuous.

Three groups, and the necessity ladder that forces the third:

| § | Claim | Status in the corpus |
|---|---|---|
| §2 | (A) the CAS arm refuses iff the core refuses, answers what the core answers, moves the word as the core moves it, and preserves admission | conjuncts 3–4 SHIPPED (`since_cas_agrees`, `stepWorded_preserves_wf`); conjuncts 1–2 NEW |
| §3 | (B) the publish guard read back, at worded depth | `publish_mem` ships at `stepRooted` ONLY; the worded restatement is NEW |
| §4 | (C) the right arms project: `since`, `listRoots`, `publish` | `since_suffix` SHIPPED; `listRoots` and `publish` projections do NOT EXIST AT EITHER DEPTH |
| §5 | (A) and (B) do not pin the extension; each conjunct of (C) is independently load-bearing | THREE adversaries, all NEW |
| §6 | (A) ∧ (B) ∧ (C) is the restated row | NEW |
| §7 | (A) ∧ (B) ∧ (C) plus the `pure` clause determines `stepWorded` UNIQUELY | NEW |

§5 is why this file exists. The estate proved the argument shape invalid
before the row was written: `Cas/Backend/SumAlgebra.lean:708` `badAgentSum`
satisfies the left-arm projection (`:714`) and FULL left-arm adequacy (`:721` —
"every store-only program is interpreted exactly right, which is the whole
reason no run gate catches it") and is refuted only by the RIGHT-arm
projection (`:753`). `EC1-T004RW` proposes to import exactly that left-arm
shape as its non-disturbance evidence.

The scout found one adversary. This file finds **three**. Each satisfies (A) in
full — all four conjuncts, including the two new halves — and (B), and two of
the three conjuncts of (C); each is refuted by the third. Every claim below is
a named theorem in this file, not prose:

| adversary | (A) | (B) | the two (C) conjuncts it satisfies | refuted by |
|---|---|---|---|---|
| `badSince` | `badSince_imports_the_core` | `badSince_publish_mem` | `badSince_listRoots`, `badSince_publish` | `badSince_differs` (C-`since`) |
| `badRoots` | `badRoots_imports_the_core` | `badRoots_publish_mem` | `badRoots_since`, `badRoots_publish` | `badRoots_differs` (C-`listRoots`) |
| `badPublish` | `badPublish_imports_the_core` | `badPublish_publish_mem` | `badPublish_since`, `badPublish_listRoots` | `badPublish_differs` (C-`publish`) |

Each conjunct of (C) is therefore independently load-bearing: drop any one and
the corresponding adversary survives the whole remaining set.

So this file's finding is STRICTLY STRONGER than the scout's. The scout named
one genuinely owed obligation (`listRoots` has no projection law). There are
**two**: `publish` has no projection law either, at either depth. `publish_mem`
(`Roots.lean:111`) is a one-directional guard on the WORD; it says nothing
about the ROOTS, and `badPublish` satisfies it while never publishing anything.

§7 closes the ladder from the other side: the set is not merely necessary but
SUFFICIENT — no fourth adversary exists. That is the honest adequacy shape the
stage gate asks for, and it is what the row should have said.

## Axiom receipt

Every theorem carries a `#print axioms` line at the foot. Nothing here uses
`sorry`, `axiom`, `native_decide`, or `#eval`. No `Classical.choice` appears.
-/

namespace EC1T004RW

open Cas.Lang
open Cas (Addr32 Binding Bytes Node Word)

section Worded

variable (H : Bytes → Addr32)

/-! ## §1 — the core's one-operation dichotomy

The recommended (A) has a refusal conjunct and an answer conjunct. Together
they are a COMPLETE determination of the CAS arm only because a single core
operation, run with the trivial continuation, has exactly two possible
outcomes. That is not obvious from the row and is not recorded in the corpus,
so it is proved here first; §7 needs it. -/

/-- One CAS operation under `step` either refuses or answers. `.done` is
unreachable: `.vis` always has an operation left to consume, and the trivial
continuation `.pure` makes the residual program `.pure r`. -/
theorem step_op_dichotomy (e : CasE) (w : Word) :
    (∃ (why : Refusal) (w' : Word), step H (.vis e .pure) w = (.refused why, w'))
      ∨ (∃ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w')) := by
  cases e with
  | put n =>
    by_cases h : n.WF
    · cases hc : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
      | error err =>
        exact Or.inl ⟨Refusal.ofAdmission err, w, by simp [step, dif_pos h, hc]⟩
      | ok out =>
        cases out with
        | fresh a σ' =>
          exact Or.inr ⟨a, w ++ [Binding.mk a n], by simp [step, dif_pos h, hc]⟩
        | duplicate a => exact Or.inr ⟨a, w, by simp [step, dif_pos h, hc]⟩
        | conflict a m =>
          exact Or.inl ⟨Refusal.collision a, w, by simp [step, dif_pos h, hc]⟩
    · exact Or.inl ⟨.notWellFormed, w, by simp [step, dif_neg h]⟩
  | load a =>
    cases hf : Word.find w a with
    | none => exact Or.inl ⟨.noObject a, w, by simp [step, hf]⟩
    | some n => exact Or.inr ⟨n, w, by simp [step, hf]⟩
  | fail reason => exact Or.inl ⟨.failed reason, w, rfl⟩

/-! ## §2 — (A) THE CORE IMPORT

The row's dependency column names `since_cas_agrees` (`Worded.lean:134`) and
`stepWorded_preserves_wf` (`Worded.lean:144`). Both ship, both resolve at those
exact lines, and both are equations over the `.2` (STATE) component only.
`since_cas_agrees`' own docstring (`Worded.lean:129-133`) disclaims the rest:
"it does not say what status the step returns, and so it is not the claim that
wording changes no Cas answer."

The two halves the row's TITLE promises and its dependency column does not
deliver are proved here. -/

/-- The refusal half. The extension refuses on a CAS operation exactly when the
core refuses, with the same refusal. NEW — the corpus states only the state
equation. -/
theorem stepWorded_cas_refuses_iff {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32)
    (why : Refusal) :
    (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
      ↔ (step H (.vis e .pure) w).1 = .refused why := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [stepWorded, stepRooted, hs]

/-- The answer half. When the core answers `r`, the extension binds the waiting
continuation to that same `r` and leaves the roots alone. NEW. -/
theorem stepWorded_cas_answers {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) := by
  simp [stepWorded, stepRooted, h, Prog.inl, Prog.bind]

/-- The refusal half as a PAIR equation, which is what §7 consumes. It is a
consequence of the refusal iff and the shipped state equation together — stated
separately so §7's uniqueness argument can be seen to use only the conjuncts of
(A), never a fact peculiar to `stepWorded`. NEW. -/
theorem stepWorded_cas_refused {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (why : Refusal)
    (h : step H (.vis e .pure) w = (.refused why, w')) :
    stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.refused why, (w', roots)) := by
  simp [stepWorded, stepRooted, h]

/-- NON-VACUITY of the answer clause: `.running (.pure r)` is the shape a
successful `load` actually leaves, at every address function. -/
theorem answer_premise_is_inhabited (a : Addr32) (n : Node) :
    step H (.vis (.load a) .pure) [Binding.mk a n]
      = (.running (.pure n), [Binding.mk a n]) := by
  simp [step, Word.find]

/-- NON-VACUITY of the refusal clause: `fail` refuses at every word. -/
theorem refusal_premise_is_inhabited (w : Word) (reason : String) :
    (step H (.vis (.fail reason) (fun e => e.elim) : Prog CasSig Addr32) w).1
      = .refused (.failed reason) := rfl

/-- **(A) THE CORE IMPORT.** The four facts the row's title promises, at the
deepest shipped selection. Conjunct 3 is the shipped `since_cas_agrees`;
conjunct 4 is the shipped `stepWorded_preserves_wf`; conjuncts 1 and 2 are the
halves the dependency column does not deliver. -/
theorem worded_selection_imports_the_core {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (∀ why : Refusal,
        (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots)
      ∧ (Word.wf w = true →
          Word.wf (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true) :=
  ⟨fun why => stepWorded_cas_refuses_iff H e k w roots why,
   fun r w' h => stepWorded_cas_answers H e k w w' roots r h,
   since_cas_agrees H e k w roots,
   fun hw => stepWorded_preserves_wf H _ roots hw⟩

/-! ## §3 — (B) THE ROOT ARM'S GUARD, AT WORDED DEPTH

`publish_mem` (`Roots.lean:111`) is the fail-closed guard read back: a
successful publish's address is bound in the word. It is stated at `stepRooted`
ONLY. Selecting `WordedSig` puts the root arm one injection deeper and the
shipped theorem no longer applies to the program you actually have. The
restatement is mechanical and its absence is real. -/

/-- `publish_mem` at the worded tower. NEW — no `stepWorded` counterpart ships. -/
theorem publish_mem_worded {A} {a : Addr32}
    {k : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none => simp [stepWorded, stepRooted, hf] at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-! ## §4 — (C) THE RIGHT-ARM PROJECTIONS

§5 proves (A) and (B) together do not pin the extension. What catches an
adversary is always the RIGHT-arm projection — the estate's own lesson at
`SumAlgebra.lean:753`, and the law shape `Handler.sum_handle_inr`
(`SumAlgebra.lean:202`) already has.

`WordedSig` has three right arms below the CAS core: `since` (the `WordSig`
arm) and `publish`/`listRoots` (the `RootSig` arm). Exactly one of the three
has a shipped projection law.

* `since` — SHIPPED as `since_suffix` (`Worded.lean:110`), which the row's
  dependency column does not name. Cited below, not restated.
* `listRoots` — NO THEOREM AT EITHER DEPTH. Verified: `grep -rn listRoots
  library/cas/Cas` returns the constructor, the `Ans` arm, the smart
  constructor (`Roots.lean:52`), the `stepRooted` clause (`:81`) and the WF
  case (`:107`). Zero theorems. Proved here.
* `publish` — NO PROJECTION AT EITHER DEPTH either. `publish_mem` is a
  one-directional guard about the WORD and says nothing about the ROOTS. This
  gap is not in the scout's report; §5c proves it load-bearing. Proved here. -/

/-- The `since` arm's projection, at the worded tower. This is the shipped
`since_suffix` (`Worded.lean:110`) handed back verbatim — the law that actually
does the row's work, and the one its dependency column does not name. -/
theorem since_projects {A} (mark : Nat) (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inr (.since mark)) k) (w, roots)
        = (.running (k (w.drop mark)), (w, roots))
      ∧ w.drop mark <:+ w :=
  since_suffix H mark k w roots

/-- The `listRoots` arm's projection, at the rooted tower. NEW — the corpus has
no theorem about `listRoots` at any depth. -/
theorem listRoots_answers_the_roots_rooted {A}
    (k : List Addr32 → Prog StoreSig A) (w : Word) (roots : List Addr32) :
    stepRooted H (.vis (Sum.inr .listRoots) k) (w, roots)
      = (.running (k roots), (w, roots)) := rfl

/-- The `listRoots` arm's projection, at the worded tower — the depth the row's
selection actually reaches. NEW. -/
theorem listRoots_answers_the_roots {A}
    (k : List Addr32 → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) k) (w, roots)
      = (.running (k roots), (w, roots)) := rfl

/-- The `publish` arm's projection, admitting half: a bound address is appended
to the roots, in order, and the word is untouched. NEW — `publish_mem` is the
converse guard and does not state this. -/
theorem publish_appends_the_root {A} (a : Addr32)
    (k : Unit → Prog WordedSig A) (w : Word) (roots : List Addr32) {n : Node}
    (hf : Word.find w a = some n) :
    stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
      = (.running (k ()), (w, roots ++ [a])) := by
  simp [stepWorded, stepRooted, hf, Prog.inl, Prog.bind]

/-- The `publish` arm's projection, refusing half: publication of absent content
refuses with `noObject` and changes nothing. NEW. -/
theorem publish_refuses_unbound {A} (a : Addr32)
    (k : Unit → Prog WordedSig A) (w : Word) (roots : List Addr32)
    (hf : Word.find w a = none) :
    stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
      = (.refused (.noObject a), (w, roots)) := by
  simp [stepWorded, stepRooted, hf]

/-- **(C) THE RIGHT-ARM PROJECTIONS**, bundled. Only the first conjunct ships. -/
theorem worded_right_arms_project {A} (mark : Nat) (a : Addr32)
    (ks : Word → Prog WordedSig A) (kr : List Addr32 → Prog WordedSig A)
    (kp : Unit → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (stepWorded H (.vis (Sum.inr (.since mark)) ks) (w, roots)
        = (.running (ks (w.drop mark)), (w, roots)) ∧ w.drop mark <:+ w)
      ∧ (stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
          = (.running (kr roots), (w, roots)))
      ∧ (∀ n, Word.find w a = some n →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running (kp ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.refused (.noObject a), (w, roots))) :=
  ⟨since_projects H mark ks w roots,
   listRoots_answers_the_roots H kr w roots,
   fun _ hf => publish_appends_the_root H a kp w roots hf,
   fun hf => publish_refuses_unbound H a kp w roots hf⟩

end Worded

/-! ## §5 — THE FINDING: the imported set does not pin the extension

Three adversaries, each a total worded step function. Every one delegates the
CAS arm to `stepWorded` verbatim, so every one satisfies (A) in full and
`stepWorded_preserves_wf` in full. They differ from `stepWorded` on exactly one
right arm each, and the conjunct of (C) that catches each one is the conjunct
the other two satisfy.

This is `Cas/Backend/SumAlgebra.lean`'s `badAgentSum` argument
(`:708`/`:721`/`:753`) instantiated at this row's own carriers, three times.

Design note: the arms an adversary gets RIGHT are written as literal calls to
`stepWorded`, not as re-implementations. That is deliberate — it makes "this
adversary satisfies the law" a fact about the shipped interpreter rather than a
fresh calculation, so a reader cannot suspect the agreement was engineered. -/

section Adversaries

variable (H : Bytes → Addr32)

/-! ### §5a — `badSince`: answers every `since` with the empty word -/

/-- ADVERSARY 1. Correct on CAS, `publish` and `listRoots`; reports that
nothing has ever happened. -/
def badSince {A : Type} :
    Prog WordedSig A → Word × List Addr32 → Status WordedSig A × (Word × List Addr32)
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl (Sum.inl e)) k, s => stepWorded H (.vis (Sum.inl (Sum.inl e)) k) s
  | .vis (Sum.inl (Sum.inr (.publish a))) k, s =>
      stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) s
  | .vis (Sum.inl (Sum.inr .listRoots)) k, s =>
      stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) k) s
  | .vis (Sum.inr (.since _)) k, (w, roots) => (.running (k []), (w, roots))

/-- `badSince` satisfies `since_cas_agrees` VERBATIM — one of the two theorems
the row names. -/
theorem badSince_cas_agrees {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) :=
  since_cas_agrees H e k w roots

/-- `badSince` satisfies `stepWorded_preserves_wf` VERBATIM — the other theorem
the row names. -/
theorem badSince_preserves_wf {A} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badSince H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl e)) k =>
      simpa [badSince] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl e)) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      simpa [badSince] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr (.publish a))) k) roots hw
  | .vis (Sum.inl (Sum.inr .listRoots)) k =>
      simpa [badSince] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr .listRoots)) k) roots hw
  | .vis (Sum.inr (.since mark)) k => exact hw

/-- `badSince` also satisfies the strengthened §2 halves, so hardening the
CAS-agreement law does not catch it either. -/
theorem badSince_cas_answers {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) :=
  stepWorded_cas_answers H e k w w' roots r h

/-- `badSince` satisfies (B): the publish guard survives it untouched. -/
theorem badSince_publish_mem {A} {a : Addr32}
    {k : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : badSince H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w :=
  publish_mem_worded H h

/-- `badSince` satisfies the `listRoots` conjunct of (C). -/
theorem badSince_listRoots {A}
    (k : List Addr32 → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    badSince H (.vis (Sum.inl (Sum.inr .listRoots)) k) (w, roots)
      = (.running (k roots), (w, roots)) := rfl

/-- `badSince` satisfies the `publish` conjunct of (C), both halves. -/
theorem badSince_publish {A} (a : Addr32) (k : Unit → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    (∀ n, Word.find w a = some n →
        badSince H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
          = (.running (k ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          badSince H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
            = (.refused (.noObject a), (w, roots))) :=
  ⟨fun _ hf => publish_appends_the_root H a k w roots hf,
   fun hf => publish_refuses_unbound H a k w roots hf⟩

/-- **`badSince` satisfies (A) IN FULL** — all four conjuncts, including the two
new halves of §2. The proof is `worded_selection_imports_the_core` handed back
verbatim: on the CAS arm the adversary IS `stepWorded`, definitionally. That is
the estate's `badAgentSum_interpret_inl` (`SumAlgebra.lean:721`) argument —
"every store-only program is interpreted exactly right, which is the whole
reason no run gate catches it" — at this row's carriers. -/
theorem badSince_imports_the_core {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (∀ why : Refusal,
        (badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots)
      ∧ (Word.wf w = true →
          Word.wf (badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true) :=
  worded_selection_imports_the_core H e k w roots

/-- The observable the falsifier reads: the word a continuing `since` binds. -/
def answeredWord : Status WordedSig Word × (Word × List Addr32) → Word
  | (.running (.pure v), _) => v
  | _ => []

/-- **FALSIFIER 1.** `badSince` is not `stepWorded`: at a one-binding word it
reports that nothing has ever happened. Concrete, at every `H`. This is the
`since` conjunct of (C) doing the work. -/
theorem badSince_differs (a : Addr32) (n : Node) (roots : List Addr32) :
    badSince H (.vis (Sum.inr (.since 0)) (A := Word) .pure) ([Binding.mk a n], roots)
      ≠ stepWorded H (.vis (Sum.inr (.since 0)) .pure) ([Binding.mk a n], roots) := by
  intro h
  have h1 : ([] : Word) = [Binding.mk a n] := congrArg answeredWord h
  exact absurd h1 (by simp)

/-! ### §5b — `badRoots`: answers every `listRoots` with the empty list -/

/-- ADVERSARY 2. Correct on CAS, `publish` and `since` — it satisfies
everything `badSince` satisfies PLUS the `since` conjunct that caught
`badSince`. It never reports a published root. -/
def badRoots {A : Type} :
    Prog WordedSig A → Word × List Addr32 → Status WordedSig A × (Word × List Addr32)
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl (Sum.inl e)) k, s => stepWorded H (.vis (Sum.inl (Sum.inl e)) k) s
  | .vis (Sum.inl (Sum.inr (.publish a))) k, s =>
      stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) s
  | .vis (Sum.inl (Sum.inr .listRoots)) k, (w, roots) => (.running (k []), (w, roots))
  | .vis (Sum.inr (.since mark)) k, s => stepWorded H (.vis (Sum.inr (.since mark)) k) s

/-- `badRoots` satisfies `since_cas_agrees` VERBATIM. -/
theorem badRoots_cas_agrees {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) :=
  since_cas_agrees H e k w roots

/-- `badRoots` satisfies `stepWorded_preserves_wf` VERBATIM. -/
theorem badRoots_preserves_wf {A} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badRoots H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl e)) k =>
      simpa [badRoots] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl e)) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      simpa [badRoots] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr (.publish a))) k) roots hw
  | .vis (Sum.inl (Sum.inr .listRoots)) k => exact hw
  | .vis (Sum.inr (.since mark)) k =>
      simpa [badRoots] using stepWorded_preserves_wf H
        (.vis (Sum.inr (.since mark)) k) roots hw

/-- `badRoots` satisfies (B). -/
theorem badRoots_publish_mem {A} {a : Addr32}
    {k : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : badRoots H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w :=
  publish_mem_worded H h

/-- `badRoots` satisfies the `since` conjunct of (C) — the very law that caught
`badSince`. The ladder is strictly increasing. -/
theorem badRoots_since {A} (mark : Nat) (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    badRoots H (.vis (Sum.inr (.since mark)) k) (w, roots)
        = (.running (k (w.drop mark)), (w, roots))
      ∧ w.drop mark <:+ w :=
  since_suffix H mark k w roots

/-- `badRoots` satisfies the `publish` conjunct of (C), both halves. -/
theorem badRoots_publish {A} (a : Addr32) (k : Unit → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    (∀ n, Word.find w a = some n →
        badRoots H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
          = (.running (k ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          badRoots H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
            = (.refused (.noObject a), (w, roots))) :=
  ⟨fun _ hf => publish_appends_the_root H a k w roots hf,
   fun hf => publish_refuses_unbound H a k w roots hf⟩

/-- **`badRoots` satisfies (A) IN FULL** — same argument as `badSince`. -/
theorem badRoots_imports_the_core {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (∀ why : Refusal,
        (badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots)
      ∧ (Word.wf w = true →
          Word.wf (badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true) :=
  worded_selection_imports_the_core H e k w roots

/-- The observable the second falsifier reads. -/
def answeredRoots : Status WordedSig (List Addr32) × (Word × List Addr32) → List Addr32
  | (.running (.pure v), _) => v
  | _ => []

/-- **FALSIFIER 2.** `badRoots` is not `stepWorded`: it reports no roots where
one was published. Only the `listRoots` conjunct of (C) separates them, and that
conjunct has NO theorem in the corpus at either depth. -/
theorem badRoots_differs (w : Word) (a : Addr32) :
    badRoots H (.vis (Sum.inl (Sum.inr .listRoots)) (A := List Addr32) .pure) (w, [a])
      ≠ stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) .pure) (w, [a]) := by
  intro h
  have h1 : ([] : List Addr32) = [a] := congrArg answeredRoots h
  exact absurd h1 (by simp)

/-! ### §5c — `badPublish`: never actually publishes

This adversary is the one the scout's report does not contain, and it is the
sharper half of the finding. It satisfies (A), (B), and BOTH the conjuncts of
(C) that catch the first two adversaries. It publishes nothing.

That `publish_mem` survives it is the point: `publish_mem` is a guard on the
WORD (was the address bound?) and says nothing whatever about the ROOTS. So the
`RootSig` arm owes TWO projection laws, not one. -/

/-- ADVERSARY 3. Correct on CAS, `listRoots` and `since`; accepts every
publication and records none. -/
def badPublish {A : Type} :
    Prog WordedSig A → Word × List Addr32 → Status WordedSig A × (Word × List Addr32)
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl (Sum.inl e)) k, s => stepWorded H (.vis (Sum.inl (Sum.inl e)) k) s
  | .vis (Sum.inl (Sum.inr (.publish a))) k, (w, roots) =>
      match Word.find w a with
      | some _ => (.running (k ()), (w, roots))
      | none => (.refused (.noObject a), (w, roots))
  | .vis (Sum.inl (Sum.inr .listRoots)) k, s =>
      stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) k) s
  | .vis (Sum.inr (.since mark)) k, s => stepWorded H (.vis (Sum.inr (.since mark)) k) s

/-- `badPublish` satisfies `since_cas_agrees` VERBATIM. -/
theorem badPublish_cas_agrees {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) :=
  since_cas_agrees H e k w roots

/-- `badPublish` satisfies `stepWorded_preserves_wf` VERBATIM. -/
theorem badPublish_preserves_wf {A} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badPublish H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl e)) k =>
      simpa [badPublish] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl e)) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      cases hf : Word.find w a <;> simp [badPublish, hf, hw]
  | .vis (Sum.inl (Sum.inr .listRoots)) k =>
      simpa [badPublish] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr .listRoots)) k) roots hw
  | .vis (Sum.inr (.since mark)) k =>
      simpa [badPublish] using stepWorded_preserves_wf H
        (.vis (Sum.inr (.since mark)) k) roots hw

/-- **`badPublish` satisfies (B).** The publish guard `publish_mem` — the only
`RootSig` theorem the estate owns, at either depth — holds of an interpreter
that never publishes. -/
theorem badPublish_publish_mem {A} {a : Addr32}
    {k : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : badPublish H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none => simp [badPublish, hf] at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-- `badPublish` satisfies the `since` conjunct of (C). -/
theorem badPublish_since {A} (mark : Nat) (k : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    badPublish H (.vis (Sum.inr (.since mark)) k) (w, roots)
        = (.running (k (w.drop mark)), (w, roots))
      ∧ w.drop mark <:+ w :=
  since_suffix H mark k w roots

/-- `badPublish` satisfies the `listRoots` conjunct of (C). -/
theorem badPublish_listRoots {A}
    (k : List Addr32 → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    badPublish H (.vis (Sum.inl (Sum.inr .listRoots)) k) (w, roots)
      = (.running (k roots), (w, roots)) := rfl

/-- **`badPublish` satisfies (A) IN FULL** — same argument as `badSince`. -/
theorem badPublish_imports_the_core {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (∀ why : Refusal,
        (badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots)
      ∧ (Word.wf w = true →
          Word.wf (badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true) :=
  worded_selection_imports_the_core H e k w roots

/-- **FALSIFIER 3.** `badPublish` is not `stepWorded`: the address is bound, the
publication is accepted, and the roots do not grow. Only the `publish` conjunct
of (C) separates them — a law the corpus does not state at either depth. -/
theorem badPublish_differs (a : Addr32) (n : Node) :
    badPublish H (.vis (Sum.inl (Sum.inr (.publish a))) (A := Unit) .pure)
        ([Binding.mk a n], [])
      ≠ stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) .pure)
        ([Binding.mk a n], []) := by
  intro h
  have hr := congrArg (fun x => x.2.2) h
  simp [badPublish, stepWorded, stepRooted, Word.find] at hr

/-! ### §5d — the headline

Every law `EC1-T004RW` names, plus the strengthened halves of §2, plus the only
`RootSig` theorem the estate owns, all hold of three different interpreters,
each of which is wrong. -/

/-- **`EC1-T004RW` AS WRITTEN DOES NOT PIN THE EXTENSION.** One statement, three
adversaries. Each satisfies the row's full dependency set — `since_cas_agrees`
verbatim, `stepWorded_preserves_wf` verbatim — and (B), the worded publish
guard, and each is refuted by a different right-arm projection. -/
theorem imported_laws_do_not_pin_the_extension
    (a : Addr32) (n : Node) (roots : List Addr32) :
    ((∀ {A} (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
          (rs : List Addr32),
          (badSince H (.vis (Sum.inl (Sum.inl e)) k) (w, rs)).2
            = ((step H (.vis e .pure) w).2, rs))
        ∧ (∀ {A} (p : Prog WordedSig A) (w : Word) (rs : List Addr32),
            Word.wf w = true → Word.wf (badSince H p (w, rs)).2.1 = true)
        ∧ badSince H (.vis (Sum.inr (.since 0)) (A := Word) .pure)
              ([Binding.mk a n], roots)
            ≠ stepWorded H (.vis (Sum.inr (.since 0)) .pure)
              ([Binding.mk a n], roots))
      ∧ ((∀ {A} (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
            (rs : List Addr32),
            (badRoots H (.vis (Sum.inl (Sum.inl e)) k) (w, rs)).2
              = ((step H (.vis e .pure) w).2, rs))
          ∧ (∀ {A} (p : Prog WordedSig A) (w : Word) (rs : List Addr32),
              Word.wf w = true → Word.wf (badRoots H p (w, rs)).2.1 = true)
          ∧ badRoots H (.vis (Sum.inl (Sum.inr .listRoots)) (A := List Addr32) .pure)
                ([Binding.mk a n], [a])
              ≠ stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) .pure)
                ([Binding.mk a n], [a]))
      ∧ ((∀ {A} (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
            (rs : List Addr32),
            (badPublish H (.vis (Sum.inl (Sum.inl e)) k) (w, rs)).2
              = ((step H (.vis e .pure) w).2, rs))
          ∧ (∀ {A} (p : Prog WordedSig A) (w : Word) (rs : List Addr32),
              Word.wf w = true → Word.wf (badPublish H p (w, rs)).2.1 = true)
          ∧ badPublish H (.vis (Sum.inl (Sum.inr (.publish a))) (A := Unit) .pure)
                ([Binding.mk a n], [])
              ≠ stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) .pure)
                ([Binding.mk a n], [])) :=
  ⟨⟨fun e k w rs => badSince_cas_agrees H e k w rs,
    fun p _w rs hw => badSince_preserves_wf H p rs hw,
    badSince_differs H a n roots⟩,
   ⟨fun e k w rs => badRoots_cas_agrees H e k w rs,
    fun p _w rs hw => badRoots_preserves_wf H p rs hw,
    badRoots_differs H [Binding.mk a n] a⟩,
   ⟨fun e k w rs => badPublish_cas_agrees H e k w rs,
    fun p _w rs hw => badPublish_preserves_wf H p rs hw,
    badPublish_differs H a n⟩⟩

end Adversaries

/-! ## §6 — THE RESTATED ROW

`EC1-T004RW`, as it should read. The quantifier over "alphabet selection" is
dropped (§1 of the scout: vacuous under selection, unstatable under
reconstruction) and the facts are stated at the deepest shipped selection.
`Alphabet`, `OpDesc` and `toSig` are not needed and do not appear — that is
what makes this an IMPORT/REUSE row rather than a blocked one. -/

section Restated

variable (H : Bytes → Addr32)

/-- **`EC1-T004RW`, restated and proved.** At the worded selection: the CAS arm
refuses exactly when the core refuses, answers exactly what the core answers,
moves the word exactly as the core moves it, leaves the roots alone, and
preserves admission (A); the publication guard survives at this depth (B); and
each of the three right arms projects (C). -/
theorem worded_selection_imports_and_pins {A} (e : CasE) (a : Addr32) (mark : Nat)
    (k : CasE.Ans e → Prog WordedSig A) (kp : Unit → Prog WordedSig A)
    (kr : List Addr32 → Prog WordedSig A) (ks : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    -- (A) the core import
    ((∀ why : Refusal,
        (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots)
      ∧ (Word.wf w = true →
          Word.wf (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true))
    -- (B) the root arm's guard at worded depth
    ∧ (∀ {rest : Prog WordedSig A} {s' : Word × List Addr32},
        stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running rest, s') → ∃ n, Binding.mk a n ∈ w)
    -- (C) the right-arm projections
    ∧ ((stepWorded H (.vis (Sum.inr (.since mark)) ks) (w, roots)
          = (.running (ks (w.drop mark)), (w, roots)) ∧ w.drop mark <:+ w)
      ∧ (stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
          = (.running (kr roots), (w, roots)))
      ∧ (∀ n, Word.find w a = some n →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running (kp ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.refused (.noObject a), (w, roots)))) :=
  ⟨worded_selection_imports_the_core H e k w roots,
   fun h => publish_mem_worded H h,
   worded_right_arms_project H mark a ks kr kp w roots⟩

/-! ## §7 — ADEQUACY: the restated set is SUFFICIENT

§5 shows each conjunct of (C) is necessary. This shows the whole set is enough:
any worded step function satisfying (A)'s refusal/answer/state conjuncts,
(C)'s three projections, and the `pure` clause IS `stepWorded`. So no fourth
adversary exists, and the restated row is not merely stronger than the DAG's —
it is exactly as strong as the interpreter it is about.

This is the stage gate's "refinement/adequacy theorem shape naming observable
behavior", and it is the reason to prefer (A)∧(B)∧(C) over any further
strengthening: nothing more can be bought.

Note what is NOT among the hypotheses: `stepWorded_preserves_wf` and
`publish_mem_worded`. Both are consequences of the equations above, so the row's
two named dependencies are subsumed — a second sense in which the row's
dependency column is not the load-bearing set. -/

/-- A pair is its two components. Used once, to assemble the CAS refusal case
out of (A)'s status conjunct and (A)'s state conjunct — which is the precise
sense in which those two conjuncts together pin the refusing CAS step. -/
theorem pair_of_components {α β : Type} {x : α × β} {a : α} {b : β}
    (h1 : x.1 = a) (h2 : x.2 = b) : x = (a, b) := by
  cases x with
  | mk u v => simp_all

/-- **The restated conjunct set determines `stepWorded` uniquely.** `A` is fixed
because the worded step is a single-step function: it never recurses on the
program, so one type index suffices and no universe polymorphism is involved. -/
theorem stepWorded_unique {A : Type}
    (f : Prog WordedSig A → Word × List Addr32 →
      Status WordedSig A × (Word × List Addr32))
    (hpure : ∀ (a : A) (s : Word × List Addr32), f (.pure a) s = (.done a, s))
    (hcasRef : ∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
        (roots : List Addr32) (why : Refusal),
        (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
    (hcasSt : ∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
        (roots : List Addr32),
        (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
          = ((step H (.vis e .pure) w).2, roots))
    (hcasAns : ∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w w' : Word)
        (roots : List Addr32) (r : CasE.Ans e),
        step H (.vis e .pure) w = (.running (.pure r), w') →
          f (.vis (Sum.inl (Sum.inl e)) k) (w, roots) = (.running (k r), (w', roots)))
    (hpubSome : ∀ (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
        (roots : List Addr32) (n : Node), Word.find w a = some n →
        f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
          = (.running (kp ()), (w, roots ++ [a])))
    (hpubNone : ∀ (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
        (roots : List Addr32), Word.find w a = none →
        f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
          = (.refused (.noObject a), (w, roots)))
    (hroots : ∀ (kr : List Addr32 → Prog WordedSig A) (w : Word)
        (roots : List Addr32),
        f (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
          = (.running (kr roots), (w, roots)))
    (hsince : ∀ (mark : Nat) (ks : Word → Prog WordedSig A) (w : Word)
        (roots : List Addr32),
        f (.vis (Sum.inr (.since mark)) ks) (w, roots)
          = (.running (ks (w.drop mark)), (w, roots))) :
    ∀ (p : Prog WordedSig A) (s : Word × List Addr32), f p s = stepWorded H p s
  | .pure a, (w, roots) => by
      exact (hpure a (w, roots)).trans rfl
  | .vis (Sum.inl (Sum.inl e)) k, (w, roots) => by
      rcases step_op_dichotomy H e w with ⟨why, w', hs⟩ | ⟨r, w', hs⟩
      · have h1 : (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why :=
          (hcasRef e k w roots why).2 (by rw [hs])
        have h2 : (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2 = (w', roots) := by
          have := hcasSt e k w roots
          rw [hs] at this
          exact this
        exact (pair_of_components h1 h2).trans
          (stepWorded_cas_refused H e k w w' roots why hs).symm
      · exact (hcasAns e k w w' roots r hs).trans
          (stepWorded_cas_answers H e k w w' roots r hs).symm
  | .vis (Sum.inl (Sum.inr (.publish a))) k, (w, roots) => by
      cases hfind : Word.find w a with
      | some n =>
        exact (hpubSome a k w roots n hfind).trans
          (publish_appends_the_root H a k w roots hfind).symm
      | none =>
        exact (hpubNone a k w roots hfind).trans
          (publish_refuses_unbound H a k w roots hfind).symm
  | .vis (Sum.inl (Sum.inr .listRoots)) k, (w, roots) => by
      exact (hroots k w roots).trans (listRoots_answers_the_roots H k w roots).symm
  | .vis (Sum.inr (.since mark)) k, (w, roots) => by
      exact (hsince mark k w roots).trans (since_projects H mark k w roots).1.symm

/-- **The row's two NAMED dependencies are subsumed, not assumed.** Given the
conclusion of `stepWorded_unique`, both `stepWorded_preserves_wf` and the
worded publish guard follow. So the dependency column names two facts that the
restated set already implies, and omits the three (`since`, `listRoots`,
`publish` projections) that §5 proves it cannot do without. That is the whole
finding in one theorem. -/
theorem named_dependencies_are_subsumed {A : Type}
    (f : Prog WordedSig A → Word × List Addr32 →
      Status WordedSig A × (Word × List Addr32))
    (hf : ∀ (p : Prog WordedSig A) (s : Word × List Addr32), f p s = stepWorded H p s) :
    (∀ (p : Prog WordedSig A) (w : Word) (roots : List Addr32), Word.wf w = true →
        Word.wf (f p (w, roots)).2.1 = true)
      ∧ (∀ (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
          (roots : List Addr32) (rest : Prog WordedSig A) (s' : Word × List Addr32),
          f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots) = (.running rest, s') →
            ∃ n, Binding.mk a n ∈ w) := by
  refine ⟨fun p w roots hw => ?_, fun a kp w roots rest s' h => ?_⟩
  · rw [hf]
    exact stepWorded_preserves_wf H p roots hw
  · rw [hf] at h
    exact publish_mem_worded H h

/-- The adequacy statement in the form a reviewer wants: `stepWorded` itself
satisfies every hypothesis of `stepWorded_unique`, so the characterization is
non-vacuous — the conjunct set has at least one model, and by
`stepWorded_unique` exactly one. -/
theorem stepWorded_satisfies_its_characterization {A : Type} :
    (∀ (a : A) (s : Word × List Addr32), stepWorded H (.pure a) s = (.done a, s))
      ∧ (∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
          (roots : List Addr32) (why : Refusal),
          (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
            ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
          (roots : List Addr32),
          (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
            = ((step H (.vis e .pure) w).2, roots))
      ∧ (∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w w' : Word)
          (roots : List Addr32) (r : CasE.Ans e),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (∀ (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
          (roots : List Addr32) (n : Node), Word.find w a = some n →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running (kp ()), (w, roots ++ [a])))
      ∧ (∀ (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
          (roots : List Addr32), Word.find w a = none →
          stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.refused (.noObject a), (w, roots)))
      ∧ (∀ (kr : List Addr32 → Prog WordedSig A) (w : Word) (roots : List Addr32),
          stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
            = (.running (kr roots), (w, roots)))
      ∧ (∀ (mark : Nat) (ks : Word → Prog WordedSig A) (w : Word)
          (roots : List Addr32),
          stepWorded H (.vis (Sum.inr (.since mark)) ks) (w, roots)
            = (.running (ks (w.drop mark)), (w, roots))) :=
  ⟨fun _ _ => rfl,
   fun e k w roots why => stepWorded_cas_refuses_iff H e k w roots why,
   fun e k w roots => since_cas_agrees H e k w roots,
   fun e k w w' roots r h => stepWorded_cas_answers H e k w w' roots r h,
   fun a kp w roots _ hf => publish_appends_the_root H a kp w roots hf,
   fun a kp w roots hf => publish_refuses_unbound H a kp w roots hf,
   fun kr w roots => listRoots_answers_the_roots H kr w roots,
   fun mark ks w roots => (since_projects H mark ks w roots).1⟩

end Restated

/-! ## Receipts -/

#print axioms step_op_dichotomy
#print axioms stepWorded_cas_refuses_iff
#print axioms stepWorded_cas_answers
#print axioms stepWorded_cas_refused
#print axioms answer_premise_is_inhabited
#print axioms refusal_premise_is_inhabited
#print axioms worded_selection_imports_the_core
#print axioms publish_mem_worded
#print axioms since_projects
#print axioms listRoots_answers_the_roots_rooted
#print axioms listRoots_answers_the_roots
#print axioms publish_appends_the_root
#print axioms publish_refuses_unbound
#print axioms worded_right_arms_project
#print axioms badSince_cas_agrees
#print axioms badSince_preserves_wf
#print axioms badSince_cas_answers
#print axioms badSince_publish_mem
#print axioms badSince_listRoots
#print axioms badSince_publish
#print axioms badSince_imports_the_core
#print axioms badSince_differs
#print axioms badRoots_cas_agrees
#print axioms badRoots_preserves_wf
#print axioms badRoots_publish_mem
#print axioms badRoots_since
#print axioms badRoots_publish
#print axioms badRoots_imports_the_core
#print axioms badRoots_differs
#print axioms badPublish_cas_agrees
#print axioms badPublish_preserves_wf
#print axioms badPublish_publish_mem
#print axioms badPublish_since
#print axioms badPublish_listRoots
#print axioms badPublish_imports_the_core
#print axioms badPublish_differs
#print axioms imported_laws_do_not_pin_the_extension
#print axioms worded_selection_imports_and_pins
#print axioms pair_of_components
#print axioms stepWorded_unique
#print axioms named_dependencies_are_subsumed
#print axioms stepWorded_satisfies_its_characterization

end EC1T004RW
