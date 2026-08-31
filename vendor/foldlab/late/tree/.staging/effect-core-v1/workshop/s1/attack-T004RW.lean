import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Lang.Interp

/-!
# `attack-T004RW` — breaker witnesses against `T004RW.lean`

Read-only attack file. Adds nothing to `Cas`, promotes no name, changes no
byte of `library/` or `formal/`. Outside every lake target; borrows
`library/cas`'s environment exactly as `T004RW.lean` does.

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T004RW.lean
```

The target file elaborates green with 42 receipts and no `sorry`, `axiom`, or
`native_decide`. Every proposition it STATES is true. This file attacks the
claims it makes ABOUT those propositions — the necessity ladder, the
subsumption claim, and the redundancy of the bundle.

Four attacks, all mechanical:

| § | Attack | Result |
|---|---|---|
| §1 | Is (A) conjunct 4 (WF preservation at the CAS node) independent of conjunct 3? | NO. It follows from conjunct 3 alone, for ANY `f`, via the shipped `step_preserves_wf`. |
| §2 | Is (B), the worded publish guard, independent of (C)? | NO. It follows from (C)'s two publish conjuncts alone, for ANY `f`. |
| §3 | Is `since_cas_agrees` — a NAMED dependency of the DAG row — "a consequence, not an input"? | NO. `badState` satisfies every other hypothesis of `stepWorded_unique` and is not `stepWorded`. |
| §4 | Does §5's three-adversary ladder show "each conjunct of (C) is independently load-bearing"? | Only 3 of the 4. `badWhy` and `badPubNone` are the two missing rungs. |
| §5 | `EC1-F87` — can the extension arms be flattened into one projection law? | NO, and the proof survives: the arms are provably inequivalent. |

Nothing here refutes a theorem of `T004RW.lean`. Everything here refutes a
sentence of its prose or fills a hole in its ladder.
-/

namespace EC1T004RWAttack

open Cas.Lang
open Cas (Addr32 Binding Bytes Node Word)

section Attack

variable (H : Bytes → Addr32)

/-! ## §1 — (A) conjunct 4 is NOT independent of conjunct 3

`T004RW.lean:49` bills (A) as four conjuncts, "conjuncts 3–4 SHIPPED
(`since_cas_agrees`, `stepWorded_preserves_wf`)". Conjunct 4 is
`stepWorded_preserves_wf` narrowed to a CAS node. It is a formal consequence of
conjunct 3 plus the shipped CORE law `step_preserves_wf` (`Interp.lean:119`) —
for a bare function variable, so no property of `stepWorded` is used.

So (A) carries three independent conjuncts, not four, and one of the row's two
"imports" is not an import at this depth: it is arithmetic on the other one. -/

/-- (A)-4 follows from (A)-3, for ANY `f`. The only extra input is the shipped
core preservation law. -/
theorem wf_conjunct_follows_from_state_conjunct {A : Type}
    (f : Prog WordedSig A → Word × List Addr32 →
      Status WordedSig A × (Word × List Addr32))
    (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
    (roots : List Addr32)
    (hSt : (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
        = ((step H (.vis e .pure) w).2, roots))
    (hw : Word.wf w = true) :
    Word.wf (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2.1 = true := by
  rw [hSt]
  exact step_preserves_wf H (.vis e .pure) hw

/-! ## §2 — (B) is NOT independent of (C)

`worded_selection_imports_and_pins` is stated as (A) ∧ (B) ∧ (C). (B) — the
worded publish guard, `publish_mem_worded` — follows from (C)'s two publish
conjuncts alone, for a bare `f`. No uniqueness theorem is needed and no
property of `stepWorded` is used.

`T004RW.lean:846` claims (B) is subsumed only "given the conclusion of
`stepWorded_unique`". It is subsumed much earlier and much more cheaply. -/

/-- (B) follows from (C)'s two publish conjuncts, for ANY `f`. -/
theorem guard_B_follows_from_C_publish {A : Type}
    (f : Prog WordedSig A → Word × List Addr32 →
      Status WordedSig A × (Word × List Addr32))
    (a : Addr32) (kp : Unit → Prog WordedSig A) (w : Word)
    (roots : List Addr32)
    (_hSome : ∀ n, Word.find w a = some n →
        f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
          = (.running (kp ()), (w, roots ++ [a])))
    (hNone : Word.find w a = none →
        f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
          = (.refused (.noObject a), (w, roots)))
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : f (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none =>
    rw [hNone hf] at h
    simp at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-! ## §3 — `since_cas_agrees` IS AN INPUT, not a consequence

`T004RW.lean:849-854`, `named_dependencies_are_subsumed`:

> **The row's two NAMED dependencies are subsumed, not assumed.** ... So the
> dependency column names two facts that the restated set already implies

The DAG dependency column (`PROOF-DAG.md:196`) reads
`stepRooted_cas_agrees`, `since_cas_agrees`, corresponding preservation
theorems. What `named_dependencies_are_subsumed` actually subsumes is
`stepWorded_preserves_wf` and `publish_mem_worded`. The second of those is NOT
in the column; `since_cas_agrees`, which IS, is hypothesis `hcasSt` of
`stepWorded_unique` (`T004RW.lean:799`) — an input.

`badState` proves the input is load-bearing: it satisfies `hpure`, `hcasRef`,
`hcasAns`, `hpubSome`, `hpubNone`, `hroots`, `hsince`, (B), and
`stepWorded_preserves_wf` in full, and it is not `stepWorded`. Drop
`since_cas_agrees` from the characterization and uniqueness fails.

The mechanism is the one arm `T004RW.lean` never probes: `since_cas_agrees` is
the ONLY hypothesis that constrains the state on a REFUSING CAS step. `hcasRef`
pins the status and says nothing about the state; `hcasAns`'s premise is false
there. `CasE.fail` refuses at every `H` and every word, so `badState` may
clobber the roots freely. -/

/-- ADVERSARY 4. `stepWorded` everywhere except on `CasE.fail`, where it
discards the published roots. Only `since_cas_agrees` sees it. -/
def badState {A : Type} (p : Prog WordedSig A) (s : Word × List Addr32) :
    Status WordedSig A × (Word × List Addr32) :=
  match p with
  | .vis (Sum.inl (Sum.inl (.fail reason))) _ => (.refused (.failed reason), (s.1, []))
  | _ => stepWorded H p s

/-- `badState` satisfies `hpure`. -/
theorem badState_pure {A : Type} (a : A) (s : Word × List Addr32) :
    badState H (.pure a) s = (.done a, s) := rfl

/-- `badState` satisfies `hcasRef` — (A) conjunct 1, in full. On `fail` both
sides say "the refusal is `.failed reason`"; elsewhere it IS `stepWorded`. -/
theorem badState_hcasRef {A : Type} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32)
    (why : Refusal) :
    (badState H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
      ↔ (step H (.vis e .pure) w).1 = .refused why := by
  cases e with
  | fail reason => simp [badState, step]
  | put n =>
    cases hs : step H (.vis (CasE.put n) .pure) w with
    | mk st w' => cases st <;> simp [badState, stepWorded, stepRooted, hs]
  | load a =>
    cases hs : step H (.vis (CasE.load a) .pure) w with
    | mk st w' => cases st <;> simp [badState, stepWorded, stepRooted, hs]

/-- `badState` satisfies `hcasAns` — (A) conjunct 2, in full. On `fail` the
premise is unsatisfiable; elsewhere it IS `stepWorded`. -/
theorem badState_hcasAns {A : Type} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    badState H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) := by
  cases e with
  | fail reason => simp [step] at h
  | put n => simp [badState, stepWorded, stepRooted, h, Prog.inl, Prog.bind]
  | load a => simp [badState, stepWorded, stepRooted, h, Prog.inl, Prog.bind]

/-- `badState` satisfies `hpubSome` and `hpubNone` — (C)'s publish conjuncts,
both halves, verbatim. -/
theorem badState_publish {A : Type} (a : Addr32) (kp : Unit → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    (∀ n, Word.find w a = some n →
        badState H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
          = (.running (kp ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          badState H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.refused (.noObject a), (w, roots))) :=
  ⟨fun _ hf => by simp [badState, stepWorded, stepRooted, hf, Prog.inl, Prog.bind],
   fun hf => by simp [badState, stepWorded, stepRooted, hf]⟩

/-- `badState` satisfies `hroots` — (C)'s `listRoots` conjunct. -/
theorem badState_hroots {A : Type} (kr : List Addr32 → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    badState H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
      = (.running (kr roots), (w, roots)) := rfl

/-- `badState` satisfies `hsince` — (C)'s `since` conjunct. -/
theorem badState_hsince {A : Type} (mark : Nat) (ks : Word → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    badState H (.vis (Sum.inr (.since mark)) ks) (w, roots)
      = (.running (ks (w.drop mark)), (w, roots)) := rfl

/-- `badState` satisfies `stepWorded_preserves_wf` VERBATIM, at every program —
the row's "corresponding preservation theorem". -/
theorem badState_preserves_wf {A : Type} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badState H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl (.fail reason))) k => simpa [badState] using hw
  | .vis (Sum.inl (Sum.inl (.put n))) k =>
      simpa [badState] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl (CasE.put n))) k) roots hw
  | .vis (Sum.inl (Sum.inl (.load a))) k =>
      simpa [badState] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl (CasE.load a))) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      simpa [badState] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr (RootE.publish a))) k) roots hw
  | .vis (Sum.inl (Sum.inr .listRoots)) k =>
      simpa [badState] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr RootE.listRoots)) k) roots hw
  | .vis (Sum.inr (.since mark)) k =>
      simpa [badState] using stepWorded_preserves_wf H
        (.vis (Sum.inr (WordE.since mark)) k) roots hw

/-- `badState` satisfies (B), the worded publish guard — by §2, since it
satisfies (C)'s publish conjuncts. -/
theorem badState_publish_mem {A : Type} {a : Addr32}
    {kp : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : badState H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w :=
  guard_B_follows_from_C_publish (badState H) a kp w roots
    (badState_publish H a kp w roots).1 (badState_publish H a kp w roots).2 h

/-- **FALSIFIER 4.** `badState` is not `stepWorded`: a refused `fail` discards
every published root. Only `since_cas_agrees` — hypothesis `hcasSt` — separates
them. -/
theorem badState_differs (w : Word) (a : Addr32) (reason : String) :
    badState H (.vis (Sum.inl (Sum.inl (.fail reason)))
        (A := Unit) (fun e => e.elim)) (w, [a])
      ≠ stepWorded H (.vis (Sum.inl (Sum.inl (.fail reason)))
        (fun e => e.elim)) (w, [a]) := by
  intro h
  have hr := congrArg (fun x => x.2.2) h
  simp [badState, stepWorded, stepRooted, step] at hr

/-- **THE §3 FINDING, as one statement.** `since_cas_agrees` is not subsumed:
`badState` satisfies every OTHER hypothesis of `stepWorded_unique`, plus (B)
and full WF preservation, and is not `stepWorded`. -/
theorem since_cas_agrees_is_load_bearing (w : Word) (a : Addr32) :
    ((∀ (x : Unit) (s : Word × List Addr32), badState H (.pure x) s = (.done x, s))
      ∧ (∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig Unit) (w' : Word)
          (rs : List Addr32) (why : Refusal),
          (badState H (.vis (Sum.inl (Sum.inl e)) k) (w', rs)).1 = .refused why
            ↔ (step H (.vis e .pure) w').1 = .refused why)
      ∧ (∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig Unit) (w' w'' : Word)
          (rs : List Addr32) (r : CasE.Ans e),
          step H (.vis e .pure) w' = (.running (.pure r), w'') →
            badState H (.vis (Sum.inl (Sum.inl e)) k) (w', rs)
              = (.running (k r), (w'', rs)))
      ∧ (∀ (b : Addr32) (kp : Unit → Prog WordedSig Unit) (w' : Word)
          (rs : List Addr32) (n : Node), Word.find w' b = some n →
          badState H (.vis (Sum.inl (Sum.inr (.publish b))) kp) (w', rs)
            = (.running (kp ()), (w', rs ++ [b])))
      ∧ (∀ (b : Addr32) (kp : Unit → Prog WordedSig Unit) (w' : Word)
          (rs : List Addr32), Word.find w' b = none →
          badState H (.vis (Sum.inl (Sum.inr (.publish b))) kp) (w', rs)
            = (.refused (.noObject b), (w', rs)))
      ∧ (∀ (kr : List Addr32 → Prog WordedSig Unit) (w' : Word) (rs : List Addr32),
          badState H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w', rs)
            = (.running (kr rs), (w', rs)))
      ∧ (∀ (mark : Nat) (ks : Word → Prog WordedSig Unit) (w' : Word)
          (rs : List Addr32),
          badState H (.vis (Sum.inr (.since mark)) ks) (w', rs)
            = (.running (ks (w'.drop mark)), (w', rs)))
      ∧ (∀ (p : Prog WordedSig Unit) (w' : Word) (rs : List Addr32),
          Word.wf w' = true → Word.wf (badState H p (w', rs)).2.1 = true))
    ∧ badState H (.vis (Sum.inl (Sum.inl (.fail "x")))
          (A := Unit) (fun e => e.elim)) (w, [a])
        ≠ stepWorded H (.vis (Sum.inl (Sum.inl (.fail "x")))
          (fun e => e.elim)) (w, [a]) :=
  ⟨⟨fun x s => badState_pure H x s,
    fun e k w' rs why => badState_hcasRef H e k w' rs why,
    fun e k w' w'' rs r h => badState_hcasAns H e k w' w'' rs r h,
    fun b kp w' rs _ hf => (badState_publish H b kp w' rs).1 _ hf,
    fun b kp w' rs hf => (badState_publish H b kp w' rs).2 hf,
    fun kr w' rs => badState_hroots H kr w' rs,
    fun mark ks w' rs => badState_hsince H mark ks w' rs,
    fun p _w' rs hw => badState_preserves_wf H p rs hw⟩,
   badState_differs H w a "x"⟩

/-! ## §4 — the necessity ladder covers 3 of 4 (C) conjuncts, and 2 of 3 (A) ones

`T004RW.lean:74`: "Each conjunct of (C) is therefore independently
load-bearing: drop any one and the corresponding adversary survives the whole
remaining set."

`worded_right_arms_project` has FOUR conjuncts and `stepWorded_unique` takes
them as four hypotheses (`hpubSome`, `hpubNone`, `hroots`, `hsince`). §5
exhibits three adversaries. `badPublish` (`T004RW.lean:562`) refuses correctly
on the unbound branch, so it violates `hpubSome` ONLY. No adversary in the file
violates `hpubNone` alone. `badPubNone` below is that rung.

Likewise §2 of the target asserts that (A)'s conjuncts 1 and 2 are "the halves
the dependency column does not deliver", but exhibits no counter-model showing
conjunct 1 is needed: all three of its adversaries satisfy (A) in full.
`badWhy` below is that rung — it satisfies `since_cas_agrees` and
`stepWorded_preserves_wf` verbatim, satisfies all four conjuncts of (C), and is
caught by `hcasRef` alone. -/

/-- ADVERSARY 5. `stepWorded` everywhere except on `CasE.fail`, where it
substitutes its own refusal reason. Caught by (A) conjunct 1 alone. -/
def badWhy {A : Type} (p : Prog WordedSig A) (s : Word × List Addr32) :
    Status WordedSig A × (Word × List Addr32) :=
  match p with
  | .vis (Sum.inl (Sum.inl (.fail _))) _ => (.refused (.failed "clobbered"), s)
  | _ => stepWorded H p s

/-- `badWhy` satisfies `since_cas_agrees` VERBATIM — a NAMED dependency of the
row, at (A) conjunct 3. -/
theorem badWhy_cas_agrees {A : Type} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badWhy H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) := by
  cases e with
  | fail reason => simp [badWhy, step]
  | put n => simpa [badWhy] using since_cas_agrees H (CasE.put n) k w roots
  | load a => simpa [badWhy] using since_cas_agrees H (CasE.load a) k w roots

/-- `badWhy` satisfies `stepWorded_preserves_wf` VERBATIM. -/
theorem badWhy_preserves_wf {A : Type} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badWhy H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl (.fail reason))) k => simpa [badWhy] using hw
  | .vis (Sum.inl (Sum.inl (.put n))) k =>
      simpa [badWhy] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl (CasE.put n))) k) roots hw
  | .vis (Sum.inl (Sum.inl (.load a))) k =>
      simpa [badWhy] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl (CasE.load a))) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      simpa [badWhy] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr (RootE.publish a))) k) roots hw
  | .vis (Sum.inl (Sum.inr .listRoots)) k =>
      simpa [badWhy] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr RootE.listRoots)) k) roots hw
  | .vis (Sum.inr (.since mark)) k =>
      simpa [badWhy] using stepWorded_preserves_wf H
        (.vis (Sum.inr (WordE.since mark)) k) roots hw

/-- `badWhy` satisfies (A) conjunct 2 — the answer half. -/
theorem badWhy_hcasAns {A : Type} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    badWhy H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) := by
  cases e with
  | fail reason => simp [step] at h
  | put n => simp [badWhy, stepWorded, stepRooted, h, Prog.inl, Prog.bind]
  | load a => simp [badWhy, stepWorded, stepRooted, h, Prog.inl, Prog.bind]

/-- `badWhy` satisfies ALL FOUR conjuncts of (C). -/
theorem badWhy_right_arms {A : Type} (mark : Nat) (a : Addr32)
    (ks : Word → Prog WordedSig A) (kr : List Addr32 → Prog WordedSig A)
    (kp : Unit → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badWhy H (.vis (Sum.inr (.since mark)) ks) (w, roots)
        = (.running (ks (w.drop mark)), (w, roots)))
      ∧ (badWhy H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
          = (.running (kr roots), (w, roots)))
      ∧ (∀ n, Word.find w a = some n →
          badWhy H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running (kp ()), (w, roots ++ [a])))
      ∧ (Word.find w a = none →
          badWhy H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.refused (.noObject a), (w, roots))) :=
  ⟨rfl, rfl,
   fun _ hf => by simp [badWhy, stepWorded, stepRooted, hf, Prog.inl, Prog.bind],
   fun hf => by simp [badWhy, stepWorded, stepRooted, hf]⟩

/-- The observable the refusal falsifiers read: the reason a `failed` refusal
carries. -/
def refusalReason {A : Type} :
    Status WordedSig A × (Word × List Addr32) → String
  | (.refused (.failed r), _) => r
  | _ => "«not a failed refusal»"

/-- **FALSIFIER 5.** `badWhy` is not `stepWorded`, and (A) conjunct 1 is the
only thing that sees it: the state agrees, the answer clause is vacuous on a
refusal, and every right arm projects correctly. -/
theorem badWhy_hcasRef_fails (w : Word) (roots : List Addr32) :
    ¬ ((badWhy H (.vis (Sum.inl (Sum.inl (.fail "boom")))
          (A := Unit) (fun e => e.elim)) (w, roots)).1 = .refused (.failed "boom")
        ↔ (step H (.vis (CasE.fail "boom") .pure) w).1 = .refused (.failed "boom")) := by
  intro h
  have hb : (Status.refused (Refusal.failed "clobbered") : Status WordedSig Unit)
      = .refused (.failed "boom") := h.mpr rfl
  have hr : "clobbered" = "boom" :=
    congrArg (fun st => refusalReason (A := Unit) (st, (w, roots))) hb
  exact absurd hr (by decide)

/-- ADVERSARY 6. `stepWorded` everywhere except on a publish of an UNBOUND
address, where it refuses with the wrong reason. Caught by (C)'s fourth
conjunct alone — the rung `T004RW.lean` §5 does not have. -/
def badPubNone {A : Type} (p : Prog WordedSig A) (s : Word × List Addr32) :
    Status WordedSig A × (Word × List Addr32) :=
  match p with
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      match Word.find s.1 a with
      | some _ => (.running (k ()), (s.1, s.2 ++ [a]))
      | none => (.refused (.failed "unbound"), s)
  | _ => stepWorded H p s

/-- `badPubNone` satisfies `since_cas_agrees` VERBATIM. -/
theorem badPubNone_cas_agrees {A : Type} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badPubNone H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) := by
  simpa [badPubNone] using since_cas_agrees H e k w roots

/-- `badPubNone` satisfies `stepWorded_preserves_wf` VERBATIM. -/
theorem badPubNone_preserves_wf {A : Type} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badPubNone H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl (Sum.inl e)) k =>
      simpa [badPubNone] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inl e)) k) roots hw
  | .vis (Sum.inl (Sum.inr (.publish a))) k =>
      cases hf : Word.find w a <;> simp [badPubNone, hf, hw]
  | .vis (Sum.inl (Sum.inr .listRoots)) k =>
      simpa [badPubNone] using stepWorded_preserves_wf H
        (.vis (Sum.inl (Sum.inr RootE.listRoots)) k) roots hw
  | .vis (Sum.inr (.since mark)) k =>
      simpa [badPubNone] using stepWorded_preserves_wf H
        (.vis (Sum.inr (WordE.since mark)) k) roots hw

/-- `badPubNone` satisfies (B), the worded publish guard — it still never
CONTINUES on an unbound address. -/
theorem badPubNone_publish_mem {A : Type} {a : Addr32}
    {kp : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : badPubNone H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none => simp [badPubNone, hf] at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-- `badPubNone` satisfies (A) in full, (C)'s `since`, (C)'s `listRoots`, and
(C)'s publish-ADMITTING half — every conjunct except the fourth. -/
theorem badPubNone_everything_else {A : Type} (e : CasE) (mark : Nat) (a : Addr32)
    (k : CasE.Ans e → Prog WordedSig A) (ks : Word → Prog WordedSig A)
    (kr : List Addr32 → Prog WordedSig A) (kp : Unit → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    (∀ why : Refusal,
        (badPubNone H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
          ↔ (step H (.vis e .pure) w).1 = .refused why)
      ∧ (∀ (r : CasE.Ans e) (w' : Word),
          step H (.vis e .pure) w = (.running (.pure r), w') →
            badPubNone H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
              = (.running (k r), (w', roots)))
      ∧ (badPubNone H (.vis (Sum.inr (.since mark)) ks) (w, roots)
          = (.running (ks (w.drop mark)), (w, roots)))
      ∧ (badPubNone H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)
          = (.running (kr roots), (w, roots)))
      ∧ (∀ n, Word.find w a = some n →
          badPubNone H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
            = (.running (kp ()), (w, roots ++ [a]))) :=
  ⟨fun why => by
      cases hs : step H (.vis e .pure) w with
      | mk st w' => cases st <;> simp [badPubNone, stepWorded, stepRooted, hs],
   fun r w' h => by simp [badPubNone, stepWorded, stepRooted, h, Prog.inl, Prog.bind],
   rfl, rfl,
   fun _ hf => by simp [badPubNone, hf]⟩

/-- **FALSIFIER 6.** `badPubNone` is not `stepWorded`: it refuses an unbound
publication with the wrong reason. `publish_refuses_unbound` — the fourth
conjunct of (C) — is the ONLY hypothesis that sees it, and `T004RW.lean` §5
exhibits no adversary against it. -/
theorem badPubNone_differs (a : Addr32) :
    badPubNone H (.vis (Sum.inl (Sum.inr (.publish a))) (A := Unit) .pure) ([], [])
      ≠ stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) .pure) ([], []) := by
  intro h
  have hr : "unbound" = "«not a failed refusal»" :=
    congrArg (refusalReason (A := Unit)) h
  exact absurd hr (by decide)

/-! ## §5 — `EC1-F87`: the extension arms cannot be flattened

`EC1-F87` (`CONTRACT-PACKET.md:747`) forbids flattening the `RootSig`/`WordSig`
extension arms. `T004RW.lean` claims compliance "by inspection of the
statement, not by a test". Here is the test.

If the arms could be flattened into one right-arm family, one uniform
projection law would cover them — every extension operation would answer from
the state and leave it alone, as `since` and `listRoots` do. `publish` refutes
that: it is a right arm that WRITES. So the three conjuncts of (C) are
genuinely three, the restatement's per-injection shape is forced, and F87 is
survived rather than merely asserted. -/

/-- The read-only arms DO preserve the state — the tempting uniform law. -/
theorem f87_read_arms_preserve_state {A : Type} (mark : Nat)
    (ks : Word → Prog WordedSig A) (kr : List Addr32 → Prog WordedSig A)
    (w : Word) (roots : List Addr32) :
    (stepWorded H (.vis (Sum.inr (.since mark)) ks) (w, roots)).2 = (w, roots)
      ∧ (stepWorded H (.vis (Sum.inl (Sum.inr .listRoots)) kr) (w, roots)).2
          = (w, roots) :=
  ⟨rfl, rfl⟩

/-- **`EC1-F87` EXERCISED.** No uniform right-arm projection law exists: the
publication arm writes. Flattening `RootSig` and `WordSig` into one extension
family therefore loses a distinction the interpreter makes, so the restated
row's per-injection (C) is forced and F87 is not tripped. -/
theorem f87_extension_arms_do_not_flatten (a : Addr32) (n : Node) :
    ¬ (∀ (A : Type) (op : WordedSig.Op) (k : WordedSig.Ans op → Prog WordedSig A)
        (w : Word) (roots : List Addr32),
        (stepWorded H (.vis op k) (w, roots)).2 = (w, roots)) := by
  intro h
  have := h Unit (Sum.inl (Sum.inr (.publish a))) (fun _ => .pure ())
    [Binding.mk a n] []
  simp [stepWorded, stepRooted, Word.find] at this

/-! ## §7 — half of (A) conjunct 1 is not load-bearing either

`T004RW.lean` §2 offers `stepWorded_cas_refuses_iff` as one of the two "halves
the dependency column does not deliver", and `stepWorded_unique` takes it as a
BICONDITIONAL (`hcasRef`). Only the ← direction is used: the proof reads
"the core refuses, therefore `f` refuses". The → direction ("`f` refuses only
if the core refuses") is never consumed.

Weakening `hcasRef` to that one implication leaves uniqueness intact, proved
below by re-running the target's own argument against the weaker hypothesis.
So the strengthened conjunct 1 is half decoration: what the characterization
needs is a one-directional import, not an iff. -/

/-- The target's `step_op_dichotomy`, restated locally (this file cannot import
`T004RW.lean` — it is not a module). -/
theorem step_op_dichotomy' (e : CasE) (w : Word) :
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
        | fresh a _ =>
          exact Or.inr ⟨a, w ++ [Binding.mk a n], by simp [step, dif_pos h, hc]⟩
        | duplicate a => exact Or.inr ⟨a, w, by simp [step, dif_pos h, hc]⟩
        | conflict a _ =>
          exact Or.inl ⟨Refusal.collision a, w, by simp [step, dif_pos h, hc]⟩
    · exact Or.inl ⟨.notWellFormed, w, by simp [step, dif_neg h]⟩
  | load a =>
    cases hf : Word.find w a with
    | none => exact Or.inl ⟨.noObject a, w, by simp [step, hf]⟩
    | some n => exact Or.inr ⟨n, w, by simp [step, hf]⟩
  | fail reason => exact Or.inl ⟨.failed reason, w, rfl⟩

/-- **UNIQUENESS SURVIVES A ONE-DIRECTIONAL `hcasRef`.** Identical to
`stepWorded_unique` except that conjunct 1 is weakened from an iff to the
single implication the target's own proof consumes. -/
theorem stepWorded_unique_weak_hcasRef {A : Type}
    (f : Prog WordedSig A → Word × List Addr32 →
      Status WordedSig A × (Word × List Addr32))
    (hpure : ∀ (a : A) (s : Word × List Addr32), f (.pure a) s = (.done a, s))
    (hcasRefBack : ∀ (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
        (roots : List Addr32) (why : Refusal),
        (step H (.vis e .pure) w).1 = .refused why →
          (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why)
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
  | .pure a, (w, roots) => hpure a (w, roots)
  | .vis (Sum.inl (Sum.inl e)) k, (w, roots) => by
      rcases step_op_dichotomy' H e w with ⟨why, w', hs⟩ | ⟨r, w', hs⟩
      · have h1 : (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why :=
          hcasRefBack e k w roots why (by rw [hs])
        have h2 : (f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2 = (w', roots) := by
          have := hcasSt e k w roots
          rw [hs] at this
          exact this
        have hpair : f (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
            = (.refused why, (w', roots)) := by
          cases hx : f (.vis (Sum.inl (Sum.inl e)) k) (w, roots) with
          | mk u v => rw [hx] at h1 h2; simp_all
        rw [hpair]
        simp [stepWorded, stepRooted, hs]
      · rw [hcasAns e k w w' roots r hs]
        simp [stepWorded, stepRooted, hs, Prog.inl, Prog.bind]
  | .vis (Sum.inl (Sum.inr (.publish a))) k, (w, roots) => by
      cases hfind : Word.find w a with
      | some n =>
        rw [hpubSome a k w roots n hfind]
        simp [stepWorded, stepRooted, hfind, Prog.inl, Prog.bind]
      | none =>
        rw [hpubNone a k w roots hfind]
        simp [stepWorded, stepRooted, hfind]
  | .vis (Sum.inl (Sum.inr .listRoots)) k, (w, roots) => hroots k w roots
  | .vis (Sum.inr (.since mark)) k, (w, roots) => hsince mark k w roots

/-! ## §6 — controls

Positive controls, so the attacks above are not mistaken for a claim that the
target's theorems are false. Everything `T004RW.lean` states about `stepWorded`
that this file re-derives, re-derives green. -/

/-- Control: the target's own (C)-publish-none conjunct holds of `stepWorded` —
`badPubNone` differs from `stepWorded`, not from the truth. -/
theorem control_publish_refuses_unbound {A : Type} (a : Addr32)
    (kp : Unit → Prog WordedSig A) (w : Word) (roots : List Addr32)
    (hf : Word.find w a = none) :
    stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) kp) (w, roots)
      = (.refused (.noObject a), (w, roots)) := by
  simp [stepWorded, stepRooted, hf]

/-- Control: `Word.find [] a = none`, so `hpubNone`'s premise is inhabited and
`badPubNone`'s falsifier is not vacuous. -/
theorem control_pubNone_premise_inhabited (a : Addr32) :
    Word.find [] a = none := rfl

/-- Control: the target's `stepWorded_unique` conclusion is not reachable from
(A) ∧ (B) alone — six adversaries now satisfy the row's two named dependencies
and are pairwise distinct from `stepWorded` for six different reasons. This
statement bundles the three this file adds. -/
theorem three_further_adversaries (w : Word) (a : Addr32) :
    (badState H (.vis (Sum.inl (Sum.inl (.fail "x"))) (A := Unit) (fun e => e.elim))
          (w, [a])
        ≠ stepWorded H (.vis (Sum.inl (Sum.inl (.fail "x"))) (fun e => e.elim)) (w, [a]))
      ∧ ((badWhy H (.vis (Sum.inl (Sum.inl (.fail "boom"))) (A := Unit)
            (fun e => e.elim)) (w, [a])).1
          ≠ (stepWorded H (.vis (Sum.inl (Sum.inl (.fail "boom"))) (fun e => e.elim))
            (w, [a])).1)
      ∧ (badPubNone H (.vis (Sum.inl (Sum.inr (.publish a))) (A := Unit) .pure) ([], [])
          ≠ stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) .pure) ([], [])) := by
  refine ⟨badState_differs H w a "x", ?_, badPubNone_differs H a⟩
  intro h
  have hr : "clobbered" = "boom" :=
    congrArg (fun st => refusalReason (A := Unit) (st, (w, [a]))) h
  exact absurd hr (by decide)

end Attack

end EC1T004RWAttack

/-! ## Receipts -/

#print axioms EC1T004RWAttack.wf_conjunct_follows_from_state_conjunct
#print axioms EC1T004RWAttack.guard_B_follows_from_C_publish
#print axioms EC1T004RWAttack.badState_pure
#print axioms EC1T004RWAttack.badState_hcasRef
#print axioms EC1T004RWAttack.badState_hcasAns
#print axioms EC1T004RWAttack.badState_publish
#print axioms EC1T004RWAttack.badState_hroots
#print axioms EC1T004RWAttack.badState_hsince
#print axioms EC1T004RWAttack.badState_preserves_wf
#print axioms EC1T004RWAttack.badState_publish_mem
#print axioms EC1T004RWAttack.badState_differs
#print axioms EC1T004RWAttack.since_cas_agrees_is_load_bearing
#print axioms EC1T004RWAttack.badWhy_cas_agrees
#print axioms EC1T004RWAttack.badWhy_preserves_wf
#print axioms EC1T004RWAttack.badWhy_hcasAns
#print axioms EC1T004RWAttack.badWhy_right_arms
#print axioms EC1T004RWAttack.badWhy_hcasRef_fails
#print axioms EC1T004RWAttack.badPubNone_cas_agrees
#print axioms EC1T004RWAttack.badPubNone_preserves_wf
#print axioms EC1T004RWAttack.badPubNone_publish_mem
#print axioms EC1T004RWAttack.badPubNone_everything_else
#print axioms EC1T004RWAttack.badPubNone_differs
#print axioms EC1T004RWAttack.f87_read_arms_preserve_state
#print axioms EC1T004RWAttack.f87_extension_arms_do_not_flatten
#print axioms EC1T004RWAttack.step_op_dichotomy'
#print axioms EC1T004RWAttack.stepWorded_unique_weak_hcasRef
#print axioms EC1T004RWAttack.control_publish_refuses_unbound
#print axioms EC1T004RWAttack.control_pubNone_premise_inhabited
#print axioms EC1T004RWAttack.three_further_adversaries
