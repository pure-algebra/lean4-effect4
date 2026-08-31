import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Lang.Interp

/-!
# `EC1-T004RW` scout probe — "remains imported" is three different laws, and one of them is missing

Row under scout (`../../PROOF-DAG.md:196`):

> `EC1-T004RW` PENDING THEOREM
> existing `RootSig`/`StoreSig` and `WordSig`/`WordedSig` CAS-agreement and
> WF-preservation laws remain imported under alphabet selection
> Depends on: `stepRooted_cas_agrees`, `since_cas_agrees`, corresponding
> preservation theorems

Stage: `lean-formalization-strategy` **Pass B** (declaration validation — the
row proposes a public obligation and the question is whether it can be
elaborated and frozen). Written 2026-08-31, Lean `leanprover/lean4:v4.33.1`,
against `library/cas` at the working tree.

Outside every lake target, exactly like `../exhibits.lean`,
`../counterexamples/Nondeterminism.lean`, `scout-T004.lean` and
`scout-T004S.lean`. Adds nothing to `Cas`, moves no byte, promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T004RW.lean
```

## What this file settles

`Alphabet`, `OpDesc` and `toSig` do not exist — every
`formal/effect-core-v1/EffectCore/Foundation/*.lean` is an empty stub, and
`grep -rn Alphabet library/cas/Cas` is empty. So the row cannot be elaborated
as written. What CAN be settled today is decided entirely by shipped library
facts, and it is settled here.

Seven findings, each with a kernel receipt at the foot. The one that decides
the row is §5b: **every law `EC1-T004RW` names is satisfied by an interpreter
that is wrong.**

1. §1 **Selection is definitional.** If `toSig` *returns* a shipped `Sig`, the
   shipped theorems apply through the projection with no transport at all —
   proved by handing the shipped theorem back verbatim. The "import" is `rfl`.
   That makes the row a tautology in exactly the sense `PROOF-DAG.md:207` used
   to delete two rows.
2. §2 **Reconstruction is not free, and the fold order is load-bearing.**
   `WordedSig` is *left*-associated by construction (`Worded.lean:57-58`). A
   table-driven alphabet that folds right produces an equivalent but not
   definitionally equal `Sig`. The transport is constructed here in four lines;
   the corpus contains none (`grep -rni "reindex\|Sig.map\|SigMorphism\|comap"`
   over `Cas/` is empty), and constructing it does not carry any interpreter
   law across.
3. §3 **The two named anchors are STATE-only.** Both are equations over the
   `.2` component, and `since_cas_agrees`' own docstring
   (`Worded.lean:129-133`) disclaims the rest: *"it does not say what status
   the step returns, and so it is not the claim that wording changes no Cas
   answer."* The status/answer halves are proved here, so the row's
   dependency column names strictly less than the row's name promises.
4. §4 **The root arm has no worded-level law.** `publish_mem`
   (`Roots.lean:111`) is stated at `stepRooted` and has no `stepWorded`
   counterpart. Under selection of `WordedSig` the publication guard is
   therefore NOT among the imported laws. Proved here; the omission is
   mechanical but real.
5. §5 **There are three shipped extension towers, not two, and the third is a
   different shape.** `AgentSig` (`Ops.lean:46`) is a shipped `Sig.sum` with
   NO step function, no `cas_agrees`, and no `_preserves_wf` of its own. Its
   route is eliminate-then-run (`Prog.handleLlm`, `runAgent`,
   `Interp.lean:184`/`:190`). Both a WF law and a CAS-agreement law are
   available for it — proved here — but they are a *program* equality and a
   `run`-level statement, not the state equation the other two towers carry.
   A single uniform "the laws remain imported" therefore has no referent.
6. §5b **THE FINDING. The imported set does not pin the extension.**
   `badStepWorded` delegates CAS exactly as `stepWorded` does, satisfies
   `since_cas_agrees` and `stepWorded_preserves_wf` *verbatim* — plus the
   strengthened §3 halves — and answers every `since` with the empty word.
   This is the estate's own `badAgentSum` argument
   (`Cas/Backend/SumAlgebra.lean:708`/`:721`/`:753`) instantiated at this row's
   carriers: left-arm agreement plus a store-level invariant is blind to the
   arm the selection ADDS. The row therefore needs a right-arm conjunct, and
   `stepRooted`'s root arm has none.
7. §6 the statement that does have content, assembled from §3–§5b.

## Axiom receipt

Every theorem carries a `#print axioms` line at the foot. Nothing here uses
`sorry`, `axiom`, `native_decide`, or `#eval`.
-/

namespace ScoutT004RW

open Cas.Lang
open Cas (Addr32 Binding Bytes Node Word)

/-! ## §1 — selection is definitional: the "import" is `rfl`

`CONTRACT-PACKET.md:88` fixes `Alphabet` as *metadata* indexed by an existing
`Cas.Lang.Sig.Op`; `ALGEBRA.md:167` fixes `Alphabet.toSig` as returning "this
existing semantic signature; it does not create a replacement handler
language". Under that reading `toSig` is a **selection**, and the scratch
carrier below is the whole of it — one field, no table, because a table would
change the question §2 asks.

The three theorems that follow are the shipped ones with `a.toSig` written in
place of the shipped signature. Each is proved by handing the shipped theorem
back unchanged: no `Eq.mpr`, no `▸`, no transport. That is the content of
"remains imported" in the selection reading, and it is nothing. -/

/-- THROWAWAY scratch carrier. It mints no signature: the field holds a
shipped `Sig` value. -/
structure SelectedAlphabet where
  toSig : Sig

/-- Selecting the rooted store language. -/
def rootedSelection : SelectedAlphabet := ⟨StoreSig⟩

/-- Selecting the worded store language. -/
def wordedSelection : SelectedAlphabet := ⟨WordedSig⟩

/-- `stepRooted_cas_agrees`, restated through the selection. The proof is the
shipped theorem applied — the statement is not a different proposition. -/
theorem selected_rooted_cas_agrees (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog rootedSelection.toSig A)
    (w : Word) (roots : List Addr32) :
    (stepRooted H (.vis (Sum.inl e) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) :=
  stepRooted_cas_agrees H e k w roots

/-- `since_cas_agrees`, restated through the selection. Same remark. -/
theorem selected_worded_cas_agrees (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog wordedSelection.toSig A)
    (w : Word) (roots : List Addr32) :
    (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) :=
  since_cas_agrees H e k w roots

/-- `stepWorded_preserves_wf`, restated through the selection. Same remark. -/
theorem selected_worded_preserves_wf (H : Bytes → Addr32) {A}
    (p : Prog wordedSelection.toSig A) {w : Word} (roots : List Addr32)
    (hw : Word.wf w = true) :
    Word.wf (stepWorded H p (w, roots)).2.1 = true :=
  stepWorded_preserves_wf H p roots hw

/-- The selection reading in one line: the alphabet's signature IS the shipped
signature, definitionally. There is no theorem here. -/
theorem selection_is_definitional :
    rootedSelection.toSig = StoreSig ∧ wordedSelection.toSig = WordedSig :=
  ⟨rfl, rfl⟩

/-! ## §2 — reconstruction: the fold order is load-bearing

`Worded.lean:57-58` records the association explicitly: "the sum parses as
`(CasSig ⊕ₛ RootSig) ⊕ₛ WordSig` (`⊕ₛ` is left-associative), which is
`StoreSig ⊕ₛ WordSig`". `stepWorded` matches on that exact shape.

A table-driven `toSig` — the natural reading of "the authored `Alphabet` is a
mapped subset" (`CONTRACT-PACKET.md:82`) — folds a list of arms. `List.foldr`
gives the RIGHT association. The two carry the same information and are not
the same `Sig`: `stepWorded` does not apply to the right-associated one, and
neither does any law proved about it.

The transport is constructible; it is written out below to price it. Note what
it does NOT do: it moves programs, and carries no interpreter, no state, and
no law. Every law the row wants to "import" would have to be re-proved through
a simulation on top of this. The corpus contains no such transport and no
signature morphism at all. -/

/-- The right-associated sum a `foldr`-built alphabet would produce. -/
def rightAssocSig : Sig := CasSig ⊕ₛ (RootSig ⊕ₛ WordSig)

/-- The shipped worded signature is left-associated, definitionally. -/
theorem worded_is_left_assoc :
    WordedSig = (CasSig ⊕ₛ RootSig) ⊕ₛ WordSig := rfl

/-- The transport, four lines, constructed here because the corpus has none.
Each arm's answer type matches definitionally, which is why no `▸` appears. -/
def reassoc {A} : Prog rightAssocSig A → Prog WordedSig A
  | .pure a => .pure a
  | .vis (Sum.inl e) k => .vis (Sum.inl (Sum.inl e)) fun r => reassoc (k r)
  | .vis (Sum.inr (Sum.inl e)) k => .vis (Sum.inl (Sum.inr e)) fun r => reassoc (k r)
  | .vis (Sum.inr (Sum.inr e)) k => .vis (Sum.inr e) fun r => reassoc (k r)

/-- The transport is not the identity dressed up: it is a genuine relabelling,
witnessed on one operation of each arm. These are `rfl`, and that is the
point — the *data* moves for free, and nothing else does. -/
theorem reassoc_relabels (a : Addr32) (n : Node) (m : Nat) :
    reassoc (A := Unit) (.vis (Sum.inr (Sum.inl (.publish a))) .pure)
        = .vis (Sum.inl (Sum.inr (.publish a))) .pure
      ∧ reassoc (A := Word) (.vis (Sum.inr (Sum.inr (.since m))) .pure)
        = .vis (Sum.inr (.since m)) .pure
      ∧ reassoc (A := Addr32) (.vis (Sum.inl (.put n)) .pure)
        = .vis (Sum.inl (Sum.inl (.put n))) .pure :=
  ⟨rfl, rfl, rfl⟩

/-! ## §3 — the two named anchors are STATE-only; here are the halves they omit

`stepRooted_cas_agrees` (`Roots.lean:85`) and `since_cas_agrees`
(`Worded.lean:134`) are both equations over the `.2` component of the step's
result — the state. Neither says anything about the `.1` component, so neither
says that a CAS operation *answers* the same thing inside the extension. The
estate says so itself at `Worded.lean:129-133`.

If `EC1-T004RW` means "CAS operations behave the same under alphabet
selection", the two theorems it names do not carry that. The missing halves
are below. They are TRUE, and they are not in the corpus. -/

/-- Refusal transfers exactly, at the rooted tower: the extension refuses on a
CAS operation exactly when `step` does, with the same refusal. -/
theorem stepRooted_cas_refuses_iff (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog StoreSig A) (w : Word) (roots : List Addr32)
    (why : Refusal) :
    (stepRooted H (.vis (Sum.inl e) k) (w, roots)).1 = .refused why
      ↔ (step H (.vis e .pure) w).1 = .refused why := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [stepRooted, hs]

/-- The answer transfers exactly, at the rooted tower: when `step` answers `r`,
the extension binds the waiting continuation to that same `r`. This is the
half `stepRooted_cas_agrees` does not state. -/
theorem stepRooted_cas_answers (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog StoreSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    stepRooted H (.vis (Sum.inl e) k) (w, roots) = (.running (k r), (w', roots)) := by
  simp [stepRooted, h, Prog.inl, Prog.bind]

/-- Refusal transfers exactly, at the worded tower — through two injections. -/
theorem stepWorded_cas_refuses_iff (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32)
    (why : Refusal) :
    (stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).1 = .refused why
      ↔ (step H (.vis e .pure) w).1 = .refused why := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [stepWorded, stepRooted, hs]

/-- The answer transfers exactly, at the worded tower. This is the half
`since_cas_agrees` explicitly declines to state. -/
theorem stepWorded_cas_answers (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    stepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) := by
  simp [stepWorded, stepRooted, h, Prog.inl, Prog.bind]

/-- NON-VACUITY of the answer clause. `.running (.pure r)` is the shape a
successful CAS operation actually leaves — witnessed concretely on `load`, at
every address function, so the premise of `stepRooted_cas_answers` and
`stepWorded_cas_answers` is inhabited and those theorems are not hollow. -/
theorem answer_premise_is_inhabited (H : Bytes → Addr32) (a : Addr32) (n : Node) :
    step H (.vis (.load a) .pure) [Binding.mk a n] = (.running (.pure n), [Binding.mk a n]) := by
  simp [step, Word.find]

/-- NON-VACUITY of the refusal clause: `.fail` refuses at every word. -/
theorem refusal_premise_is_inhabited (H : Bytes → Addr32) (w : Word) (reason : String) :
    (step H (.vis (.fail reason) (fun e => e.elim) : Prog CasSig Addr32) w).1
      = .refused (.failed reason) := rfl

/-! ## §4 — the root arm has no worded-level law

`publish_mem` (`Roots.lean:111`) is the fail-closed guard read back: a
successful publish's address is bound in the word. It is stated at
`stepRooted` only. Selecting `WordedSig` puts the root arm one injection
deeper and the theorem no longer applies to the program you actually have.

The worded restatement is proved here. It is mechanical, and its absence is a
gap in the set the row calls "the existing laws". -/

/-- `publish_mem` at the worded tower: a publish that continues had its
address bound in the word. Not in the corpus. -/
theorem publish_mem_worded (H : Bytes → Addr32) {A} {a : Addr32}
    {k : Unit → Prog WordedSig A} {w : Word} {roots : List Addr32}
    {rest : Prog WordedSig A} {s' : Word × List Addr32}
    (h : stepWorded H (.vis (Sum.inl (Sum.inr (.publish a))) k) (w, roots)
        = (.running rest, s')) :
    ∃ n, Binding.mk a n ∈ w := by
  cases hf : Word.find w a with
  | none => simp [stepWorded, stepRooted, hf] at h
  | some n => exact ⟨n, Word.find_mem hf⟩

/-! ## §5 — there are three shipped towers, and the third is a different shape

`AgentSig := CasSig ⊕ₛ LlmSig` (`Ops.lean:46`) is a shipped signature sum on
the same footing as `StoreSig` and `WordedSig`. It has:

* no `stepAgent` — `grep -rn "^def step" Cas/` returns exactly `step`
  (`Interp.lean:70`), `stepRooted` (`Roots.lean:69`), `stepWorded`
  (`Worded.lean:97`);
* no `agent_cas_agrees`;
* no `stepAgent_preserves_wf`.

Its route is *eliminate-then-run*: `Prog.handleLlm` folds the oracle's answers
in and leaves a `Prog CasSig`, which `runAgent` hands to `run`
(`Interp.lean:184`, `:190`). Both laws ARE available for it — below — but they
are a **program equality** and a **`run`-level** statement. Neither is the
state equation `stepRooted_cas_agrees`/`since_cas_agrees` carry.

So "the existing CAS-agreement and WF-preservation laws" is not one family
with one import. It is three shapes across three towers, and a row quantified
over "alphabet selection" has to say which. -/

/-- The agent tower's CAS agreement is a PROGRAM equality, not a state
equation: handling the LLM arm leaves the CAS operation exactly where it was.
`rfl` — and that is a different kind of fact from §3. Not in the corpus. -/
theorem handleLlm_cas_agrees (oracle : String → String) {A} (e : CasE)
    (k : CasE.Ans e → Prog AgentSig A) :
    Prog.handleLlm oracle (.vis (Sum.inl e) k)
      = .vis e (fun r => Prog.handleLlm oracle (k r)) := rfl

/-- The agent tower's WF preservation, at `run` rather than at a step, because
there is no agent step to state it at. Not in the corpus. -/
theorem runAgent_preserves_wf (H : Bytes → Addr32) (oracle : String → String)
    (fuel : Nat) {A} (p : Prog AgentSig A) {w : Word}
    (hw : Word.wf w = true) :
    Word.wf (runAgent H oracle fuel p w).2 = true :=
  run_preserves_wf H fuel (p.handleLlm oracle) hw

/-! ## §5b — the imported set does not pin the extension

This is the finding that decides the row, and the estate got there first.

`Cas/Backend/SumAlgebra.lean` §"Adversary 2" builds `badAgentSum` (`:708`), a
handler on `AgentSig` that answers every `infer` with `""`. It satisfies the
left-arm projection (`:714` `badAgentSum_handle_inl`) and the full left-arm
adequacy law (`:721` `badAgentSum_interpret_inl` — "every store-only program is
interpreted exactly right, which is the whole reason no run gate catches it"),
and only the RIGHT-arm projection separates it from the truth (`:753`
`badAgentSum_not_interpret_inr`). The module's own prose: *"the word gate is
blind by construction — a `CasSig`-only program cannot tell the difference."*
`badHandleLlm` (`:992`) repeats it one level up: it satisfies
`badHandleLlm_liftCas` (`:999`) in full and is still wrong (`:1007`
`badHandleLlm_differs`).

`EC1-T004RW` proposes to import exactly the left-arm shape — CAS agreement plus
a store-level invariant — as its non-disturbance evidence. The adversary below
is that argument instantiated at the row's own carriers: a worded step function
that delegates CAS *identically to `stepWorded`*, satisfies both named anchors
verbatim, preserves word admission, and answers every `since` with the empty
word. Every law `EC1-T004RW` names holds of it. It is wrong.

So the row, even fully discharged, establishes nothing about the arm the
alphabet selection ADDS.

**The repair is cheap and the estate already shipped half of it.** The law that
catches this adversary is `since_suffix` (`Worded.lean:110`) — the right-arm
projection for `since` — and the row's dependency column does not name it.
`since_zero`/`since_next`/`since_compose` (`:119`/`:163`/`:176`) complete that
arm. What is genuinely missing is the ROOT arm's projection: `publish_mem`
(`Roots.lean:111`) is a one-directional guard stated only at `stepRooted`
(§4 supplies the worded restatement), and `listRoots` has no law at either
depth. So `EC1-T004RW` should name the right-arm projections, not the
CAS-agreement pair. -/

/-- ADVERSARY: delegates store operations exactly as `stepWorded` does, and
answers every `since` with the empty word. -/
def badStepWorded (H : Bytes → Addr32) {A : Type} :
    Prog WordedSig A → Word × List Addr32 →
    Status WordedSig A × (Word × List Addr32)
  | .pure a, s => (.done a, s)
  | .vis (Sum.inl e) k, s =>
    match stepRooted H (.vis e .pure) s with
    | (.running rest, s') => (.running (rest.inl.bind k), s')
    | (.done r, s') => (.running (k r), s')
    | (.refused why, s') => (.refused why, s')
  | .vis (Sum.inr (.since _)) k, (w, roots) => (.running (k []), (w, roots))

/-- The adversary satisfies `since_cas_agrees` VERBATIM — same statement, same
quantifiers, one of the two theorems `EC1-T004RW` names. -/
theorem bad_since_cas_agrees (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w : Word) (roots : List Addr32) :
    (badStepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)).2
      = ((step H (.vis e .pure) w).2, roots) := by
  cases hs : step H (.vis e .pure) w with
  | mk st w' => cases st <;> simp [badStepWorded, stepRooted, hs]

/-- The adversary satisfies `stepWorded_preserves_wf` VERBATIM — the other
theorem `EC1-T004RW` names. -/
theorem bad_preserves_wf (H : Bytes → Addr32) {A} (p : Prog WordedSig A)
    {w : Word} (roots : List Addr32) (hw : Word.wf w = true) :
    Word.wf (badStepWorded H p (w, roots)).2.1 = true := by
  match p with
  | .pure a => exact hw
  | .vis (Sum.inl e) k =>
    have h := stepRooted_preserves_wf H (.vis e .pure) roots hw
    cases hs : stepRooted H (.vis e .pure) (w, roots) with
    | mk st s' =>
      rw [hs] at h
      cases st <;> simpa [badStepWorded, hs] using h
  | .vis (Sum.inr (.since mark)) k => exact hw

/-- The adversary also satisfies the §3 status/answer halves on the CAS arm —
so strengthening the CAS-agreement law does not catch it either. -/
theorem bad_cas_answers (H : Bytes → Addr32) {A} (e : CasE)
    (k : CasE.Ans e → Prog WordedSig A) (w w' : Word) (roots : List Addr32)
    (r : CasE.Ans e)
    (h : step H (.vis e .pure) w = (.running (.pure r), w')) :
    badStepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, roots)
      = (.running (k r), (w', roots)) := by
  simp [badStepWorded, stepRooted, h, Prog.inl, Prog.bind]

/-- The observable the falsifier reads: the word a continuing `since` binds. -/
def answerOf : Status WordedSig Word × (Word × List Addr32) → Word
  | (.running (.pure v), _) => v
  | _ => []

/-- **The falsifier.** The adversary is not `stepWorded`: at a one-binding word
it reports that nothing has ever happened. Concrete, at every `H`. Both sides
reduce definitionally, so `congrArg` alone carries the inequality. -/
theorem bad_differs (H : Bytes → Addr32) (a : Addr32) (n : Node)
    (roots : List Addr32) :
    badStepWorded H (.vis (Sum.inr (.since 0)) .pure) ([Binding.mk a n], roots)
      ≠ stepWorded H (.vis (Sum.inr (.since 0)) .pure) ([Binding.mk a n], roots) := by
  intro h
  have h1 : ([] : Word) = [Binding.mk a n] := congrArg answerOf h
  exact absurd h1 (by simp)

/-- **`EC1-T004RW` does not pin the extension**, in the estate's own
`badAgentSum` shape: one interpreter satisfies every law the row names —
both anchors verbatim, plus the strengthened §3 halves — and is still wrong on
the operation the selection added. -/
theorem imported_laws_do_not_pin_the_extension (H : Bytes → Addr32)
    (a : Addr32) (n : Node) (roots : List Addr32) :
    (∀ {A} (e : CasE) (k : CasE.Ans e → Prog WordedSig A) (w : Word)
        (rs : List Addr32),
        (badStepWorded H (.vis (Sum.inl (Sum.inl e)) k) (w, rs)).2
          = ((step H (.vis e .pure) w).2, rs))
      ∧ (∀ {A} (p : Prog WordedSig A) (w : Word) (rs : List Addr32),
          Word.wf w = true →
            Word.wf (badStepWorded H p (w, rs)).2.1 = true)
      ∧ badStepWorded H (.vis (Sum.inr (.since 0)) (A := Word) .pure)
            ([Binding.mk a n], roots)
          ≠ stepWorded H (.vis (Sum.inr (.since 0)) .pure) ([Binding.mk a n], roots) :=
  ⟨fun e k w rs => bad_since_cas_agrees H e k w rs,
   fun p _w rs hw => bad_preserves_wf H p rs hw,
   bad_differs H a n roots⟩

/-! ## §6 — the statement with content

Assembled from §3–§5, and stated where it can actually be proved: about the
shipped towers, with no `Alphabet` carrier required. This is the row an
IMPORT/REUSE obligation should carry — it is dischargeable today, and every
conjunct is a fact the corpus does not currently record.

It deliberately does NOT quantify over "alphabet selection": §1 shows that
quantifier is either vacuous (selection) or unstatable (reconstruction, §2). -/

/-- **The recommended `EC1-T004RW`.** For the worded tower — the deepest
shipped selection — a CAS operation refuses exactly when the core refuses,
answers exactly what the core answers, leaves the word exactly where the core
leaves it, leaves the roots untouched, preserves admission, and the root arm's
fail-closed guard survives at this depth. -/
theorem worded_selection_imports_the_core (H : Bytes → Addr32) {A} (e : CasE)
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

/-! ## Receipts -/

#print axioms selected_rooted_cas_agrees
#print axioms selected_worded_cas_agrees
#print axioms selected_worded_preserves_wf
#print axioms selection_is_definitional
#print axioms worded_is_left_assoc
#print axioms reassoc_relabels
#print axioms stepRooted_cas_refuses_iff
#print axioms stepRooted_cas_answers
#print axioms stepWorded_cas_refuses_iff
#print axioms stepWorded_cas_answers
#print axioms answer_premise_is_inhabited
#print axioms refusal_premise_is_inhabited
#print axioms publish_mem_worded
#print axioms handleLlm_cas_agrees
#print axioms runAgent_preserves_wf
#print axioms bad_since_cas_agrees
#print axioms bad_preserves_wf
#print axioms bad_cas_answers
#print axioms bad_differs
#print axioms imported_laws_do_not_pin_the_extension
#print axioms worded_selection_imports_the_core

end ScoutT004RW
