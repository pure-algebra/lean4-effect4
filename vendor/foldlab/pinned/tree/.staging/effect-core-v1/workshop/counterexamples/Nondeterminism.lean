import Cas.Lang.Wp
import Cas.Lang.Tower

/-!
# `EC1-CE042` — the denotation is not a function of the program alone

The register row this file discharges (`../../COUNTEREXAMPLES.md` §7):

> **`EC1-CE042`** — "Full Effect Core has a globally unique denotation without
> fixing choices." Required witness: one admitted program with two typed
> decision/schedule streams and two permitted observations.

Written 2026-08-31 against `56a938fe` plus the working tree, Lean
`leanprover/lean4:v4.33.1`. Stage: `lean-algebraic-systems`
(`.claude/skills/lean/workflows/`). Outside every lake target, exactly like
`FixedFuel.lean`, `LocalAnchors.lean`, `../exhibits.lean` and
`../../breaker-exhibits.lean`. It adds nothing to `Cas`, moves no byte, and
promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/Nondeterminism.lean
```

## What is under attack, exactly

`../exhibits.lean` proves `denotes_unique`: for the CAS/block graph language
under a fixed address function, `Denotes` is a partial function. That theorem
is TRUE and is not touched here. `EXHIBITS-REVIEW.md` §3 X1 already records why
it does not generalize — the graph language "contains no handler-answer choice,
external request, scheduler choice, clock/random choice, fork, race, or
competing finalization". X1 states that as an ARGUMENT. This file replaces the
argument with a witness: it exhibits one program in a language that has exactly
ONE of those sources, and shows the uniqueness statement is false there.

The claim defeated is therefore the UNIVERSAL one, not an inequality between
two runs:

```text
∀ p w o₁ o₂, Denotes H p w o₁ → Denotes H p w o₂ → o₁ = o₂
```

and, in the sharper "no such function" form the estate already uses for
`run_has_no_composition_law` (`Cas/Backend/Universal.lean` §8):

```text
∃ f, ∀ p w d o, Runs H p w d o → o = f p w
```

Both are refuted below, for EVERY address function `H`.

| § | Content |
|---|---|
| 1 | decision alphabet, tape, and the observation mask |
| 2 | the decision-indexed executable interpreter |
| 3 | the relational semantics `Runs` / `Denotes` |
| 4 | adequacy: the two agree |
| 5 | `denotes_unique_given` — fixing the tape restores determinism |
| 5b | the ask-free fragment is unique with NOTHING fixed |
| 6 | the witness: one program, two tapes, two observations |
| 7 | **`EC1-CE042`** — two forms of the refutation |
| 8 | the same phenomenon at the shipped `AgentSig`, conditional on `EC1-XT012` |

## The decision source modelled, and the ones NOT modelled

`EXHIBITS-REVIEW.md` §4.1 enumerates eight decision sources. This file models
exactly ONE — **direct-handler answer**, "one `Step` branch per admitted
answer/outcome | typed answer token" — as one operation `ask` whose answer the
fixed store handler does not determine, summed onto `CasSig` with the estate's
own `⊕ₛ`.

NOT modelled here, and NOT claimed by any theorem below: registered foreign
reply as a symbolic request frontier, scheduler choice, race tie, clock/random
sampling, interruption arrival, and replay token selection. §8 does exhibit the
same phenomenon at the estate's SHIPPED registered-foreign-reply operation
(`LlmE.infer` and `Prog.handleLlm`), but that is a second instance of the same
source pattern, not a second source.

One source is all the row needs: a universal statement falls to one witness.

## What this file does NOT claim

- It does NOT claim the relational semantics below is Effect Core's semantics.
  `Runs` here is a four-constructor judgment over EXISTING carriers, built to
  be the smallest thing that can carry the counterexample.
- It does NOT weaken `denotes_unique`. §5 proves the POSITIVE companion —
  fixing the decision tape restores determinism — so the row cannot be read as
  forbidding the replay theorem the packet needs. §5b proves the stronger
  specialization: on the ask-free fragment the observation is unique with
  NOTHING fixed, which is where `../exhibits.lean`'s theorem lives.
- It says nothing about fairness, liveness, or any schedule. `Tape` is one
  decision stream, not a policy, and no theorem quantifies over schedules.
- It does not establish that a decision-INDEXED denotation exists for Effect
  Core generally. `runTape` is total only because `Prog` is finite; loops,
  external frontiers, and forks are outside it.
- It does not claim `AgentSig` is admitted into Effect Core v1's alphabet.
  `EXISTING-TYPES.md` `EC1-XT012` leaves that an explicit versioned decision,
  so §8 is CONDITIONAL on it and §1–§7 are not.
- No `sorry`, no `axiom`, no `native_decide`, no `Classical.choice`. Every
  theorem is receipted at the foot.
-/

namespace EffectCoreNondet

open Cas.Lang
open Cas (Bytes Addr32 Node Word Binding)

/-! ## §1 — the decision alphabet, the tape, and the observation

Three carriers, none of them new semantic machinery: an operation whose answer
is a typed token, the stream of those tokens, and `interpretRef`'s own
codomain as the observation. -/

/-- The decision language: ONE operation. Its answer is not computed from the
store, so the fixed reference handler cannot supply it. -/
inductive DecE where
  | ask
  deriving DecidableEq

/-- The typed decision token. `Bool` is the smallest answer type with two
inhabitants; nothing below depends on it being `Bool` rather than a richer
typed answer. -/
abbrev DecE.Ans : DecE → Type
  | .ask => Bool

/-- The decision signature. -/
def DecSig : Sig := ⟨DecE, DecE.Ans⟩

/-- The core under test: the store language plus one undetermined answer,
composed by the estate's own signature sum (`Sig.sum`, `Sig.lean`). No new
program carrier — `Prog CoreSig` is `Cas.Lang.Prog` at a summed signature,
exactly as `AgentSig` is. -/
def CoreSig : Sig := CasSig ⊕ₛ DecSig

/-- A complete typed decision tape: the answers, in request order. -/
abbrev Tape := List Bool

/-- The permitted observation. This is `interpretRef`'s codomain VERBATIM
(`Cas/Lang/Handler.lean`): value and final word on success, the refusal ALONE
on failure. The refusal-side partial word is deliberately outside the mask —
that is the existing ruling `EC1-CE010`, and inventing a finer observation here
would make the counterexample easier and therefore worthless. -/
abbrev Obs (A : Type) := Except Refusal (A × Word)

/-! ## §2 — the decision-indexed executable interpreter

The store side is not re-derived: every CAS clause is `referenceHandler`'s,
called. Only the `ask` clause is new, and it reads the tape.

`casClause` exists so that each `runTape` equation is `rfl`; it is the reference
handler's own outcome match, nothing more. -/

/-- One store operation, as a continuation-passing clause of the EXISTING
reference handler. -/
def casClause (H : Bytes → Addr32) {A : Type} (op : CasE) (w : Word)
    (cont : CasE.Ans op → Word → Option (Obs A)) : Option (Obs A) :=
  match (referenceHandler H).handle op w with
  | .ok (ans, w') => cont ans w'
  | .error r => some (.error r)

/-- The decision-indexed run. Total and fuel-free — `Prog` is finite, so this
is structural recursion, the same reason `interpret` needs no fuel.

`none` is the DECISION FRONTIER of `EXHIBITS-REVIEW.md` §4.2: the tape did not
supply an answer the program asked for, so there is no observation at all. It is
not a refusal, and §6 exhibits it. -/
def runTape (H : Bytes → Addr32) {A : Type} :
    Prog CoreSig A → Word → Tape → Option (Obs A)
  | .pure a, w, _ => some (.ok (a, w))
  | .vis (Sum.inl op) k, w, d => casClause H op w (fun ans w' => runTape H (k ans) w' d)
  | .vis (Sum.inr .ask) _, _, [] => none
  | .vis (Sum.inr .ask) k, w, b :: d => runTape H (k b) w d

section Equations
variable (H : Bytes → Addr32) {A : Type}

theorem casClause_ok {op : CasE} {w w' : Word} {ans : CasE.Ans op}
    (cont : CasE.Ans op → Word → Option (Obs A))
    (h : (referenceHandler H).handle op w = .ok (ans, w')) :
    casClause H op w cont = cont ans w' := by
  unfold casClause; rw [h]

theorem casClause_error {op : CasE} {w : Word} {r : Refusal}
    (cont : CasE.Ans op → Word → Option (Obs A))
    (h : (referenceHandler H).handle op w = .error r) :
    casClause H op w cont = some (.error r) := by
  unfold casClause; rw [h]

theorem runTape_pure (a : A) (w : Word) (d : Tape) :
    runTape H (.pure a) w d = some (.ok (a, w)) := rfl

theorem runTape_cas (op : CasE) (k : CasE.Ans op → Prog CoreSig A) (w : Word)
    (d : Tape) :
    runTape H (.vis (Sum.inl op) k) w d
      = casClause H op w (fun ans w' => runTape H (k ans) w' d) := rfl

theorem runTape_ask_nil (k : Bool → Prog CoreSig A) (w : Word) :
    runTape H (.vis (Sum.inr .ask) k) w [] = none := rfl

theorem runTape_ask_cons (k : Bool → Prog CoreSig A) (w : Word) (b : Bool)
    (d : Tape) :
    runTape H (.vis (Sum.inr .ask) k) w (b :: d) = runTape H (k b) w d := rfl

end Equations

/-! ## §3 — the relational semantics

The public shape `EXHIBITS-REVIEW.md` §3 X1 selects:

```text
Runs p initial decisions observation : Prop
Denotes p initial observation := ∃ decisions, Runs p initial decisions observation
```

Four constructors. Three of them are the reference handler, read off; the
fourth is the only place a choice enters, and it is LABELLED by the token it
consumed — "every relational branch has a label" (§4.1). -/

/-- The judgment. `Runs H p w d o` reads: from word `w`, consuming the decision
tape `d`, program `p` is permitted to produce observation `o`. -/
inductive Runs (H : Bytes → Addr32) :
    {A : Type} → Prog CoreSig A → Word → Tape → Obs A → Prop
  | halt {A : Type} {a : A} {w : Word} {d : Tape} :
      Runs H (.pure a) w d (.ok (a, w))
  | cas {A : Type} {op : CasE} {k : CasE.Ans op → Prog CoreSig A}
      {w w' : Word} {ans : CasE.Ans op} {d : Tape} {o : Obs A} :
      (referenceHandler H).handle op w = .ok (ans, w') →
      Runs H (k ans) w' d o →
      Runs H (.vis (Sum.inl op) k) w d o
  | refuse {A : Type} {op : CasE} {k : CasE.Ans op → Prog CoreSig A}
      {w : Word} {d : Tape} {r : Refusal} :
      (referenceHandler H).handle op w = .error r →
      Runs H (.vis (Sum.inl op) k) w d (.error r : Obs A)
  | choose {A : Type} {k : Bool → Prog CoreSig A}
      {w : Word} {b : Bool} {d : Tape} {o : Obs A} :
      Runs H (k b) w d o →
      Runs H (.vis (Sum.inr .ask) k) w (b :: d) o

/-- The denotation: the observations the program is permitted to produce when
the decisions are NOT fixed. This is the statement `EC1-CE042` attacks. -/
def Denotes (H : Bytes → Addr32) {A : Type} (p : Prog CoreSig A) (w : Word)
    (o : Obs A) : Prop :=
  ∃ d : Tape, Runs H p w d o

/-! ## §4 — adequacy: the relation and the executable run are one semantics

The stage's `refinement/adequacy theorem shape naming observable behavior`.
Everything after this point is a corollary of `runs_iff`. -/

section Adequacy
variable (H : Bytes → Addr32) {A : Type}

/-- Every permitted run is computed by the executable interpreter. -/
theorem runs_sound {p : Prog CoreSig A} {w : Word} {d : Tape} {o : Obs A}
    (h : Runs H p w d o) : runTape H p w d = some o := by
  induction h with
  | halt => rfl
  | cas hop _ ih => rw [runTape_cas, casClause_ok _ _ hop]; exact ih
  | refuse hop => rw [runTape_cas, casClause_error _ _ hop]
  | choose _ ih => rw [runTape_ask_cons]; exact ih

/-- Everything the executable interpreter computes is a permitted run. -/
theorem runs_complete (p : Prog CoreSig A) :
    ∀ (w : Word) (d : Tape) (o : Obs A), runTape H p w d = some o → Runs H p w d o := by
  induction p with
  | pure a =>
    intro w d o h
    have h' : (some (.ok (a, w)) : Option (Obs A)) = some o :=
      (runTape_pure H a w d).symm.trans h
    rw [← Option.some.inj h']
    exact .halt
  | vis op k ih =>
    match op with
    | Sum.inl casOp =>
      intro w d o h
      have h' : casClause H casOp w (fun ans w' => runTape H (k ans) w' d) = some o :=
        (runTape_cas H casOp k w d).symm.trans h
      cases hh : (referenceHandler H).handle casOp w with
      | ok aw =>
        obtain ⟨ans, w'⟩ := aw
        rw [casClause_ok _ _ hh] at h'
        exact .cas hh (ih ans w' d o h')
      | error r =>
        rw [casClause_error _ _ hh] at h'
        rw [← Option.some.inj h']
        exact .refuse hh
    | Sum.inr .ask =>
      intro w d o h
      match d with
      | [] =>
        have h' : (none : Option (Obs A)) = some o :=
          (runTape_ask_nil H k w).symm.trans h
        exact absurd h' (by simp)
      | b :: d' =>
        have h' : runTape H (k b) w d' = some o :=
          (runTape_ask_cons H k w b d').symm.trans h
        exact .choose (ih b w d' o h')

/-- **ADEQUACY.** The relational judgment and the executable decision-indexed
interpreter decide the same observations. -/
theorem runs_iff (p : Prog CoreSig A) (w : Word) (d : Tape) (o : Obs A) :
    Runs H p w d o ↔ runTape H p w d = some o :=
  ⟨runs_sound H, runs_complete H p w d o⟩

end Adequacy

/-! ## §5 — the POSITIVE companion: `denotes_unique_given`

Stated FIRST, before the counterexample, because a row that proves too much is
a bad row. `EC1-CE042` must not forbid replay. It does not: fixing the tape
restores exactly the determinism `EXHIBITS-REVIEW.md` §4.3 asks for —

```text
fixed initial configuration + one complete typed decision tape
  -> executable replay is deterministic
```

Note what is fixed and what is not. `H`, `w` and `d` are fixed; the program is
arbitrary; the tape is one tape, not a policy. -/

section Determinism
variable (H : Bytes → Addr32) {A : Type}

/-- **`denotes_unique_given`.** Under one fixed decision tape the observation is
unique — the relational semantics is a partial FUNCTION of
`(program, word, tape)`. -/
theorem denotes_unique_given {p : Prog CoreSig A} {w : Word} {d : Tape}
    {o₁ o₂ : Obs A} (h₁ : Runs H p w d o₁) (h₂ : Runs H p w d o₂) : o₁ = o₂ :=
  Option.some.inj ((runs_sound H h₁).symm.trans (runs_sound H h₂))

/-- The same fact as the replay statement: a fixed tape names a total function
of the program and the word, wherever an observation exists at all. -/
theorem replay_is_a_function (d : Tape) :
    ∃ f : Prog CoreSig A → Word → Option (Obs A),
      ∀ (p : Prog CoreSig A) (w : Word) (o : Obs A),
        Runs H p w d o ↔ f p w = some o :=
  ⟨fun p w => runTape H p w d, fun p w o => runs_iff H p w d o⟩

/-! ### §5b — the fragment on which uniqueness survives WITHOUT fixing anything

`EXHIBITS-REVIEW.md` §4.3: "The admissible theorems are `denotes_unique_given`
under fixed decisions and the stronger deterministic CAS specialization." §5 is
the first; this is the second, and together they fence the counterexample in.

The fence matters: without it `EC1-CE042` would read as "CAS programs have no
unique denotation either", which is false and would contradict `denotes_unique`.
The decision source is the ONLY thing that breaks uniqueness here. -/

/-- The deterministic fragment: a program that never asks. -/
inductive AskFree {A : Type} : Prog CoreSig A → Prop
  | pure (a : A) : AskFree (.pure a)
  | cas {op : CasE} {k : CasE.Ans op → Prog CoreSig A} :
      (∀ ans, AskFree (k ans)) → AskFree (.vis (Sum.inl op) k)

/-- On the ask-free fragment the tape is not read, so it cannot matter. -/
theorem askFree_tape_irrelevant {p : Prog CoreSig A} (hp : AskFree p) :
    ∀ (w : Word) (d₁ d₂ : Tape), runTape H p w d₁ = runTape H p w d₂ := by
  induction hp with
  | pure a => intro w d₁ d₂; rw [runTape_pure, runTape_pure]
  | @cas op k _ ih =>
    intro w d₁ d₂
    rw [runTape_cas, runTape_cas]
    cases hh : (referenceHandler H).handle op w with
    | ok aw =>
      obtain ⟨ans, w'⟩ := aw
      rw [casClause_ok _ _ hh, casClause_ok _ _ hh]
      exact ih ans w' d₁ d₂
    | error r => rw [casClause_error _ _ hh, casClause_error _ _ hh]

/-- **THE DETERMINISTIC SPECIALIZATION.** For an ask-free program the
observation is unique across ALL decision tapes — no tape needs fixing. This is
the fragment `../exhibits.lean`'s `denotes_unique` lives on, recovered inside
the nondeterministic language. -/
theorem denotes_unique_on_the_askFree_fragment {p : Prog CoreSig A} (hp : AskFree p)
    {w : Word} {d₁ d₂ : Tape} {o₁ o₂ : Obs A}
    (h₁ : Runs H p w d₁ o₁) (h₂ : Runs H p w d₂ o₂) : o₁ = o₂ :=
  Option.some.inj
    (((runs_sound H h₁).symm.trans (askFree_tape_irrelevant H hp w d₁ d₂)).trans
      (runs_sound H h₂))

end Determinism

/-! ## §6 — the witness: one admitted program, two tapes, two observations

The program asks once and loads one of two addresses according to the answer.
Both branches are ordinary admitted CAS: `load` is the estate's own operation
and the clause taken is `referenceHandler`'s.

Every fact in this section holds for EVERY address function `H`, because `load`
never consults it (the same `H`-independence the breaker's §2 witnesses use). -/

section Witness

/-- The bound address — the estate's existing falsifier constant. -/
def hit : Addr32 := Falsifier.zeroAddr

/-- The absent address. -/
def miss : Addr32 := ⟨List.replicate 32 1, by simp⟩

/-- The node that is bound. -/
def nA : Node := ⟨0, 0, [], []⟩

/-- The fixed initial configuration: one binding, at `hit`. -/
def initial : Word := [Binding.mk hit nA]

/-- **THE ADMITTED PROGRAM.** One `ask`, then one `load` whose address the
answer selects. Nothing else. -/
def branch : Prog CoreSig Node :=
  .vis (Sum.inr .ask) fun (b : Bool) =>
    .vis (Sum.inl (CasE.load (cond b hit miss))) .pure

variable (H : Bytes → Addr32)

/-- Decision stream 1. -/
def tapeHit : Tape := [true]

/-- Decision stream 2. -/
def tapeMiss : Tape := [false]

/-- The two streams are distinct. -/
theorem tapes_differ : tapeHit ≠ tapeMiss := by decide

/-- Permitted observation 1: the load succeeds and the word is unchanged. -/
theorem runs_hit : Runs H branch initial tapeHit (.ok (nA, initial)) :=
  runs_complete H branch initial tapeHit _ rfl

/-- Permitted observation 2: the load refuses, at the SAME program and the SAME
initial word. -/
theorem runs_miss : Runs H branch initial tapeMiss (.error (.noObject miss)) :=
  runs_complete H branch initial tapeMiss _ rfl

/-- The two observations are distinct — and distinct in KIND, so no finer or
coarser observation mask can identify them: one halts with a value, the other
refuses. -/
theorem observations_differ :
    (Except.ok (nA, initial) : Obs Node) ≠ .error (.noObject miss) := by
  simp

/-- Both are denotations of the one program at the one configuration. -/
theorem both_denote :
    Denotes H branch initial (.ok (nA, initial))
      ∧ Denotes H branch initial (.error (.noObject miss)) :=
  ⟨⟨tapeHit, runs_hit H⟩, ⟨tapeMiss, runs_miss H⟩⟩

/-- **WHERE THE NONDETERMINISM IS.** Each of `branch`'s two continuations is
ask-free, hence deterministic by §5b on its own. The CAS layer contributes
nothing to the counterexample: the single `ask` is the whole of it. -/
theorem both_continuations_are_deterministic (b : Bool) :
    AskFree (.vis (Sum.inl (CasE.load (cond b hit miss))) (Prog.pure : Node → Prog CoreSig Node)) :=
  .cas fun _ => .pure _

/-- The DECISION FRONTIER, kept separate from both: with no decisions at all the
program has no observation whatsoever. This is not a refusal and not a value —
`EXHIBITS-REVIEW.md` §4.2's `frontier decision` leaf, exhibited. -/
theorem empty_tape_is_a_frontier : runTape H branch initial [] = none := rfl

/-- Consequently the empty tape denotes nothing, which is why "no observation"
must not be read as "unique observation". -/
theorem empty_tape_denotes_nothing (o : Obs Node) : ¬ Runs H branch initial [] o := by
  intro h
  have := runs_sound H h
  rw [empty_tape_is_a_frontier] at this
  exact absurd this (by simp)

end Witness

/-! ## §7 — the counterexample

Two statements, because the row must defeat a UNIVERSAL claim and not merely
exhibit two runs. The first is the negation of `denotes_unique`'s own shape
(`../exhibits.lean` §5, `../../breaker-exhibits.lean` §2). The second is the
sharper "no such function" form, in the idiom
`Cas/Backend/Universal.lean`'s `run_has_no_composition_law` already uses. -/

section Counterexample
variable (H : Bytes → Addr32)

/-- **`EC1-CE042`, form 1.** `Denotes` is NOT a partial function. This is the
exact negation of the quantifier `denotes_unique` establishes for the
deterministic CAS/block fragment, at a language with one admitted decision
source — for every address function. -/
theorem denotes_is_not_unique :
    ¬ ∀ (p : Prog CoreSig Node) (w : Word) (o₁ o₂ : Obs Node),
        Denotes H p w o₁ → Denotes H p w o₂ → o₁ = o₂ := by
  intro huniq
  exact observations_differ
    (huniq branch initial _ _ (both_denote H).1 (both_denote H).2)

/-- **`EC1-CE042`, form 2 — THE LOAD-BEARING THEOREM.** There is NO function of
the program and the initial configuration alone that gives the permitted
observation. The quantifier order is what matters: `f` is chosen first, may
depend on `H`, may be non-computable, and may inspect the whole program — and
still no such `f` exists.

Hence a `denotes : Prog → Word → Obs` cannot be defined for this language at
all, and the public semantics must be the relation. -/
theorem no_choice_free_denotation :
    ¬ ∃ f : Prog CoreSig Node → Word → Obs Node,
        ∀ (p : Prog CoreSig Node) (w : Word) (d : Tape) (o : Obs Node),
          Runs H p w d o → o = f p w := by
  rintro ⟨f, hf⟩
  have h1 := hf branch initial tapeHit _ (runs_hit H)
  have h2 := hf branch initial tapeMiss _ (runs_miss H)
  exact observations_differ (h1.trans h2.symm)

/-- The same refutation against a PARTIAL candidate: even allowing `f` to
decline to answer, it cannot answer for `branch`. -/
theorem no_partial_choice_free_denotation :
    ¬ ∃ f : Prog CoreSig Node → Word → Option (Obs Node),
        (∀ (p : Prog CoreSig Node) (w : Word) (d : Tape) (o : Obs Node),
            Runs H p w d o → f p w = some o)
          ∧ (f branch initial).isSome := by
  rintro ⟨f, hf, _⟩
  exact observations_differ
    (Option.some.inj ((hf branch initial tapeHit _ (runs_hit H)).symm.trans
      (hf branch initial tapeMiss _ (runs_miss H))))

/-- **The pair, as the register row states it**: one admitted program, one fixed
initial configuration, two distinct typed decision streams, two distinct
permitted observations — and no choice-free denotation. -/
theorem EC1_CE042 :
    tapeHit ≠ tapeMiss
      ∧ Runs H branch initial tapeHit (.ok (nA, initial))
      ∧ Runs H branch initial tapeMiss (.error (.noObject miss))
      ∧ ((Except.ok (nA, initial) : Obs Node) ≠ .error (.noObject miss))
      ∧ (¬ ∃ f : Prog CoreSig Node → Word → Obs Node,
            ∀ (p : Prog CoreSig Node) (w : Word) (d : Tape) (o : Obs Node),
              Runs H p w d o → o = f p w)
      ∧ (∀ {A : Type} {p : Prog CoreSig A} {w : Word} {d : Tape} {o₁ o₂ : Obs A},
            Runs H p w d o₁ → Runs H p w d o₂ → o₁ = o₂) :=
  ⟨tapes_differ, runs_hit H, runs_miss H, observations_differ,
    no_choice_free_denotation H, fun h₁ h₂ => denotes_unique_given H h₁ h₂⟩

end Counterexample

/-! ## §8 — the same phenomenon at the SHIPPED agent language

CONDITIONAL on `EC1-XT012`: `EXISTING-TYPES.md` records that `AgentSig` is not
automatically part of Effect Core v1's alphabet. §1–§7 do not depend on this
section.

What it adds: the phenomenon is not a property of the workshop's `DecSig`. The
estate ALREADY ships a language with an undetermined answer — `LlmE.infer`,
whose reply arrives through `Prog.handleLlm`'s oracle parameter, and whose own
docstring (`Cas/Lang/Interp.lean`) says so: "The oracle's nondeterminism enters
only as the recorded answer."

Every declaration in the statements below is SHIPPED: `Prog.handleLlm`,
`interpretRef`, `AgentSig`, `liftCas`, `load`. The oracle is exactly the
`decisions` parameter, in function form, and the theorem says the meaning is a
function of `(program, word, ORACLE)` and of nothing smaller. -/

section ShippedAgentLanguage

/-- One `infer`, then one `load` the reply selects. Written with the shipped
`liftCas`/`load`. -/
def agentBranch : Prog AgentSig Node :=
  .vis (Sum.inr (LlmE.infer "which address?")) fun s =>
    liftCas (load (if s.isEmpty then hit else miss))

/-- Oracle 1 — the empty reply. -/
def oracleHit : String → String := fun _ => ""

/-- Oracle 2. -/
def oracleMiss : String → String := fun _ => "x"

variable (H : Bytes → Addr32)

/-- Under oracle 1 the shipped pipeline succeeds. -/
theorem agent_hit :
    interpretRef H (agentBranch.handleLlm oracleHit) initial = .ok (nA, initial) := rfl

/-- Under oracle 2 the shipped pipeline refuses — same program, same word. -/
theorem agent_miss :
    interpretRef H (agentBranch.handleLlm oracleMiss) initial
      = .error (.noObject miss) := rfl

/-- **The counterexample at shipped declarations only.** No function of the
program and the word alone agrees with `interpretRef ∘ handleLlm` for every
oracle. The oracle is a semantic parameter of the estate's agent language, not
an implementation detail of a driver. -/
theorem shipped_agent_has_no_oracle_free_denotation :
    ¬ ∃ f : Prog AgentSig Node → Word → Except Refusal (Node × Word),
        ∀ (oracle : String → String) (p : Prog AgentSig Node) (w : Word),
          interpretRef H (p.handleLlm oracle) w = f p w := by
  rintro ⟨f, hf⟩
  have h1 := hf oracleHit agentBranch initial
  have h2 := hf oracleMiss agentBranch initial
  rw [agent_hit] at h1
  rw [agent_miss] at h2
  exact absurd (h1.trans h2.symm) (by simp)

/-- And the positive companion there too: one fixed oracle IS a semantics.
`interpretRef ∘ handleLlm` is a function of `(oracle, program, word)`, so
replay against a recorded oracle is deterministic — the shipped analogue of
`denotes_unique_given`. -/
theorem shipped_agent_unique_given_oracle (oracle : String → String)
    (p : Prog AgentSig Node) (w : Word) (o₁ o₂ : Except Refusal (Node × Word))
    (h₁ : interpretRef H (p.handleLlm oracle) w = o₁)
    (h₂ : interpretRef H (p.handleLlm oracle) w = o₂) : o₁ = o₂ :=
  h₁.symm.trans h₂

end ShippedAgentLanguage

end EffectCoreNondet

/-! ## Kernel receipts

Read, not asserted. Every line must show `[propext]`, `[propext, Quot.sound]`,
or no axioms at all. A `sorryAx` or a `Classical.choice` here is a finding. -/

#print axioms EffectCoreNondet.casClause_ok
#print axioms EffectCoreNondet.casClause_error
#print axioms EffectCoreNondet.runTape_pure
#print axioms EffectCoreNondet.runTape_cas
#print axioms EffectCoreNondet.runTape_ask_nil
#print axioms EffectCoreNondet.runTape_ask_cons
#print axioms EffectCoreNondet.runs_sound
#print axioms EffectCoreNondet.runs_complete
#print axioms EffectCoreNondet.runs_iff
#print axioms EffectCoreNondet.denotes_unique_given
#print axioms EffectCoreNondet.replay_is_a_function
#print axioms EffectCoreNondet.askFree_tape_irrelevant
#print axioms EffectCoreNondet.denotes_unique_on_the_askFree_fragment
#print axioms EffectCoreNondet.tapes_differ
#print axioms EffectCoreNondet.runs_hit
#print axioms EffectCoreNondet.runs_miss
#print axioms EffectCoreNondet.observations_differ
#print axioms EffectCoreNondet.both_continuations_are_deterministic
#print axioms EffectCoreNondet.both_denote
#print axioms EffectCoreNondet.empty_tape_is_a_frontier
#print axioms EffectCoreNondet.empty_tape_denotes_nothing
#print axioms EffectCoreNondet.denotes_is_not_unique
#print axioms EffectCoreNondet.no_choice_free_denotation
#print axioms EffectCoreNondet.no_partial_choice_free_denotation
#print axioms EffectCoreNondet.EC1_CE042
#print axioms EffectCoreNondet.agent_hit
#print axioms EffectCoreNondet.agent_miss
#print axioms EffectCoreNondet.shipped_agent_has_no_oracle_free_denotation
#print axioms EffectCoreNondet.shipped_agent_unique_given_oracle
