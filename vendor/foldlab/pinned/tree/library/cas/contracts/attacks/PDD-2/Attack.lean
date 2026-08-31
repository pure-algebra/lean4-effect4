import Cas.Lang.Wp

/-!
# PDD-2 — the adversarial record

WHAT THIS FILE IS. The independent breaker's attack against the PDD-2
contract packet (`library/cas/contracts/PDD-2.contract.md`) and its
castle (`library/cas/Cas/Lang/Wp.lean`) at commit `539beec8`. Every
wrong-but-passing candidate, every counter-witness table and every
kernel-checked verification the attack produced is here, whether it
broke something or not: a failed break attempt is the packet's earned
confidence, and earned confidence is record too.

IMPORTS. `Cas.Lang.Wp` only, which pulls `Cas.Lang.Defun` and
`Cas.Codec.Sha256`. Nothing imports this file.

THIS FILE MUST NOT ENTER ANY LAKE LIBRARY TARGET. It is adversarial
apparatus, not library content. It sits under `contracts/attacks/`,
outside every `srcDir` and `globs` that `lakefile.toml` declares for
`Cas`, `CasWp`, `CasBackend`, `CasExamples` and `Gate`, so it is
outside `Walk.libraryImports` and moves no byte of
`surface/cas-surface.json`, `surface/cas-obligations.json`,
`surface/cas-laws.json` or `docs/lab-core/ENVIRONMENT.json`. It is
elaborated by hand — `lake env lean library/cas/contracts/attacks/PDD-2/Attack.lean`
from `library/cas` — and never by `lake build`. Adding it to a target
is a promotion, and a promotion is a ruling.

NO `sorry`, no `native_decide`, no `ofReduceBool`. Digest computation
runs in `#eval`, never in kernel `decide`, per this lane's law.

Verdict, findings and the full failed-attempt list: `RESULTS.md`
beside this file.
-/

set_option maxRecDepth 100000

namespace Cas.Lang.Attack

open Cas Cas.Lang Cas.Lang.Falsifier

/-! ## 0. The corpus — tables the packet's battery does not cover

The packet's battery is ONE chained table (`chained`) plus the refusing
`absentLoad`. These are the shapes an adversary reaches for: a load
before any put, an answer index past the end of the history, a
completing prefix followed by a dangling suffix, a load through the
table's own answer, a load of a literal the word does not hold, a
DUPLICATE put (the store dedups, so the word does NOT grow), a
three-line table ending in a load, and a prefix that refuses MIDWAY. -/

/-- A load before any put, at the literal all-zero address. -/
def loadFirst : PProg := [.load (.lit zeroAddr), putA]

/-- A put whose only answer index points past the end of the history. -/
def danglingAns : PProg := [.put 0 0 [] [(0, .ans 5)]]

/-- A completing prefix, then a line indexing OUT OF RANGE. -/
def preThenDangling : PProg := [putA, .put 0 1 [] [(0, .ans 3)]]

/-- A put, then a load of that put's own answer: resolves through the
history and finds the binding the put admitted. -/
def putThenLoadOwn : PProg := [putA, .load (.ans 0)]

/-- A put, then a load of a literal the word does not hold. -/
def putThenLoadAbsent : PProg := [putA, .load (.lit zeroAddr)]

/-- THE SAME PUT TWICE. The store dedups, so the word grows by ONE, not
two — the shape that separates the battery's `twoBindings`
postcondition from a length-blind one. -/
def dupPut : PProg := [putA, putA]

/-- Three lines, the last a load through the second answer. -/
def chainThenLoad : PProg := [putA, putB, .load (.ans 1)]

/-- A nonempty prefix that REFUSES MID-TABLE: line 1 completes, line 2
loads an address the word does not hold. The probe for
`runPFrom_append_refused`'s interplay with `wp_append`. -/
def refusesMidway : PProg := [putA, .load (.lit zeroAddr)]

/-- A put whose node is a DIFFERENT LENGTH from `putA`'s.

The payload is not decoration. `Falsifier.lenAddr` addresses a node by
its ENCODED LENGTH, so `.put 0 2 [] []` and `.put 0 0 [] []` collide —
same address, different node — and the store REFUSES the second as the
hash collision it is. A probe that needs two distinct addresses has to
say so in bytes. See `toy_hash_collides` below. -/
def putD : PLine := .put 0 2 [7, 7, 7] []

/-- The address `putA` admits at the toy hash. -/
def addrA : Addr32 := lenAddr (encodeNode ⟨0, 0, [], []⟩)

/-- A starting word that ALREADY holds `addrA` — the word `onePut`
leaves behind. Run-relativity is tested against this, not against `[]`. -/
def wordWithA : Word := (runP lenAddr onePut []).2

/-- The trivial Boolean postcondition: the verdict is then pure
termination, and a disagreement cannot hide behind a false `Q`. -/
def alwaysTrue : Addr32 → Word → Bool := fun _ _ => true

/-- THE TOY ADDRESS FUNCTION COLLIDES, and the collision is
OBSERVABLE: two nodes of equal encoded length share an address, and the
store refuses the second because its content differs. Every witness in
`Wp.lean` was re-checked against this (see `RESULTS.md`); none of them
depends on `lenAddr` separating anything, and the packet's ledger
witness is reproduced at the production digest below. -/
theorem toy_hash_collides :
    lenAddr (encodeNode ⟨0, 0, [], []⟩) = lenAddr (encodeNode ⟨0, 2, [], []⟩)
      ∧ lenAddr (encodeNode ⟨0, 0, [], []⟩)
          ≠ lenAddr (encodeNode ⟨0, 2, [7, 7, 7], []⟩) := by
  refine ⟨by decide, by decide⟩

/-! ## 1. THE LEDGER WITNESS, VERIFIED INDEPENDENTLY

The packet's break ledger claims original-L8 is FALSE at `pre = []`,
`post = [.put 0 0 [] []]`, `Q = ⊤`, `w = []`. Restated here without
invoking `falsifier_empty_prefix`, and DECIDED rather than argued: the
two sides are computed by `wpB`, which `wpB_iff_wp` ties back to `wp`. -/

/-- The witness, computed. LEFT is `true`, RIGHT is `false`. -/
theorem ledger_witness_computed :
    (wpB lenAddr [] ([] ++ onePut) alwaysTrue [],
     wpB lenAddr [] [] (fun _ w' =>
        wpB lenAddr (PProg.answersFrom lenAddr [] []) onePut alwaysTrue w') [])
      = (true, false) := by decide

/-- The same witness at the `Prop` transformer, proved from `wp_iff`
rather than from the builder's `falsifier_empty_prefix`. -/
theorem ledger_witness_verified :
    wp lenAddr ([] ++ onePut) WPost.top []
      ∧ ¬ wp lenAddr [] (fun _ w' =>
            wpAux lenAddr False (PProg.answersFrom lenAddr [] []) onePut
              WPost.top w') [] := by
  refine ⟨?_, ?_⟩
  · rw [wp_iff]
    exact trivial
  · rw [wp_iff]
    exact id

/-- AND THE BREAK IS NOT AN ARTIFACT OF THE TOY HASH: the same witness
fires at the production digest. An `#eval` IO assert — never a kernel
`decide`, never `native_decide` — so no `ofReduceBool` enters the
census. -/
def ledgerWitnessAtDigest : IO Unit := do
  let left := wpB Cas.sha256Addr [] ([] ++ onePut) alwaysTrue []
  let right := wpB Cas.sha256Addr [] [] (fun _ w' =>
    wpB Cas.sha256Addr (PProg.answersFrom Cas.sha256Addr [] []) onePut
      alwaysTrue w') []
  unless left && !right do
    throw (IO.userError
      "PDD-2 attack: the ledger's empty-prefix witness does not fire at sha256Addr")
  IO.println
    "PDD-2 attack: ledger witness reproduced at the production digest — left true, right false"

#eval ledgerWitnessAtDigest

/-! ## 2. THE WEAKENING ATTACKED — is `pre ≠ []` enough?

The Boolean analogue of `wp_append`, which `wpB_iff` and `wpB_iff_wp`
make a statement about `wp`: at `pre ≠ []`,

    wpB H [] (pre ++ post) Q w
      = wpB H [] pre (fun _ w' => wpB H (answersFrom H [] pre) post Q w') w

checked EXHAUSTIVELY over 12 prefixes x 12 suffixes x 3 starting words
= 432 points, at the toy hash, by `decide`. If the weakening still
missed an edge, a point of this grid would disagree. -/

/-- One point of the composition grid, as a Boolean. -/
def appendAgrees (H : Bytes → Addr32) (pre post : PProg)
    (Q : Addr32 → Word → Bool) (w : Word) : Bool :=
  wpB H [] (pre ++ post) Q w
    == wpB H [] pre (fun _ w' => wpB H (PProg.answersFrom H [] pre) post Q w') w

/-- The prefixes. Every one is NONEMPTY — the side condition — and
between them they complete, refuse at line 1, refuse MID-TABLE, dangle,
dedup, and end in a load. -/
def prefixes : List PProg :=
  [onePut, chained, dupPut, putThenLoadOwn, refusesMidway, absentLoad,
   danglingAns, loadFirst, chainThenLoad, preThenDangling,
   [putD], [putA, putD]]

/-- The suffixes, EMPTY INCLUDED: the law puts no hypothesis on `post`,
so the empty suffix is its own edge. -/
def suffixes : List PProg :=
  [[], onePut, chained, [putB], [putD], [.load (.ans 0)],
   [.load (.ans 1)], [.load (.ans 3)], [.load (.lit zeroAddr)],
   [.put 0 1 [] [(0, .ans 3)]], absentLoad, dupPut]

/-- The starting words: empty, one already holding `addrA`, and the one
the chained table leaves behind. -/
def words : List Word :=
  [[], wordWithA, (runP lenAddr chained []).2]

/-- EXHAUSTIVE, at the trivial postcondition. The composition law holds
at every one of the 432 points, for every nonempty prefix. -/
theorem append_law_holds_on_grid_top :
    (prefixes.flatMap fun pre =>
      suffixes.flatMap fun post =>
        words.map fun w =>
          appendAgrees lenAddr pre post alwaysTrue w).all id = true := by
  decide

/-- EXHAUSTIVE, at the battery's DISCRIMINATING postcondition — a
postcondition that reads the final word's length and last address, so a
transformer that threaded the word wrongly would show here. -/
theorem append_law_holds_on_grid_twoBindings :
    (prefixes.flatMap fun pre =>
      suffixes.flatMap fun post =>
        words.map fun w =>
          appendAgrees lenAddr pre post Battery.twoBindings w).all id = true := by
  decide

/-- NON-VACUITY. The grid does not pass because both sides are always
false: 156 of its 432 points have the LEFT side TRUE. A law that only
ever compares `false` to `false` is not evidence. -/
theorem append_grid_is_not_vacuous :
    ((prefixes.flatMap fun pre =>
      suffixes.flatMap fun post =>
        words.map fun w =>
          wpB lenAddr [] (pre ++ post) alwaysTrue w).filter id).length = 156 := by
  decide

/-- AND THE SIDE CONDITION IS LOAD-BEARING. Drop `pre ≠ []` and the
same grid FAILS at 12 of its 36 points — every suffix that completes
from the empty prefix is a counter-witness. The ledger's break,
exhibited as a census rather than as one line. -/
theorem append_law_fails_at_empty_prefix :
    ((suffixes.flatMap fun post =>
      words.map fun w => appendAgrees lenAddr [] post alwaysTrue w).filter
        (fun b => !b)).length = 12 := by
  decide

/-! ### 2b. The named edge probes

The edges the weakening might still have missed, one table at a time so
a reader sees the shape rather than a grid cell. -/

/-- EDGE 1 — A NONEMPTY PREFIX THAT REFUSES MID-TABLE. `refusesMidway`
completes line 1 and refuses line 2; the suffix references an answer
the prefix never produced. Both sides are FALSE and the law holds —
this is the case `runPFrom_append_refused` carries, reached with
`env ≠ []` rather than with `pre ≠ []`. -/
theorem edge_refusing_prefix :
    wpB lenAddr [] (refusesMidway ++ [putB]) alwaysTrue [] = false
      ∧ appendAgrees lenAddr refusesMidway [putB] alwaysTrue [] = true := by
  decide

/-- EDGE 2 — A PREFIX THAT COMPLETES WITH ANSWERS THE SUFFIX INDEXES
OUT OF RANGE. `[putA]` answers one address; the suffix asks for
`.ans 3`. The threaded history has one entry, so the suffix dangles;
both sides are FALSE. -/
theorem edge_suffix_index_out_of_range :
    wpB lenAddr [] ([putA] ++ [.put 0 1 [] [(0, .ans 3)]]) alwaysTrue [] = false
      ∧ appendAgrees lenAddr [putA] [.put 0 1 [] [(0, .ans 3)]] alwaysTrue []
          = true := by
  decide

/-- EDGE 3 — A LOAD RESOLVING AGAINST THE STARTING WORD RATHER THAN AN
ANSWER. The SAME table gets two verdicts at two starting words: from
`wordWithA`, which already holds `addrA`, the suffix's load completes;
from `[]` it refuses. Run-relativity, decided — and the composition law
holds at both. -/
theorem edge_load_against_starting_word :
    wpB lenAddr [] ([putD] ++ [.load (.lit addrA)]) alwaysTrue wordWithA = true
      ∧ wpB lenAddr [] ([putD] ++ [.load (.lit addrA)]) alwaysTrue [] = false
      ∧ appendAgrees lenAddr [putD] [.load (.lit addrA)] alwaysTrue wordWithA
          = true
      ∧ appendAgrees lenAddr [putD] [.load (.lit addrA)] alwaysTrue [] = true := by
  decide

/-- EDGE 4 — THE OTHER DISJUNCT. `wpAux_append` licenses `pre = []`
when `env ≠ []`, and that disjunct is not decoration: it is the case
the induction lands in once a line has been consumed, and there the law
is TRUE at every suffix, postcondition and word. -/
theorem edge_empty_prefix_nonempty_env (Q : WPost) (w : Word) (post : PProg)
    (a : Addr32) :
    wpAux lenAddr False [a] ([] ++ post) Q w
      ↔ wpAux lenAddr False [a] []
          (fun _ w' =>
            wpAux lenAddr False ([a] ++ PProg.answersFrom lenAddr [a] []) post Q w') w :=
  wpAux_append lenAddr False [a] [] post Q w (Or.inl (by simp))

/-! ## 3. ADEQUACY — could a WRONG `wp` satisfy every law?

The decisive result: L1 alone PINS `wp`. Instantiate the anchor at a
singleton precondition and the transformer's value at every table,
postcondition and word is forced. No wrong transformer survives L1, so
the packet's adequacy obligation reduces to `Triple`'s definition and
to `runP` — and to nothing else in the file. -/

section Adequacy

variable (H : Bytes → Addr32)

/-- A precondition entails another exactly when the second holds at the
one word the first admits. -/
theorem le_singleton (P' : WPre) (w : Word) :
    ((fun v => v = w) ≤ P') ↔ P' w := by
  constructor
  · intro h; exact h w rfl
  · intro h v hv; subst hv; exact h

/-- **THE ANCHOR PINS THE TRANSFORMER.** Any `wp'` satisfying L1 —
`Triple H p P Q ↔ P ≤ wp' p Q` at every `p`, `P` and `Q` — agrees with
`wp` at every table, postcondition and word. The adequacy class is
discharged by L1 alone: there is NO wrong-but-passing transformer, and
the packet's whole adequacy question reduces to whether `Triple` and
`runP` say what they should. -/
theorem anchor_pins_wp (wp' : PProg → WPost → WPre)
    (h : ∀ p P Q, Triple H p P Q ↔ P ≤ wp' p Q)
    (p : PProg) (Q : WPost) (w : Word) :
    wp' p Q w ↔ wp H p Q w := by
  have hb := h p (fun v => v = w) Q
  have ha := Triple_iff_wp H p (fun v => v = w) Q
  rw [le_singleton] at hb ha
  exact hb.symm.trans ha

end Adequacy

/-! ### 3a. Wrong-but-passing candidates, and the law that catches each

Three adversarial transformers, each satisfying a large part of the
algebra. Each is caught, and the record says by WHICH law — the point
being that most of the algebra is blind to them and the anchor is not. -/

section Candidates

variable (H : Bytes → Addr32)

/-! #### Candidate A — `wlp` passed off as `wp`

BREAKER.md, wp-sp-calculus: "WLP passed off as WP — crash-freedom
dropped; exhibit the crashing run declared correct." -/

theorem candidateA_passes_L3 {Q Q' : WPost} (hq : Q ≤ Q') (p : PProg) :
    wlp H p Q ≤ wlp H p Q' := wlp_mono H hq p

theorem candidateA_passes_L4 (p : PProg) (Q Q' : WPost) (w : Word) :
    wlp H p (WPost.meet Q Q') w ↔ (wlp H p Q w ∧ wlp H p Q' w) := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wlp_of_done H hs, WPost.meet]
  · simp only [wlp_of_refused H hs, and_self]

theorem candidateA_passes_L5 {ι : Type} (_hι : Nonempty ι) (p : PProg)
    (Q : ι → WPost) (w : Word) :
    wlp H p (fun a w' => ∀ i, Q i a w') w ↔ ∀ i, wlp H p (Q i) w := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wlp_of_done H hs]
  · simp only [wlp_of_refused H hs]
    exact ⟨fun _ _ => trivial, fun _ => trivial⟩

theorem candidateA_passes_L6 (p : PProg) (Q Q' : WPost) (w : Word) :
    wlp H p (WPost.join Q Q') w ↔ (wlp H p Q w ∨ wlp H p Q' w) := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wlp_of_done H hs, WPost.join]
  · simp only [wlp_of_refused H hs, or_self]

/-- Candidate A even inherits the COMPOSITION law verbatim: the
builder stated `wpAux_append` at an arbitrary `refused`, so the
weakened L8 does not distinguish `wp` from `wlp` at all. -/
theorem candidateA_passes_L8 (env : List Addr32) (pre post : PProg)
    (Q : WPost) (w : Word) (hne : env ≠ [] ∨ pre ≠ []) :
    wpAux H True env (pre ++ post) Q w
      ↔ wpAux H True env pre
          (fun _ w' =>
            wpAux H True (env ++ PProg.answersFrom H env pre) post Q w') w :=
  wpAux_append H True env pre post Q w hne

/-- CANDIDATE A IS CAUGHT BY L7 — the excluded miracle. `wlp` of the
IMPOSSIBLE postcondition is TRUE at the refusing table, so a `wp`
defined as `wlp` proves anything about a program that crashes. -/
theorem candidateA_caught_by_L7 :
    wlp lenAddr absentLoad WPost.bot [] ∧ ¬ wp lenAddr absentLoad WPost.bot [] :=
  ⟨by simp [wlp, wpAux, absentLoad, PIn.resolve],
   wp_bot lenAddr absentLoad []⟩

/-- CANDIDATE A IS ALSO CAUGHT BY L1, in the completeness direction:
the refusing table satisfies `P ≤ wlp p Q` and no total triple. -/
theorem candidateA_caught_by_L1 :
    ((fun w => w = ([] : Word)) ≤ wlp lenAddr absentLoad WPost.bot)
      ∧ ¬ Triple lenAddr absentLoad (fun w => w = []) WPost.bot := by
  refine ⟨?_, ?_⟩
  · intro w hw
    subst hw
    simp [wlp, wpAux, absentLoad, PIn.resolve]
  · intro h
    obtain ⟨a, w', hs, _⟩ := h [] rfl
    simp [runP, runPFrom, absentLoad, PIn.resolve] at hs

/-! #### Candidate B — the SNAPSHOT error

BREAKER.md, loops §11.0: "wrong-state postcondition — the exit bounds
hold for a modified input, not the entry value." A transformer that
evaluates the postcondition at the STARTING word instead of the final
one. This is the candidate the algebra is blindest to. -/

def wpStale (p : PProg) (Q : WPost) : WPre :=
  fun w => ∃ a w', runP H p w = (.done a, w') ∧ Q a w

theorem candidateB_passes_L3 {Q Q' : WPost} (hq : Q ≤ Q') (p : PProg) :
    wpStale H p Q ≤ wpStale H p Q' := by
  intro w hw
  obtain ⟨a, w', hs, hq'⟩ := hw
  exact ⟨a, w', hs, hq a w hq'⟩

/-- Determinism does the work on the starting word exactly as it does
on the final one, so conjunctivity cannot see the defect. -/
theorem candidateB_passes_L4 (p : PProg) (Q Q' : WPost) (w : Word) :
    wpStale H p (WPost.meet Q Q') w ↔ (wpStale H p Q w ∧ wpStale H p Q' w) := by
  constructor
  · rintro ⟨a, w', hs, hq, hq'⟩
    exact ⟨⟨a, w', hs, hq⟩, ⟨a, w', hs, hq'⟩⟩
  · rintro ⟨⟨a, w', hs, hq⟩, ⟨b, w'', ht, hq'⟩⟩
    rw [hs] at ht
    simp only [Prod.mk.injEq, Status.done.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨a, w', hs, hq, hq'⟩

theorem candidateB_passes_L6 (p : PProg) (Q Q' : WPost) (w : Word) :
    wpStale H p (WPost.join Q Q') w ↔ (wpStale H p Q w ∨ wpStale H p Q' w) := by
  constructor
  · rintro ⟨a, w', hs, hq | hq⟩
    · exact Or.inl ⟨a, w', hs, hq⟩
    · exact Or.inr ⟨a, w', hs, hq⟩
  · rintro (⟨a, w', hs, hq⟩ | ⟨a, w', hs, hq⟩)
    · exact ⟨a, w', hs, Or.inl hq⟩
    · exact ⟨a, w', hs, Or.inr hq⟩

/-- And it passes the EXCLUDED MIRACLE too. -/
theorem candidateB_passes_L7 (p : PProg) (w : Word) :
    ¬ wpStale H p WPost.bot w := by
  rintro ⟨_, _, _, hq⟩
  exact hq

/-- CANDIDATE B IS CAUGHT BY L1, AND ONLY BY L1. The postcondition "the
final word holds exactly one binding" is established by `onePut` from
the empty word; the stale transformer reads it at the EMPTY starting
word and reports false. Monotonicity, conjunctivity, disjunctivity and
the excluded miracle are all blind to this. -/
theorem candidateB_caught_by_L1 :
    Triple lenAddr onePut (fun w => w = []) (fun _ w' => w'.length = 1)
      ∧ ¬ ((fun w => w = ([] : Word))
            ≤ wpStale lenAddr onePut (fun _ w' => w'.length = 1)) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    subst hw
    exact ⟨_, _, rfl, rfl⟩
  · intro h
    obtain ⟨_, _, _, hq⟩ := h [] rfl
    exact absurd hq (by decide)

/-! #### Candidate C — the MIRACLE

BREAKER.md, wp-sp-calculus §2.N: "`assume false` proves anything." The
cheap candidate, here to name which law is the cheap defence. -/

def wpMiracle (_ : PProg) (_ : WPost) : WPre := fun _ => True

theorem candidateC_passes_L3_L4_L6 (p : PProg) (Q Q' : WPost) (w : Word) :
    (wpMiracle p Q ≤ wpMiracle p Q')
      ∧ (wpMiracle p (WPost.meet Q Q') w
          ↔ (wpMiracle p Q w ∧ wpMiracle p Q' w))
      ∧ (wpMiracle p (WPost.join Q Q') w
          ↔ (wpMiracle p Q w ∨ wpMiracle p Q' w)) :=
  ⟨fun _ _ => trivial, ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩,
   ⟨fun _ => Or.inl trivial, fun _ => trivial⟩⟩

theorem candidateC_caught_by_L7 (p : PProg) (w : Word) :
    wpMiracle p WPost.bot w ∧ ¬ wp H p WPost.bot w :=
  ⟨trivial, wp_bot H p w⟩

end Candidates

/-! ## 4. THE COMPUTED TRANSFORMER vs THE STATED ONE

`wpB_iff_wp` is quantified over ALL tables, postconditions and words —
the battery's single chained table is not the scope of the claim. Even
so, the computed transformer is checked here against a REFERENCE read
straight off the trusted run, on every adversarial shape of the corpus,
at both a discriminating and a trivial postcondition. -/

/-- The reference: the verdict read straight off `runP`, independent of
`wpB`'s own recursion. -/
def refWpB (H : Bytes → Addr32) (p : PProg) (Q : Addr32 → Word → Bool)
    (w : Word) : Bool :=
  match runP H p w with
  | (.done a, w') => Q a w'
  | _ => false

/-- The adversarial corpus. -/
def corpus : List PProg :=
  [loadFirst, danglingAns, preThenDangling, putThenLoadOwn,
   putThenLoadAbsent, dupPut, chainThenLoad, refusesMidway,
   chained, onePut, absentLoad, [], [putD], [putA, putD]]

/-- EXHAUSTIVE: `wpB` equals the reference at every shape of the corpus
and every starting word, at the discriminating postcondition. -/
theorem wpB_matches_reference_twoBindings :
    (corpus.flatMap fun p =>
      words.map fun w =>
        wpB lenAddr [] p Battery.twoBindings w
          == refWpB lenAddr p Battery.twoBindings w).all id = true := by
  decide

/-- The same at the trivial postcondition, where the verdict is pure
termination. -/
theorem wpB_matches_reference_top :
    (corpus.flatMap fun p =>
      words.map fun w =>
        wpB lenAddr [] p alwaysTrue w == refWpB lenAddr p alwaysTrue w).all id
      = true := by
  decide

/-- THE BATTERY'S POSTCONDITION IS NOT VACUOUS. `twoBindings` separates
the chained table (two bindings) from the DUPLICATE-PUT table, which
the store dedups to ONE. A postcondition that could not tell these
apart would make the battery's `true` worthless. -/
theorem twoBindings_discriminates :
    wpB lenAddr [] chained Battery.twoBindings [] = true
      ∧ wpB lenAddr [] dupPut Battery.twoBindings [] = false
      ∧ (runP lenAddr dupPut []).2.length = 1
      ∧ (runP lenAddr chained []).2.length = 2 := by
  decide

/-- THE BATTERY CAN GO RED. Controls: tables whose computed `wp` at the
battery's own postconditions is FALSE, decided in the same kernel. A
gate that cannot fail proves nothing. -/
theorem battery_control_red :
    wpB lenAddr [] loadFirst Battery.twoBindings [] = false
      ∧ wpB lenAddr [] absentLoad alwaysTrue [] = false
      ∧ wpB lenAddr [] danglingAns alwaysTrue [] = false := by
  decide

/-! ## 5. THE FUEL

`falsifier_fuel_bound_is_tight` exhibits ONE table still running at
`p.length`. The attack asks whether that is a property of that table or
of every table. -/

/-- The packet's falsifier, re-verified from the definitions. -/
theorem fuel_falsifier_verified :
    (run lenAddr onePut.length (embed onePut) []).1.isRunning = true
      ∧ (runP lenAddr onePut []).1.isDone = true := by
  decide

/-- THE BOUND IS TIGHT FOR EVERY COMPLETING TABLE, not only the
witness: at `p.length` each of these is still RUNNING, and at
`p.length + 1` none is. `p.length + 1` is not slack anywhere a caller
could round it down. -/
theorem fuel_tight_on_completing_tables :
    ([onePut, chained, chainThenLoad, dupPut, putThenLoadOwn].map
      (fun p => ((run lenAddr p.length (embed p) []).1.isRunning,
                 (run lenAddr (p.length + 1) (embed p) []).1.isRunning)))
      = [(true, false), (true, false), (true, false), (true, false),
         (true, false)] := by
  decide

/-- AND IT IS SLACK ON REFUSING TABLES — the honest other half. A table
that refuses early has halted long before `p.length`, so "tight" is a
statement about tables that COMPLETE. -/
theorem fuel_slack_on_refusing_tables :
    ([absentLoad, danglingAns, loadFirst].map
      (fun p => (run lenAddr p.length (embed p) []).1.isRunning))
      = [false, false, false] := by
  decide

/-! ## 6. CLAIM SCOPE — the two-state reading

`Triple_two_state` is stated at a UNIVERSAL starting word: "for every
`w₀`, the singleton triple holds". That is the two-state triple at
precondition `⊤`. The debt object's `σ` asks for a two-state
postcondition relative to `P`. It is derivable in three lines — proved
here, so the record says "derivable", not "missing". -/

section TwoState

variable (H : Bytes → Addr32)

/-- The two-state triple RELATIVE TO A PRECONDITION — the form the debt
object asks for, which `Triple_two_state` does not state. -/
theorem Triple_two_state_rel (p : PProg) (P : WPre)
    (R : Word → Addr32 → Word → Prop) :
    (∀ w₀, P w₀ → Triple H p (fun w => w = w₀) (fun a w' => R w₀ a w'))
      ↔ ∀ w₀, P w₀ → ∃ a w', runP H p w₀ = (.done a, w') ∧ R w₀ a w' := by
  refine ⟨fun h w₀ hp => h w₀ hp w₀ rfl, fun h w₀ hp w hw => ?_⟩
  subst hw
  exact h w hp

/-- And it is not vacuous: an actual two-state statement about the
carrier — `onePut` run from the empty word leaves exactly one binding
and answers the address it admitted. -/
theorem two_state_witness :
    Triple lenAddr onePut (fun w => w = [])
      (fun a w' => w'.length = 1 ∧ a = addrA) := by
  intro w hw
  subst hw
  exact ⟨_, _, rfl, rfl, rfl⟩

end TwoState

end Cas.Lang.Attack
