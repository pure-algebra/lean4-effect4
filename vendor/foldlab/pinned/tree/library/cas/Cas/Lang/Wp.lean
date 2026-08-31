import Cas.Lang.Defun
import Cas.Codec.Sha256

/-!
# `wp` — the weakest precondition of a program table

Contract packet: `library/cas/contracts/PDD-2.contract.md` (the laws,
their falsification equations, the carrier defence and the claim-scope
line). Design basis:
`.staging/operational-structure/PROOF-DRIVEN-DEVELOPMENT.md` §2 (the
debt object) and §5 A2. Book vocabulary: *Program Proofs* ch. 2, tagged
in `.agents/skills/implement/CATALOG.md` — §2.2 (the total-correctness
triple), §2.3–§2.4 (the transformer pair), §2.6 (sequential
composition), §2.9 (WLP), §2.12 (definedness), §2.N (the excluded
miracle), §3.1 (the variant).

## The carrier judgment

`wp` is stated over the DEFUNCTIONALIZED TABLE (`PProg`, `Defun.lean`)
and its direct run `runP`, not over `Prog` and the big-step denotation.
Three facts about the carriers decide it:

- the variant is STRUCTURAL here. On `Prog` the continuations are host
  functions, so fuel has to be produced rather than assumed
  (`run_of_interpretRef`, `Handler.lean:209` — "enough fuel is a
  conclusion, not a hypothesis"); on a table the measure is the line
  count and `runP_embed_agree` fixes the bound at `p.length + 1`
  exactly;
- `wp` has to COMPUTE. A table is first-order content (R14 stratum 1),
  so the recursion that defines the `Prop` transformer defines the
  `Bool` one (`wpB`) — verification-condition generation, decided on
  the table;
- nothing is lost. `runP` halts at every table and word
  (`runP_halts`), and the estate's bridge (`run_interpretRef_agree`)
  carries the anchor to the big-step judgment at that exact fuel, so
  `wp_iff_interpretRef` proves the SAME transformer against the
  denotation. The choice buys the two properties above and costs no
  generality at this rung.

Everything is relative to the STARTING WORD: `WPre` is a predicate on
it, and a run's meaning is relative to it (PDD §6.2). The two-state
reading — the book's `old` — enters as a logical variable, by
instantiating the precondition at the starting word
(`Triple_two_state`), so no second carrier is minted for it.

## The shape of the file

`wpAux` is ONE recursion carrying the value a REFUSAL is worth. `wp`
takes that to be `False` (total correctness), `wlp` takes it to be
`True` (partial correctness), and §2.9's distinction is therefore a
parameter rather than a second definition. `wpAux_iff` characterizes
the fold by the run and every law below is read off it.

The counter-examples are named `falsifier_*` and are the packet's
falsification equations, exhibited — named rather than anonymous so the
packet can cite them and a breaker can attack them by name. Each one
kills a law the packet does NOT claim, and one of them
(`falsifier_empty_prefix`) killed a law it DID claim: see the packet's
break ledger.

Nothing in this file runs a program at gate time except the battery at
the bottom, and nothing here is imported by the library: it is proof-
stratum statement apparatus (A1's licence, decision 2 — no new sort, no
registry motion), declared as its own Lake library so `lake build`
kernel-checks it.
-/

namespace Cas.Lang

/-! ## Predicates over the run's observables -/

/-- A precondition: a predicate on the STARTING word. -/
abbrev WPre := Word → Prop

/-- A postcondition: a predicate on the ANSWER and the FINAL word.
Two-state postconditions are `Triple_two_state`'s business, not a
second carrier's. -/
abbrev WPost := Addr32 → Word → Prop

/-- The pointwise order on preconditions — the lattice `Pred(W)` of the
debt object, ordered by "every word satisfying the first satisfies the
second". -/
instance : LE WPre := ⟨fun P P' => ∀ w, P w → P' w⟩

/-- The pointwise order on postconditions. -/
instance : LE WPost := ⟨fun Q Q' => ∀ a w, Q a w → Q' a w⟩

theorem WPre.le_def (P P' : WPre) : (P ≤ P') = ∀ w, P w → P' w := rfl

theorem WPost.le_def (Q Q' : WPost) : (Q ≤ Q') = ∀ a w, Q a w → Q' a w := rfl

/-- Pointwise meet. -/
def WPre.meet (P P' : WPre) : WPre := fun w => P w ∧ P' w

/-- Pointwise meet. -/
def WPost.meet (Q Q' : WPost) : WPost := fun a w => Q a w ∧ Q' a w

/-- Pointwise join. -/
def WPost.join (Q Q' : WPost) : WPost := fun a w => Q a w ∨ Q' a w

/-- The top postcondition — "anything at all", the postcondition whose
weakest precondition is pure termination. -/
def WPost.top : WPost := fun _ _ => True

/-- The bottom postcondition — the impossible one the excluded miracle
is about (§2.N). -/
def WPost.bot : WPost := fun _ _ => False

section Wp

variable (H : Bytes → Addr32)

/-! ## The transformer

One fold over the table, threading the answer history exactly as
`runPFrom` does, with the postcondition consumed at the last answer.
`refused` is what a refusal is worth: `False` for `wp`, `True` for
`wlp`. The put clause is §2.12's shape — the operation's DEFINEDNESS
(here: admission succeeding) conjoined with the postcondition
transported through the operation's effect on the word. -/

/-- The fold. `refused` is the value of every clause the run refuses
at: a dangling operand, a refusing put, an absent load, and the empty
history. Recursion is on the table, whose tail is strictly shorter —
the variant, §3.1. -/
def wpAux (refused : Prop) (env : List Addr32) :
    PProg → WPost → Word → Prop
  | [], Q, w =>
    match env.getLast? with
    | some a => Q a w
    | none => refused
  | .put v t payload refs :: rest, Q, w =>
    match resolveRefs env refs with
    | some rs =>
      match putWord H ⟨v, t, payload, rs⟩ w with
      | .ok (a, w') => wpAux refused (env ++ [a]) rest Q w'
      | .error _ => refused
    | none => refused
  | .load src :: rest, Q, w =>
    match src.resolve env with
    | some a =>
      match Word.find w a with
      | some _ => wpAux refused (env ++ [a]) rest Q w
      | none => refused
    | none => refused

/-- THE WEAKEST PRECONDITION: the words a table runs to completion from,
answering something the postcondition accepts. A refusal is worth
nothing, so this is TOTAL correctness (§2.2). -/
def wp (p : PProg) (Q : WPost) : WPre := wpAux H False [] p Q

/-- THE WEAKEST LIBERAL PRECONDITION: the same fold, with a refusal
worth everything. Partial correctness (§2.9). -/
def wlp (p : PProg) (Q : WPost) : WPre := wpAux H True [] p Q

/-! ## The characterization — the fold IS the run's outcome

The workhorse. Every law below is read off it, so no law is proved by
a second induction over the table. -/

/-- The fold, characterized by the run it mirrors: at a completed run
the transformer is the postcondition at the answer and the final word;
at a refused run it is the refusal value. -/
theorem wpAux_iff (refused : Prop) (env : List Addr32) (p : PProg)
    (Q : WPost) (w : Word) :
    wpAux H refused env p Q w
      ↔ (match runPFrom H env p w with
         | (.done a, w') => Q a w'
         | _ => refused) := by
  induction p generalizing env w with
  | nil =>
    cases hg : env.getLast? with
    | none => simp [wpAux, runPFrom, hg]
    | some a => simp [wpAux, runPFrom, hg]
  | cons line rest ih =>
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => simp [wpAux, runPFrom, hr]
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e => simp [wpAux, runPFrom, hr, hp]
        | ok aw =>
          obtain ⟨a, w'⟩ := aw
          simp only [wpAux, runPFrom, hr, hp]
          exact ih (env ++ [a]) w'
    | load src =>
      cases hs : src.resolve env with
      | none => simp [wpAux, runPFrom, hs]
      | some a =>
        cases hf : Word.find w a with
        | none => simp [wpAux, runPFrom, hs, hf]
        | some n =>
          simp only [wpAux, runPFrom, hs, hf]
          exact ih (env ++ [a]) w

/-- The transformer at a completed run. -/
theorem wpAux_of_done {refused : Prop} {env : List Addr32} {p : PProg}
    {Q : WPost} {w w' : Word} {a : Addr32}
    (h : runPFrom H env p w = (.done a, w')) :
    wpAux H refused env p Q w ↔ Q a w' := by
  simp [wpAux_iff, h]

/-- The transformer at a refused run — the ONE place `wp` and `wlp`
differ. -/
theorem wpAux_of_refused {refused : Prop} {env : List Addr32} {p : PProg}
    {Q : WPost} {w w' : Word} {r : Refusal}
    (h : runPFrom H env p w = (.refused r, w')) :
    wpAux H refused env p Q w ↔ refused := by
  simp [wpAux_iff, h]

/-- `wp`, by the run. -/
theorem wp_iff (p : PProg) (Q : WPost) (w : Word) :
    wp H p Q w
      ↔ (match runP H p w with
         | (.done a, w') => Q a w'
         | _ => False) :=
  wpAux_iff H False [] p Q w

/-- `wlp`, by the run. -/
theorem wlp_iff (p : PProg) (Q : WPost) (w : Word) :
    wlp H p Q w
      ↔ (match runP H p w with
         | (.done a, w') => Q a w'
         | _ => True) :=
  wpAux_iff H True [] p Q w

/-- A run is done or refused and never running (`runPFrom_halts`), in
the shape the case analyses below consume. -/
theorem runPFrom_halted (env : List Addr32) (p : PProg) (w : Word) :
    (∃ a w', runPFrom H env p w = (.done a, w'))
      ∨ (∃ r w', runPFrom H env p w = (.refused r, w')) := by
  have hh := runPFrom_halts H env p w
  cases hs : runPFrom H env p w with
  | mk st w' =>
    cases st with
    | done a => exact Or.inl ⟨a, w', rfl⟩
    | refused r => exact Or.inr ⟨r, w', rfl⟩
    | running q => rw [hs] at hh; simp [Status.isRunning] at hh

/-- The same, at the table's own run. -/
theorem runP_done_or_refused (p : PProg) (w : Word) :
    (∃ a w', runP H p w = (.done a, w')) ∨ (∃ r w', runP H p w = (.refused r, w')) :=
  runPFrom_halted H [] p w

/-- `wp` at a completed run. -/
theorem wp_of_done {p : PProg} {Q : WPost} {w w' : Word} {a : Addr32}
    (h : runP H p w = (.done a, w')) : wp H p Q w ↔ Q a w' :=
  wpAux_of_done H h

/-- `wp` at a refused run: nothing is established. -/
theorem wp_of_refused {p : PProg} {Q : WPost} {w w' : Word} {r : Refusal}
    (h : runP H p w = (.refused r, w')) : wp H p Q w ↔ False :=
  wpAux_of_refused H h

/-- `wlp` at a completed run — the same clause as `wp`. -/
theorem wlp_of_done {p : PProg} {Q : WPost} {w w' : Word} {a : Addr32}
    (h : runP H p w = (.done a, w')) : wlp H p Q w ↔ Q a w' :=
  wpAux_of_done H h

/-- `wlp` at a refused run: everything is established. This single pair
of clauses IS the §2.9 distinction. -/
theorem wlp_of_refused {p : PProg} {Q : WPost} {w w' : Word} {r : Refusal}
    (h : runP H p w = (.refused r, w')) : wlp H p Q w ↔ True :=
  wpAux_of_refused H h

/-- `wp` in existential form — the shape the anchor is stated in. -/
theorem wp_iff_exists (p : PProg) (Q : WPost) (w : Word) :
    wp H p Q w ↔ ∃ a w', runP H p w = (.done a, w') ∧ Q a w' := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · rw [wp_of_done H hs]
    refine ⟨fun h => ⟨a, w', hs, h⟩, fun h => ?_⟩
    obtain ⟨b, w'', hb, hq⟩ := h
    rw [hs] at hb
    simp only [Prod.mk.injEq, Status.done.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact hq
  · rw [wp_of_refused H hs]
    refine ⟨False.elim, fun h => ?_⟩
    obtain ⟨b, w'', hb, _⟩ := h
    rw [hs] at hb
    simp at hb

/-- `wlp` in universal form: it says nothing whatever about a refusing
run — by construction, and matching the bridge, which carries no word
on the refusal side (`Handler.lean:106-113`). -/
theorem wlp_iff_forall (p : PProg) (Q : WPost) (w : Word) :
    wlp H p Q w ↔ ∀ a w', runP H p w = (.done a, w') → Q a w' := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · rw [wlp_of_done H hs]
    refine ⟨fun h b w'' hb => ?_, fun h => h a w' hs⟩
    rw [hs] at hb
    simp only [Prod.mk.injEq, Status.done.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact h
  · rw [wlp_of_refused H hs]
    refine ⟨fun _ b w'' hb => ?_, fun _ => trivial⟩
    rw [hs] at hb
    simp at hb

/-! ## The algebra

Each law is a theorem; the packet's falsification equation for each is
the counter-`example` of the same name where one exists. -/

/-- **L3 — MONOTONICITY** (§2.3): a weaker postcondition has a weaker
precondition. -/
theorem wp_mono {Q Q' : WPost} (hq : Q ≤ Q') (p : PProg) :
    wp H p Q ≤ wp H p Q' := by
  intro w hw
  obtain ⟨a, w', hs, hq'⟩ := (wp_iff_exists H p Q w).mp hw
  exact (wp_iff_exists H p Q' w).mpr ⟨a, w', hs, hq a w' hq'⟩

/-- Monotonicity for `wlp`, by the same argument on the other side of
the quantifier. -/
theorem wlp_mono {Q Q' : WPost} (hq : Q ≤ Q') (p : PProg) :
    wlp H p Q ≤ wlp H p Q' := by
  intro w hw
  exact (wlp_iff_forall H p Q' w).mpr fun a w' hs =>
    hq a w' ((wlp_iff_forall H p Q w).mp hw a w' hs)

/-- **L4 — CONJUNCTIVITY**, as an equivalence. -/
theorem wp_and (p : PProg) (Q Q' : WPost) (w : Word) :
    wp H p (WPost.meet Q Q') w ↔ (wp H p Q w ∧ wp H p Q' w) := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wp_of_done H hs, WPost.meet]
  · simp only [wp_of_refused H hs, and_self]

/-- **L4 — CONJUNCTIVITY**, as an equality of transformers. The
carrier's determinism is what makes the hard direction hold: a table
has ONE outcome at a word, so two postconditions established separately
are established together. -/
theorem wp_meet (p : PProg) (Q Q' : WPost) :
    wp H p (WPost.meet Q Q') = WPre.meet (wp H p Q) (wp H p Q') := by
  funext w
  exact propext (wp_and H p Q Q' w)

/-- **L5 — UNIVERSAL CONJUNCTIVITY**, over a NONEMPTY family. The
hypothesis is not decoration: `falsifier_empty_family` exhibits the
empty family, where the law fails (§2.9's empty-family identity). -/
theorem wp_forall {ι : Type} (hι : Nonempty ι) (p : PProg) (Q : ι → WPost)
    (w : Word) :
    wp H p (fun a w' => ∀ i, Q i a w') w ↔ ∀ i, wp H p (Q i) w := by
  obtain ⟨i₀⟩ := hι
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wp_of_done H hs]
  · simp only [wp_of_refused H hs]
    exact ⟨False.elim, fun h => h i₀⟩

/-- **L6 — DISJUNCTIVITY**. True at this rung BECAUSE the carrier is
deterministic and total; it is a fact about `CasSig` tables, not about
effectful computation in general. The claim-scope line names where it
would break, and the estate already exhibits that boundary
(`Defun.lean`'s closing counter-witness: one program, two oracles, two
answer histories). -/
theorem wp_or (p : PProg) (Q Q' : WPost) (w : Word) :
    wp H p (WPost.join Q Q') w ↔ (wp H p Q w ∨ wp H p Q' w) := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wp_of_done H hs, WPost.join]
  · simp only [wp_of_refused H hs, or_self]

/-- **L7 — THE LAW OF THE EXCLUDED MIRACLE** (§2.N): no table
establishes the impossible postcondition from any word. -/
theorem wp_bot (p : PProg) (w : Word) : ¬ wp H p WPost.bot w := by
  intro h
  obtain ⟨_, _, _, hq⟩ := (wp_iff_exists H p WPost.bot w).mp h
  exact hq

/-- The liberal transformer's empty-family identity (§2.9): `wlp` of
`true` is `true`, at every table and every word. Its `wp` counterpart
is FALSE — that is the whole distinction, and
`falsifier_wlp_ne_wp` exhibits it. -/
theorem wlp_top (p : PProg) (w : Word) : wlp H p WPost.top w :=
  (wlp_iff_forall H p WPost.top w).mpr fun _ _ _ => trivial

/-- **L9 — THE CONSERVATIVE DECOMPOSITION** (§2.9):
`WP[S,Q] = WLP[S,Q] ∧ WP[S,true]`. The second conjunct is the separate
obligation the book insists on — here it is exactly "the run does not
refuse". -/
theorem wp_iff_wlp_and_total (p : PProg) (Q : WPost) (w : Word) :
    wp H p Q w ↔ (wlp H p Q w ∧ wp H p WPost.top w) := by
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · simp only [wp_of_done H hs, wlp_of_done H hs, WPost.top, and_true]
  · simp only [wp_of_refused H hs, wlp_of_refused H hs]
    exact ⟨False.elim, And.right⟩

/-! ### L8 — sequential composition, and the unit that is not one

The book's §2.6 law pulls the goal backward through the second
statement first. On tables the second statement runs at a HISTORY, and
the history is the one the prefix DETERMINED — `PProg.answersFrom`,
which `runPFrom_append_done` already identifies for the run. Composing
at a restarted history is a different (and wrong) transformer;
`falsifier_append_needs_history` exhibits the difference.

The law needs a side condition, and finding out why is the packet's
break: `runPFrom` refuses an empty table at an empty history, so the
empty table is NOT a unit of composition. The hypothesis
`env ≠ [] ∨ pre ≠ []` is the honest statement, and
`falsifier_empty_prefix` is the witness that nothing weaker will do. -/

/-! The walker's clauses, named. `Defun.lean` exports the two load
clauses (`runPFrom_load_absent`, `runPFrom_load_present`) and no put
clause; the three below complete the set at the shape the induction
consumes, so no proof has to unfold the walker in a goal whose tail is
an append. -/

/-- Clause: a put whose operands dangle. -/
theorem runPFrom_put_dangling {env : List Addr32} {v t : UInt8}
    {payload : Bytes} {refs : List (UInt8 × PIn)} {rest : PProg} {w : Word}
    (hr : resolveRefs env refs = none) :
    runPFrom H env (.put v t payload refs :: rest) w
      = (.refused (.failed "defun: dangling answer index"), w) := by
  simp [runPFrom, hr]

/-- Clause: a put the store refuses. -/
theorem runPFrom_put_error {env : List Addr32} {v t : UInt8} {payload : Bytes}
    {refs : List (UInt8 × PIn)} {rs : List Ref} {rest : PProg} {w : Word}
    {e : Refusal} (hr : resolveRefs env refs = some rs)
    (hp : putWord H ⟨v, t, payload, rs⟩ w = .error e) :
    runPFrom H env (.put v t payload refs :: rest) w = (.refused e, w) := by
  simp [runPFrom, hr, hp]

/-- Clause: a put the store admits — the run continues at the answered
address and the store's word. -/
theorem runPFrom_put_ok {env : List Addr32} {v t : UInt8} {payload : Bytes}
    {refs : List (UInt8 × PIn)} {rs : List Ref} {rest : PProg} {w w' : Word}
    {a : Addr32} (hr : resolveRefs env refs = some rs)
    (hp : putWord H ⟨v, t, payload, rs⟩ w = .ok (a, w')) :
    runPFrom H env (.put v t payload refs :: rest) w
      = runPFrom H (env ++ [a]) rest w' := by
  simp [runPFrom, hr, hp]

/-- Clause: a load whose operand dangles. -/
theorem runPFrom_load_dangling {env : List Addr32} {src : PIn} {rest : PProg}
    {w : Word} (hs : src.resolve env = none) :
    runPFrom H env (.load src :: rest) w
      = (.refused (.failed "defun: dangling answer index"), w) := by
  simp [runPFrom, hs]

/-- A refusal inside a prefix is a refusal of the whole table, at the
same reason and the same word — PROVIDED the prefix is a real prefix.
At `env = []` and `pre = []` the empty-program refusal is not stable
under extension, which is exactly the break. -/
theorem runPFrom_append_refused :
    ∀ (env : List Addr32) (pre post : PProg) (w : Word) {r : Refusal} {w' : Word},
      (env ≠ [] ∨ pre ≠ []) →
      runPFrom H env pre w = (.refused r, w') →
        runPFrom H env (pre ++ post) w = (.refused r, w') := by
  intro env pre
  induction pre generalizing env with
  | nil =>
    intro post w r w' hne h
    rcases hne with hne | hne
    · cases hg : env.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
      | some c => simp [runPFrom, hg] at h
    · exact absurd rfl hne
  | cons l rest ih =>
    intro post w r w' _ h
    rw [List.cons_append]
    cases l with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none =>
        rw [runPFrom_put_dangling H hr] at h
        rw [runPFrom_put_dangling H hr]
        exact h
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e =>
          rw [runPFrom_put_error H hr hp] at h
          rw [runPFrom_put_error H hr hp]
          exact h
        | ok aw =>
          obtain ⟨c, w''⟩ := aw
          rw [runPFrom_put_ok H hr hp] at h
          rw [runPFrom_put_ok H hr hp]
          exact ih (env ++ [c]) post w'' (Or.inl (by simp)) h
    | load src =>
      cases hs : src.resolve env with
      | none =>
        rw [runPFrom_load_dangling H hs] at h
        rw [runPFrom_load_dangling H hs]
        exact h
      | some c =>
        cases hf : Word.find w c with
        | none =>
          rw [runPFrom_load_absent H env src rest w hs hf] at h
          rw [runPFrom_load_absent H env src (rest ++ post) w hs hf]
          exact h
        | some n =>
          rw [runPFrom_load_present H env src rest w hs hf] at h
          rw [runPFrom_load_present H env src (rest ++ post) w hs hf]
          exact ih (env ++ [c]) post w (Or.inl (by simp)) h

/-- **L8 — SEQUENTIAL COMPOSITION**: the transformer of a longer table
is the transformer of its prefix applied to the transformer of its
suffix, at the history the prefix determines. Stated for `wpAux`, so it
holds for `wp` and `wlp` at once. -/
theorem wpAux_append (refused : Prop) (env : List Addr32) (pre post : PProg)
    (Q : WPost) (w : Word) (hne : env ≠ [] ∨ pre ≠ []) :
    wpAux H refused env (pre ++ post) Q w
      ↔ wpAux H refused env pre
          (fun _ w' => wpAux H refused (env ++ PProg.answersFrom H env pre) post Q w') w := by
  rcases runPFrom_halted H env pre w with ⟨b, w', hs⟩ | ⟨r, w', hs⟩
  · calc wpAux H refused env (pre ++ post) Q w
        ↔ (match runPFrom H env (pre ++ post) w with
           | (.done a, w'') => Q a w''
           | _ => refused) := wpAux_iff H refused env (pre ++ post) Q w
      _ ↔ (match runPFrom H (env ++ PProg.answersFrom H env pre) post w' with
           | (.done a, w'') => Q a w''
           | _ => refused) := by
            rw [runPFrom_append_done H env pre post w hs]
      _ ↔ wpAux H refused (env ++ PProg.answersFrom H env pre) post Q w' :=
            (wpAux_iff H refused _ post Q w').symm
      _ ↔ wpAux H refused env pre
            (fun _ w' => wpAux H refused (env ++ PProg.answersFrom H env pre) post Q w') w :=
            (wpAux_of_done
              (Q := fun _ w' =>
                wpAux H refused (env ++ PProg.answersFrom H env pre) post Q w') H hs).symm
  · rw [wpAux_of_refused H (runPFrom_append_refused H env pre post w hne hs),
      wpAux_of_refused H hs]

/-- **L8 at the table** — `wp` of an extended table, composed. The
prefix must be non-empty: `falsifier_empty_prefix` is the counter-
example at `pre = []`. -/
theorem wp_append (pre post : PProg) (Q : WPost) (w : Word) (hpre : pre ≠ []) :
    wp H (pre ++ post) Q w
      ↔ wp H pre
          (fun _ w' => wpAux H False (PProg.answersFrom H [] pre) post Q w') w := by
  have h := wpAux_append H False [] pre post Q w (Or.inr hpre)
  simpa [wp] using h

/-- TABLE EXTENSION, the corollary a scheduler wants: whatever an
extended table establishes, its prefix at least COMPLETES. Extending a
table only strengthens its precondition. -/
theorem wp_append_le_total (pre post : PProg) (Q : WPost) (hpre : pre ≠ []) :
    wp H (pre ++ post) Q ≤ wp H pre WPost.top := by
  intro w hw
  have h := (wp_append H pre post Q w hpre).mp hw
  exact wp_mono H (by intro _ _ _; trivial) pre w h

/-! ## The anchor -/

/-- THE TRIPLE, over the fueled run (§2.2 total correctness): from every
starting word the precondition admits, the table's run HALTS DONE and
its answer and final word satisfy the postcondition. Refusal is
excluded by `done`; divergence is excluded by the carrier
(`runP_halts`), which is why this rung can afford total correctness at
all. -/
def Triple (p : PProg) (P : WPre) (Q : WPost) : Prop :=
  ∀ w, P w → ∃ a w', runP H p w = (.done a, w') ∧ Q a w'

/-- The partial-correctness triple, for contrast: it promises nothing
about refusal. `falsifier_partial_is_not_total` separates the two. -/
def PartialTriple (p : PProg) (P : WPre) (Q : WPost) : Prop :=
  ∀ w, P w → ∀ a w', runP H p w = (.done a, w') → Q a w'

/-- **L1 — THE ANCHOR**, both directions. Soundness (`→`) and
completeness (`←`): the triple holds exactly when the precondition
entails the weakest one. Completeness is available here — and only
here — because the carrier is total: there is no fuel hypothesis to
discharge, the fuel being a conclusion the table's length supplies
(`Triple_run`). -/
theorem Triple_iff_wp (p : PProg) (P : WPre) (Q : WPost) :
    Triple H p P Q ↔ P ≤ wp H p Q := by
  simp only [Triple, WPre.le_def]
  exact ⟨fun h w hw => (wp_iff_exists H p Q w).mpr (h w hw),
    fun h w hw => (wp_iff_exists H p Q w).mp (h w hw)⟩

/-- The partial triple's anchor is `wlp`, by the same reading. -/
theorem PartialTriple_iff_wlp (p : PProg) (P : WPre) (Q : WPost) :
    PartialTriple H p P Q ↔ P ≤ wlp H p Q := by
  simp only [PartialTriple, WPre.le_def]
  exact ⟨fun h w hw => (wlp_iff_forall H p Q w).mpr (h w hw),
    fun h w hw => (wlp_iff_forall H p Q w).mp (h w hw)⟩

/-- TWO-STATE POSTCONDITIONS, without a second carrier: the starting
word enters as a logical variable, by instantiating the precondition at
it (§2.3 — "use fresh logical variables when updates overwrite
information"). This is the estate's `old`.

Note the quantifier: this is the two-state reading at a UNIVERSAL
starting word, which is the two-state triple at precondition `⊤`. The
form the debt object's `σ` actually asks for — two-state RELATIVE to a
precondition — is `Triple_two_state_rel` below. -/
theorem Triple_two_state (p : PProg) (R : Word → Addr32 → Word → Prop) :
    (∀ w₀, Triple H p (fun w => w = w₀) (fun a w' => R w₀ a w'))
      ↔ ∀ w₀, ∃ a w', runP H p w₀ = (.done a, w') ∧ R w₀ a w' := by
  refine ⟨fun h w₀ => h w₀ w₀ rfl, fun h w₀ w hw => ?_⟩
  subst hw
  exact h w

/-- THE TWO-STATE TRIPLE, RELATIVE TO A PRECONDITION — the form the
debt object's `σ` asks for: a two-state postcondition over the starting
words `P` admits, rather than over all of them.

Proved first by the independent breaker, who found that
`Triple_two_state` covers only `P = ⊤` and derived this in three lines
rather than filing the gap (attack record
`library/cas/contracts/attacks/PDD-2/Attack.lean` §6, branch
`attack/opus-cc-mac/pdd-2`, commit `c6f74608`, NOTE-4). Adopted here
with credit, because a public theorem belongs in the module its
statement is about. -/
theorem Triple_two_state_rel (p : PProg) (P : WPre)
    (R : Word → Addr32 → Word → Prop) :
    (∀ w₀, P w₀ → Triple H p (fun w => w = w₀) (fun a w' => R w₀ a w'))
      ↔ ∀ w₀, P w₀ → ∃ a w', runP H p w₀ = (.done a, w') ∧ R w₀ a w' := by
  refine ⟨fun h w₀ hp => h w₀ hp w₀ rfl, fun h w₀ hp w hw => ?_⟩
  subst hw
  exact h w hp

/-- **L10 — THE VARIANT, DISCHARGED WITH A NUMBER.** A triple's run is
the embedded program's run at fuel `p.length + 1` — "enough fuel" is a
conclusion the table's own length supplies, never a hypothesis.
`falsifier_fuel_bound_is_tight` shows the bound is exact. -/
theorem Triple_run (p : PProg) (P : WPre) (Q : WPost) (h : Triple H p P Q)
    (w : Word) (hw : P w) :
    ∃ a w', run H (p.length + 1) (embed p) w = (.done a, w') ∧ Q a w' := by
  obtain ⟨a, w', hs, hq⟩ := h w hw
  exact ⟨a, w', by rw [runP_embed_agree]; exact hs, hq⟩

/-- **L2 — THE ANCHOR AT THE BIG-STEP JUDGMENT.** The same transformer,
read against the denotation `interpretRef` of the table's embedding.
The two judgments are one semantics (R10's bridge), so choosing the
table as the carrier costs no generality: everything above is equally a
statement about the reference handler's meaning. -/
theorem wp_iff_interpretRef (p : PProg) (Q : WPost) (w : Word) :
    wp H p Q w ↔ ∃ a w', interpretRef H (embed p) w = .ok (a, w') ∧ Q a w' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, w', hs, hq⟩ := (wp_iff_exists H p Q w).mp h
    refine ⟨a, w', ?_, hq⟩
    exact interpretRef_of_run_done H (p.length + 1)
      (by rw [runP_embed_agree]; exact hs)
  · obtain ⟨a, w', hi, hq⟩ := h
    rcases runP_done_or_refused H p w with ⟨b, w'', hs⟩ | ⟨r, w'', hs⟩
    · have hb : interpretRef H (embed p) w = .ok (b, w'') :=
        interpretRef_of_run_done H (p.length + 1)
          (by rw [runP_embed_agree]; exact hs)
      rw [hi] at hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact (wp_iff_exists H p Q w).mpr ⟨_, _, hs, hq⟩
    · have hb : interpretRef H (embed p) w = .error r :=
        interpretRef_of_run_refused H (p.length + 1)
          (by rw [runP_embed_agree]; exact hs)
      rw [hi] at hb
      simp at hb

/-- The triple, against the big-step judgment. -/
theorem Triple_iff_interpretRef (p : PProg) (P : WPre) (Q : WPost) :
    Triple H p P Q
      ↔ ∀ w, P w → ∃ a w', interpretRef H (embed p) w = .ok (a, w') ∧ Q a w' := by
  simp only [Triple_iff_wp, WPre.le_def]
  exact ⟨fun h w hw => (wp_iff_interpretRef H p Q w).mp (h w hw),
    fun h w hw => (wp_iff_interpretRef H p Q w).mpr (h w hw)⟩

/-! ## L11 — the transformer computes

The same fold at `Bool`: for a decidable postcondition the weakest
precondition of a concrete table is COMPUTED, which is A2's
"mechanical verification-condition generation for free". The agreement
theorem is what makes the computed verdict a statement about `wp` and
not merely about a second program. -/

/-- The computed transformer. `false` at every refusing clause — this
is `wp`, not `wlp`. -/
def wpB (env : List Addr32) :
    PProg → (Addr32 → Word → Bool) → Word → Bool
  | [], Q, w =>
    match env.getLast? with
    | some a => Q a w
    | none => false
  | .put v t payload refs :: rest, Q, w =>
    match resolveRefs env refs with
    | some rs =>
      match putWord H ⟨v, t, payload, rs⟩ w with
      | .ok (a, w') => wpB (env ++ [a]) rest Q w'
      | .error _ => false
    | none => false
  | .load src :: rest, Q, w =>
    match src.resolve env with
    | some a =>
      match Word.find w a with
      | some _ => wpB (env ++ [a]) rest Q w
      | none => false
    | none => false

/-- The computed transformer is characterized by the same run. -/
theorem wpB_iff (env : List Addr32) (p : PProg) (Q : Addr32 → Word → Bool)
    (w : Word) :
    wpB H env p Q w = true
      ↔ (match runPFrom H env p w with
         | (.done a, w') => Q a w' = true
         | _ => False) := by
  induction p generalizing env w with
  | nil =>
    cases hg : env.getLast? with
    | none => simp [wpB, runPFrom, hg]
    | some a => simp [wpB, runPFrom, hg]
  | cons line rest ih =>
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => simp [wpB, runPFrom, hr]
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e => simp [wpB, runPFrom, hr, hp]
        | ok aw =>
          obtain ⟨a, w'⟩ := aw
          simp only [wpB, runPFrom, hr, hp]
          exact ih (env ++ [a]) w'
    | load src =>
      cases hs : src.resolve env with
      | none => simp [wpB, runPFrom, hs]
      | some a =>
        cases hf : Word.find w a with
        | none => simp [wpB, runPFrom, hs, hf]
        | some n =>
          simp only [wpB, runPFrom, hs, hf]
          exact ih (env ++ [a]) w

/-- **L11 — THE COMPUTED VERDICT IS THE STATED TRANSFORMER.** What the
`#guard` and `#eval` batteries below decide is `wp`, not a lookalike. -/
theorem wpB_iff_wp (p : PProg) (Q : Addr32 → Word → Bool) (w : Word) :
    wpB H [] p Q w = true ↔ wp H p (fun a w' => Q a w' = true) w := by
  rw [wpB_iff, wp_iff, runP]

end Wp

/-! ## The falsifiers

The packet's falsification equations, exhibited. Each `example` names
the law it kills; between them they say exactly where the algebra above
stops. The address functions are toy — a hash is not needed to decide
any of these, and the estate's law keeps digest computation out of the
kernel. -/

namespace Falsifier

/-- The all-zero address: the literal these witnesses load. -/
def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- A toy address function separating nodes by their encoded length —
enough for the witnesses, and no digest in the kernel. -/
def lenAddr : Bytes → Addr32 :=
  fun bs => ⟨List.replicate 32 (UInt8.ofNat bs.length), by simp⟩

/-- A table that loads an address no empty word holds: the refusing
witness the WLP distinction needs. -/
def absentLoad : PProg := [.load (.lit zeroAddr)]

/-- A put with no operands: the smallest completing line. -/
def putA : PLine := .put 0 0 [] []

/-- A put naming the previous line's answer, at the kind tag that line
admitted — the reference discipline a registered program uses. -/
def putB : PLine := .put 0 1 [] [(0, .ans 0)]

/-- One put, no operands: the smallest completing table. -/
def onePut : PProg := [putA]

/-- Two puts, the second naming the first by answer index — the shape
`encodeProg` lays a registered program down in. -/
def chained : PProg := [putA, putB]

/-- **FALSIFIER for L3's converse.** `wp` is monotone but not faithful:
the empty table's transformer is constantly `⊥`, so it orders every
pair of postconditions the same way. This is why the anchor is stated
as `P ≤ wp p Q` and never as an equality of postconditions — a
transformer inequality carries no information about `Q`. -/
theorem falsifier_wp_not_faithful :
    ∃ (H : Bytes → Addr32) (p : PProg) (Q Q' : WPost),
      wp H p Q ≤ wp H p Q' ∧ ¬ (Q ≤ Q') := by
  refine ⟨lenAddr, [], WPost.top, WPost.bot, ?_, ?_⟩
  · intro w hw
    exact absurd hw (by simp [wp, wpAux])
  · intro h
    exact (h zeroAddr [] trivial)

/-- **FALSIFIER for L5 at the empty family** (§2.9's empty-family
identity). Over an empty index type the right-hand side is vacuously
true and the left-hand side asks the table to complete — which the
refusing witness does not. The `Nonempty` hypothesis in `wp_forall` is
load-bearing. -/
theorem falsifier_empty_family :
    ∃ (H : Bytes → Addr32) (p : PProg) (Q : Empty → WPost) (w : Word),
      (∀ i, wp H p (Q i) w) ∧ ¬ wp H p (fun a w' => ∀ i, Q i a w') w := by
  refine ⟨lenAddr, absentLoad, fun i => i.elim, [], fun i => i.elim, ?_⟩
  simp [wp, wpAux, absentLoad, PIn.resolve]

/-- **FALSIFIER for L8 at a restarted history.** Composing the suffix at
the EMPTY history rather than the determined one is a different
transformer: the second line's answer operand dangles where the
threaded history resolves it. The `PProg.answersFrom` in `wp_append` is
not decoration. -/
theorem falsifier_append_needs_history :
    ∃ (H : Bytes → Addr32) (pre post : PProg) (w : Word),
      wp H (pre ++ post) WPost.top w
        ∧ ¬ wp H pre (fun _ w' => wp H post WPost.top w') w := by
  refine ⟨lenAddr, [putA], [putB], [], ?_, ?_⟩
  · show wp lenAddr ([putA] ++ [putB]) WPost.top []
    exact trivial
  · intro h
    exact h

/-- **FALSIFIER for L8 AS THE PACKET FIRST STATED IT — the break.**
The empty table is NOT a unit of composition, so no unconditional
composition law is available: `[] ++ post` runs `post`, while
`wp H []` is the constant `⊥`, because `runPFrom` refuses an empty
table at an empty history ("defun: empty program"). The law survives
with the hypothesis `pre ≠ []` (`wp_append`), and this witness is why
that hypothesis is not slack. Recorded in the packet's break ledger. -/
theorem falsifier_empty_prefix :
    ∃ (H : Bytes → Addr32) (post : PProg) (Q : WPost) (w : Word),
      wp H ([] ++ post) Q w
        ∧ ¬ wp H [] (fun _ w' =>
              wpAux H False (PProg.answersFrom H [] []) post Q w') w := by
  refine ⟨lenAddr, onePut, WPost.top, [], ?_, ?_⟩
  · show wp lenAddr ([] ++ onePut) WPost.top []
    exact trivial
  · intro h
    exact h

/-- **FALSIFIER for L9 — the WLP distinction, with its witness
program.** At a word that does not hold the loaded address the run
refuses, and there `wlp` of the IMPOSSIBLE postcondition is true while
`wp` of the trivial one is false. Both of §2.9's rows —
`WLP[S,true] == true` and `WP[assert false,true] == false` — in one
table. -/
theorem falsifier_wlp_ne_wp :
    ∃ (H : Bytes → Addr32) (p : PProg) (w : Word),
      wlp H p WPost.bot w ∧ ¬ wp H p WPost.top w := by
  refine ⟨lenAddr, absentLoad, [], ?_, ?_⟩
  · simp [wlp, wpAux, absentLoad, PIn.resolve]
  · simp [wp, wpAux, absentLoad, PIn.resolve]

/-- **FALSIFIER for L1 weakened to partial correctness** (§3.0: total
correctness is value correctness AND termination). The refusing table
satisfies every partial triple and no total one, so the anchor cannot
be restated over `PartialTriple`. -/
theorem falsifier_partial_is_not_total :
    ∃ (H : Bytes → Addr32) (p : PProg) (P : WPre) (Q : WPost),
      PartialTriple H p P Q ∧ ¬ Triple H p P Q := by
  refine ⟨lenAddr, absentLoad, fun w => w = [], WPost.bot, ?_, ?_⟩
  · intro w hw a w' hs
    subst hw
    simp [runP, runPFrom, absentLoad, PIn.resolve] at hs
  · intro h
    obtain ⟨a, w', hs, _⟩ := h [] rfl
    simp [runP, runPFrom, absentLoad, PIn.resolve] at hs

/-- **FALSIFIER for L10's slack.** The fuel `p.length + 1` is exact:
one line short and the embedded program is still RUNNING, which is the
status that says nothing at all. The bound is a theorem about the
table, not a constant anyone may round down. -/
theorem falsifier_fuel_bound_is_tight :
    ∃ (H : Bytes → Addr32) (p : PProg) (w : Word),
      (run H p.length (embed p) w).1.isRunning = true
        ∧ (runP H p w).1.isDone = true := by
  refine ⟨lenAddr, onePut, [], ?_, ?_⟩ <;> rfl

end Falsifier

/-! ## The battery — the transformer, computed

A registered-program-shaped table (puts alone, the second naming the
first by answer index) with a decidable postcondition: two bindings in
the final word and the answer being the second put's address. `#guard`
decides it in the kernel at the toy address function; the `#eval`
below is the same verdict at the production digest, as a build-time IO
assert — this lane's law is that digest computation runs in `#eval`,
never in kernel `decide`. -/

namespace Battery

open Falsifier

/-- The postcondition, decidable: the run admitted exactly two bindings
and answered the last one's address. -/
def twoBindings : Addr32 → Word → Bool :=
  fun a w => w.length == 2 && (w.getLast?.map Binding.address == some a)

-- The kernel-decided verdict at the toy address function.
#guard wpB lenAddr [] chained twoBindings [] = true

/-- The same verdict, at the production digest, as a build-time
assert. -/
def check : IO Unit := do
  unless wpB Cas.sha256Addr [] chained twoBindings [] do
    throw (IO.userError
      "PDD-2 battery: the computed wp of the chained table is false")
  unless !(wpB Cas.sha256Addr [] absentLoad (fun _ _ => true) []) do
    throw (IO.userError
      "PDD-2 battery: the refusing table's computed wp is not false")
  IO.println
    "PDD-2: computed wp green — chained table admits two bindings, refusing table's wp is false"

#eval check

end Battery

end Cas.Lang
