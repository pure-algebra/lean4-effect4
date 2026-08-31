# PDD-2 — the contract packet: `wp` on the program carrier

Ticket: `.staging/wave-1/PDD-2.md`. Process: `.agents/skills/implement/`
(SKILL.md, CONTRACT.md, IMPLEMENTER.md); design basis
`.staging/operational-structure/PROOF-DRIVEN-DEVELOPMENT.md` §2 (the
debt object) and §5 A2. Authored before `Cas/Lang/Wp.lean` exists and
committed ahead of it, so the history carries the order.

CATEGORIES `wp-sp-calculus`, `contracts`, `assertions`, `termination`

CATALOG rows this packet is stated in (`.agents/skills/implement/CATALOG.md`):
§1.1 (assertions are discharged symbolically, never by selected runs),
§2.0 (predicates as sets of states), §2.2 (the total-correctness Hoare
triple), §2.3–§2.4 (the transformer pair; logical variables for
overwritten values), §2.6 (sequential composition pulls the goal
backward through the second statement first), §2.9 (WLP, the
conservative decomposition, the adjoint distributions and the
empty-family identities), §2.12 (definedness conjoined into the
transformer), §2.13 (method correctness), §2.N (the law of the excluded
miracle), §3.0 (total correctness = value correctness + termination),
§3.1 and §3.5 (every recursive edge strictly decreases a nonnegative
metric).

Battery and falsifiers: `library/cas/Cas/Lang/Wp.lean` — the counter-
`example`s named under FALSIFIER below, and the computed-`wp`
demonstration (`#guard` at a toy address function, `#eval` IO assert at
the production digest).

## The degree claimed

I have shown algebraically that this can be implemented to this degree:
a predicate transformer defined by structural recursion over the
defunctionalized table, with monotonicity, finite and universal
conjunctivity, disjunctivity, the excluded miracle, sequential
composition, the WLP decomposition, and the triple/`wp` anchor proved in
both directions (soundness AND completeness) against two judgments — the
direct run `runP` and, through the estate's existing bridge, the
big-step denotation `interpretRef` of the table's embedding. Kernel-
checked, no `sorry`, no new axiom beyond the estate's clean three.

Axiom census, exact (corrected by the breaker's NOTE-1; the summary
this packet first carried said "two" where the answer is six):
`propext` throughout, and `Quot.sound` on six declarations —
`Wp.lean:333` (`wp_meet`), `:341` (`wp_forall`), `:501`
(`wpAux_append`), `:528` (`wp_append`), `:538` (`wp_append_le_total`),
`:866` (`Battery.check`). `wp_forall` is an INDEPENDENT carrier, not
downstream of `wp_meet` or `wpAux_append`; the three `:528`/`:538`
declarations are downstream of `wpAux_append`. No `Classical.choice`,
no `sorryAx`.

## The carrier judgment, chosen and defended

**Chosen: the fueled `runP` on the defunctionalized table
(`Cas/Lang/Defun.lean`), with the big-step denotation
(`Cas/Lang/Handler.lean:95-123`) carried as a proved corollary rather
than as the primary judgment.**

Three reasons, each a fact about the carriers rather than a preference.

1. **The variant is structural here and existential there.** On `Prog`
   the continuations are host functions, so no size exists to quantify
   over and fuel must be PRODUCED (`run_of_interpretRef`,
   Handler.lean:209-245: "enough fuel is a conclusion, not a
   hypothesis"). On the table the measure is the line count, and
   `runP_embed_agree` (Defun.lean:362) fixes the exact bound
   `p.length + 1`. `DECREASES` is therefore discharged with a number,
   not with an existential, and §3.1's obligation — every recursive edge
   strictly decreases a nonnegative metric — is met by the table's own
   tail.
2. **`wp` must COMPUTE, and only first-order content computes.** The
   ticket's decidability requirement is unsatisfiable over `Prog`
   (stratum 2, propositional equality under `funext`, continuations
   opaque). A table is stratum-1 first-order content (R14), so the same
   recursion that defines `wp` as a `Prop` transformer defines it as a
   `Bool` fold — mechanical verification-condition generation, which is
   what A2 promised.
3. **Nothing is lost.** `runP` is total and halted at every table and
   word (`runP_halts`, Defun.lean:403), and the bridge
   (`run_interpretRef_agree`, Handler.lean:255) transports the anchor to
   the big-step judgment at the exact fuel. The anchor is therefore
   proved against BOTH judgments; choosing the table costs no
   generality at this rung and buys the two properties above.

The cost is named, not hidden: the table is the straight-line fragment
(`Fragments.lean`'s lowest rung). Programs outside it — anything with a
host continuation, anything oracled — are outside every theorem in this
packet. See the claim-scope line.

## The headings

```
REQUIRES   The precondition is a predicate on the STARTING word
           (`WPre := Word → Prop`), run-relative by construction: a
           run's meaning is relative to its starting word
           (PROOF-DRIVEN-DEVELOPMENT.md §6.2), so nothing here is
           quantified over all words unless a theorem says so. No
           premise on `H`: every statement holds at the abstract
           address function (CAS-003 discipline).

ENSURES    The postcondition is a predicate on the ANSWER and the
           FINAL word (`WPost := Addr32 → Word → Prop`). `old` — the
           starting word — enters the way §2.3 says an overwritten
           value enters: as a logical variable, by instantiating the
           precondition at it (`Triple_two_state`). No second carrier
           is minted for two-state postconditions.

DECREASES  The table's tail: `wpAux` recurses on `rest`, whose length
           is one less, into `<` on `Nat` (§3.1, §3.5). The fuel that
           discharges the same statement over the embedded program is
           `p.length + 1` exactly (`runP_embed_agree`), and the
           falsifier below shows the bound is tight, not slack.

FRAME      Reads: the addresses the table's operands resolve to.
           Writes: the bindings its put lines admit. Both are already
           theorems on main and are USED, not restated:
           `runP_frame_sound` (Defun.lean:1965) bounds every consulted
           address by the envelope, `runP_puts_sound` (:1672) bounds
           the admitted bindings by the declared puts, and
           `runP_preserves_wf` (:368) says the word stays admitted.
           `wp` adds no footprint of its own — it is a predicate
           transformer, and nothing in this file runs anything.
```

## The laws, each with its falsifier

Notation: `P ≤ P'` is the pointwise order on predicates; `⊤`/`⊥` are the
constant postconditions; `Q ⊓ Q'` and `Q ⊔ Q'` are pointwise meet and
join.

```
LAW  L1  ANCHOR (soundness and completeness).
         Triple H p P Q  ↔  P ≤ wp H p Q,
         where Triple H p P Q says: from every starting word in P the
         run HALTS DONE and its answer and final word satisfy Q
         (§2.2 total correctness; §2.13 method correctness).
FALS L1  exhibit H, p, P, Q with Triple H p P Q and a word w with
         P w and ¬ wp H p Q w — or the converse.
BATT L1  `Triple_iff_wp`; the near-miss is executable as
         `falsifier_partial_is_not_total` (a table, a precondition and
         a postcondition for which the PARTIAL triple holds and the
         total one fails), so the anchor cannot be weakened to
         partial correctness and still be this equivalence.

LAW  L2  ANCHOR AT THE BIG-STEP JUDGMENT.
         wp H p Q w ↔ ∃ a w', interpretRef H (embed p) w = .ok (a, w')
         ∧ Q a w' — the same transformer, read against the denotation,
         at the exact fuel p.length + 1 (R10's bridge).
FALS L2  exhibit p, Q, w where the two judgments disagree: the run
         reports done and the denotation errors, or conversely.
BATT L2  `wp_iff_interpretRef`, `Triple_iff_interpretRef`.

LAW  L3  MONOTONICITY.  Q ≤ Q' → wp H p Q ≤ wp H p Q' (§2.3).
FALS L3  exhibit p, Q ≤ Q' and w with wp H p Q w and ¬ wp H p Q' w.
BATT L3  `wp_mono`. The CONVERSE is false and its counter-example is
         kept: `falsifier_wp_not_faithful` — a table whose transformer
         is constantly ⊥, so wp p Q ≤ wp p Q' holds while Q ≤ Q' fails.
         That is why L1 is stated as P ≤ wp and never as an equality
         of postconditions.

LAW  L4  CONJUNCTIVITY.  wp H p (Q ⊓ Q') = wp H p Q ⊓ wp H p Q'
         (§2.9's adjoint distribution, at the meet).
FALS L4  exhibit p, Q, Q', w satisfying both conjuncts on the right and
         failing on the left — which is exactly the claim that the run
         has two outcomes at one word.
BATT L4  `wp_meet` (equality of predicates), `wp_and` (the iff).

LAW  L5  UNIVERSAL CONJUNCTIVITY, over a NONEMPTY family.
         For ι nonempty: wp H p (⨅ i, Q i) = ⨅ i, wp H p (Q i).
FALS L5  exhibit a family for which the two sides differ — and for the
         EMPTY family they do: §2.9's empty-family identity is where
         this law stops.
BATT L5  `wp_forall`; the counter-example `falsifier_empty_family`
         exhibits ι = Empty, a refusing table and a word where the
         right side is vacuously true and the left side is false.

LAW  L6  DISJUNCTIVITY.  wp H p (Q ⊔ Q') = wp H p Q ⊔ wp H p Q'.
         True here BECAUSE the carrier is deterministic and total; the
         law is a fact about `CasSig`, not about effects in general.
FALS L6  exhibit p, Q, Q', w with wp H p (Q ⊔ Q') w and neither
         disjunct — i.e. a table with two outcomes at one word.
BATT L6  `wp_or` (over `WPost.join`). No counter-example exists at
         this rung and the claim-scope line says where one does.

LAW  L7  EXCLUDED MIRACLE.  wp H p ⊥ = ⊥ (§2.N).
FALS L7  exhibit p, w with wp H p (fun _ _ => False) w.
BATT L7  `wp_bot`.

LAW  L8  SEQUENTIAL COMPOSITION / TABLE EXTENSION.
         wp H (pre ++ post) Q
           = wp H pre (fun _ w' => wp-at-the-determined-history post Q w'),
         the history being `PProg.answersFrom H [] pre` — the one
         `runPFrom_append_done` names (§2.6: pull the goal back through
         `post` first, then through `pre`).
FALS L8  exhibit pre, post, Q, w where the two sides differ; in
         particular where composing at a RESTARTED history (the naive
         `wp H pre (fun _ w' => wp H post Q w')`) differs from the
         table's own composition.
BATT L8  `wpAux_append`, `wp_append`; the counter-examples
         `falsifier_append_needs_history` (the restarted history
         dangles where the threaded one resolves) and
         `falsifier_empty_prefix` (see the break ledger).
NOTE L8  BROKEN AS STATED ABOVE. The law is FALSE without a side
         condition and lands with one: `env ≠ [] ∨ pre ≠ []` on
         `wpAux_append`, `pre ≠ []` on `wp_append`. The statement is
         left verbatim here and the break is recorded below, per the
         ledger discipline — the law is not quietly rewritten.

LAW  L9  THE WLP DISTINCTION.
         wp H p Q = wlp H p Q ⊓ wp H p ⊤   (§2.9's conservative
         decomposition), and the two transformers are ONE recursion
         differing only in what a refusal is worth.
FALS L9  exhibit p, Q, w where wp and wlp are indistinguishable at
         every table — i.e. show the refusal path is unobservable.
BATT L9  `wp_iff_wlp_and_total`, `wlp_top`; the witness program
         `falsifier_wlp_ne_wp` — a table that loads an address the
         starting word does not hold, at which `wlp p ⊥` is TRUE and
         `wp p ⊤` is FALSE. Both §2.9 rows ("WLP[S,true] == true",
         "WP[assert false,true] == false") in one witness.

LAW  L10 THE VARIANT IS EXACT.  The embedding halts at fuel
         p.length + 1 and the anchor is stated at that fuel; the bound
         is not slack (§3.1).
FALS L10 exhibit p, w where the run is already halted at fuel
         p.length.
BATT L10 `falsifier_fuel_bound_is_tight` — a one-line table still
         RUNNING at fuel `p.length` and done at `p.length + 1`. The
         falsifier fires against the weaker claim "any fuel ≥ 1 does",
         and that is the point: the bound is a theorem about this
         table, not a constant.

LAW  L11 THE TRANSFORMER COMPUTES.
         wpB H p Q w = true ↔ wp H p (fun a w' => Q a w' = true) w,
         for a Bool-valued postcondition — verification-condition
         generation, decided on the table (A2).
FALS L11 exhibit p, Q, w where the computed verdict and the stated
         transformer disagree.
BATT L11 `wpB_iff_wp`; the demonstration is a registered-program-shaped
         table (puts alone, the second referencing the first by answer
         index — `encodeProg`'s own shape) checked by `#guard` at a toy
         address function and by an `#eval` IO assert at the production
         digest `sha256Addr`, per this lane's law that executable digest
         checks are `#eval` asserts and never kernel `decide`.
```

## Claim-scope — what is NOT claimed

- **Not claimed: anything about host code.** No TypeScript is a proof
  subject here; nothing in this packet moves a generated byte or adds a
  word-equality vector. The transport of these statements to the host
  (an emitted VC generator, a `wp` arm on the verify gate) is A3's
  business and is named, not claimed (estate C5, R14 strata 3–4).
- **Not claimed: completeness over divergent or oracled programs.** The
  anchor is proved at the straight-line table, where `runP` is total.
  For `Prog` with host continuations the fuel stays existential and this
  file proves nothing new about it; for oracled programs the
  determinism L4/L6 depend on is FALSE and the estate's own
  counter-witness is the closing `example` of `Defun.lean` (:2190) —
  one program, two oracles, two answer histories.
- **Not claimed: a refusal-word theorem.** `Triple` says a run halts
  DONE; when it refuses, this packet says nothing about the partial
  word, exactly as the bridge does not (Handler.lean:106-113). `wlp`
  quantifies over `done` outcomes only, by construction.
- **Not claimed: an enforcement arm.** No CLI verb, no MCP tool, no
  gate consumes `wp` yet. A3's decidable menu is untouched.
- **Not claimed: a new sort, kind, or registry row.** Statement
  apparatus in the proof stratum only (decision 2; A1's licence).
- **Not claimed: that this module is in the library's ledgers.**
  `Cas.Lang.Wp` rides its OWN Lake library (`CasWp`,
  `globs = ["Cas.Lang.Wp"]`, in `defaultTargets`), the device
  `CasBackend` already uses. `lake build` kernel-checks every theorem
  here; because the module is outside `Cas`'s import closure it is also
  outside `Walk.libraryImports`, so it is INVISIBLE to the surface,
  obligation and law ledgers — which is exactly why this ticket's
  "moves no bytes" gate holds. Promoting `Cas.Lang.Wp` into that walk
  is a promotion, and a promotion is a ruling. (Added on the breaker's
  NOTE-2: the device was disclosed in the lakefile, the module
  docstring and the commit message, but the packet is the artifact the
  estate reads later, so it belongs here too.)
- **Not claimed: that `wp` is defined on `Prog`.** It is defined on
  `PProg`. The `Prog`-level reading is the corollary L2 and goes
  through `embed`.

## Breaks

The ledger of successful falsifications. A packet with an empty ledger
and a green battery says the laws were never seriously attacked; this
one is not empty.

```
BROKE      fa3b8f8a (the law as this packet stated it at 2029a787;
           the defect is in the LAW, not in an implementation — the
           falsifier fired against L8 before any body satisfied it)
LAW        L8 SEQUENTIAL COMPOSITION / TABLE EXTENSION, verbatim:
           "wp H (pre ++ post) Q
              = wp H pre (fun _ w' => wp-at-the-determined-history
                                        post Q w')"
           — stated unconditionally, for every pre and post.
WITNESS    pre = [], post = [.put 0 0 [] []], Q = ⊤, w = [],
           H = the length-toy address function.
           Left:  wp H ([] ++ post) ⊤ [] — the put is admitted, so
                  this is TRUE.
           Right: wp H [] (…) [] — `runPFrom` refuses an EMPTY table
                  at an EMPTY history (`.failed "defun: empty
                  program"`, Defun.lean:276), so `wp H []` is the
                  constant ⊥ and this is FALSE.
           Exhibited as `Cas.Lang.Falsifier.falsifier_empty_prefix`.
CLASS      adequacy — the spec's own obligation. The law was written
           from the shape of §2.6 rather than from the carrier: the
           empty table is not a unit of composition, because the
           carrier gives it a meaning ("answer the last answer") that
           refuses when there is none. Nothing was wrong with any
           implementation; the packet was.
FIXED-BY   fa3b8f8a — L8 lands weakened, with the side condition
           `env ≠ [] ∨ pre ≠ []` on `wpAux_append` and `pre ≠ []` on
           `wp_append`. The witness stays in the tree as a named
           theorem, and `runPFrom_append_refused` carries the same
           hypothesis for the same reason.
```

What the break is worth beyond this ticket: `PProg` is a MONOID under
`++` and its transformer is NOT a monoid homomorphism — the unit fails.
Anything that composes tables (a scheduler, a fragment splicer, the
lowering in `EmitProg`) inherits the same edge, and it is decidable on
the table, before anything runs. The estate's own `runPFrom_append_done`
(Defun.lean:1887) is stated only for a prefix that COMPLETES, which is
why it never met this case.

A second, smaller finding, recorded rather than filed: `Defun.lean`
exports the two load clauses of the walker (`runPFrom_load_absent`,
`runPFrom_load_present`) and no put clause, so a proof whose table is
an append has to re-derive them. `Wp.lean` names the missing three
(`runPFrom_put_dangling`, `runPFrom_put_error`, `runPFrom_put_ok`)
rather than editing a fenced file. If they belong in `Defun.lean`, that
is a promotion and a promotion is a ruling.

## The attack — the independent breaker's pass

Record: `library/cas/contracts/attacks/PDD-2/` (`Attack.lean`,
`RESULTS.md`) on branch `attack/opus-cc-mac/pdd-2`, commit `c6f74608`.
Verdict **STANDS** — no BREAK, no HOLE; fifteen attack families failed,
seven NOTEs, four of them places where the theorem is STRONGER than the
sentence describing it.

The decisive result runs in the packet's favour and is evidence FOR it,
so it is recorded here rather than left in the attack tree:

```
RESULT     anchor_pins_wp (Attack.lean) — any transformer wp'
           satisfying L1 at every table, precondition and
           postcondition agrees with `wp` POINTWISE. Instantiate the
           anchor at the singleton precondition (· = w) and the
           transformer's value is forced everywhere.
CLASS      adequacy — discharged, not argued. The obligation class the
           whole process turns on ("is Q strong enough that no wrong
           implementation passes?") has NO ROOM in it here: there is
           no wrong-but-passing transformer. The adequacy question
           reduces to whether `Triple` and `runP` say what they should,
           and both are read off the run the estate already trusts.
```

Two amendments were adopted from that pass and are in this document and
in `Wp.lean`:

- **NOTE-1** — the axiom census above is corrected: six `Quot.sound`
  carriers, not two, with `wp_forall` independent. Re-verified here by
  a `#print axioms` sweep over every declaration in the module, not
  copied.
- **NOTE-2** — the Lake-library device now has its claim-scope bullet.
- **NOTE-4** — `Triple_two_state` states the two-state reading at a
  UNIVERSAL starting word, which is the two-state triple at
  precondition `⊤`; the debt object's `σ` asks for it relative to `P`.
  The breaker derived the relative form, and it is ADOPTED into
  `Wp.lean` as `Triple_two_state_rel`, credited in its docstring. The
  breaker proved it first; the packet says so.

NOTE-3, NOTE-5, NOTE-6 and NOTE-7 stand as record in `RESULTS.md` and
are not restated here.
