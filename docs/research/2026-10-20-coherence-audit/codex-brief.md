# Codex brief: test the coherence model, and find what the plan forgets

You are reviewing `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, at
`92c4baff8`. Work in a worktree of your own, cut from that commit. This is a review: commit
nothing, push nothing and merge nothing.

## What we want

The owner and the coordinator wrote one document for the coherence work:
`docs/research/2026-10-20-coherence-audit/coherence.md`. It states a model of a run, a rule for
hand-written code (rule S), one plan in seven steps, and seven decisions. The owner asks two
things of this review:
- Is the model true to the code and to the algebra, and does rule S hold up?
- Does the plan forget anything that an earlier plan still owed?

The second question has a record. When the slices plan replaced an earlier plan, it dropped the
Zarith switch (slice 2.2b part 2) without a word, and nobody noticed for days. So Part A is the
heaviest part of this review.

Four parts, in this order of weight:
- **Part A, the sweep of open items** (about half the effort): every open item of every earlier
  plan, mapped.
- **Part B, truth**: each claim of `coherence.md`, checked against the code.
- **Part C, the model against the algebra and Effect**: where the model or rule S breaks.
- **Part D, the documents**: where the authorities now disagree with the model.

Judge everything by one question: would the owner, reading only `coherence.md`, now act on
something false or miss something owed?

## Read first

`docs/research` is not in your worktree. Read it at
`/Users/pooks/Dev/lean4-effect4/docs/research/`.

1. `AGENTS.md`: the rules and the vocabulary.
2. `docs/research/2026-10-20-coherence-audit/coherence.md`: the document under review.
3. `docs/research/2026-10-20-coherence-audit/orientation.md`: the project's philosophy and the
   owner's words, for judging coherence.
4. `docs/research/2026-10-20-coherence-audit/README.md`: the audit's synthesis, moves M1 to M11.
5. `docs/core/controlled-english.md` §3.7 (the host boundary) and the entries **host**,
   **runtime**, **reactor**, **tape**, **journal**, **host session** and **host protocol**.
6. `docs/core/semantics.md` concept 9, `host-session-protocol`.
7. `docs/core/decisions.md`, rows 97, 361, 381, 391, 405, 408 and 414 to 417.

## Part A: the sweep of open items

Collect every open item from the sources below. Map each one to one of three places in
`coherence.md`: a step of §8, a decision of §9, or nothing. An item mapped to nothing is a finding,
unless a later document dropped it with a reason. Name that document.

The sources, newest first:
1. `docs/research/2026-10-19-quality-review/`, four files:
   - `codex-review/README.md`: findings A1 to A10 and B1 to B5, and the Part C tables with C1's
     branch verdicts;
   - `wave3.md`: seats R1 to R3, E6, the TypeScript JSON move and F1;
   - `receipt-r1-store.md`: O1 to O4;
   - `coherence.md`: the store's model, its §5 on the log and its §6 on R2.
2. `docs/research/2026-10-20-coherence-audit/README.md`: M1 to M11, the evident rows E-1 to E-5,
   and the small instances of §3.6.
3. `docs/research/2026-10-18-slices/README.md`: the lanes (§4), the order (§5), the owner's
   decisions (§7), the rulings (§9) and the hygiene lane H1 to H21 (§10). Its receipts
   in the same folder record what each seat left open.
4. `docs/research/2026-10-17-ocaml-estate-review/plan.md`, including its §6a on `driveFrom`.
5. `docs/research/2026-10-17-session-composition/plan.md`,
   `docs/research/2026-10-17-authoring-and-store/README.md` and `docs/research/2026-10-17-seams/`.
6. `docs/research/2026-10-16-c-interop/README.md` and `docs/research/2026-10-16-ocaml-interop/README.md`.
7. `docs/research/2026-10-15-interop-plan/README.md` and `docs/research/2026-10-15-remaining-work/README.md`.
8. `docs/STATE.md`: "Next, in order" and "What the owner must decide".
9. `docs/core/decisions.md`: every row whose status is open, in whole or in part.
10. `docs/DESIGN-ISSUES.md`: every open DI.
11. `docs/core/system-map.md`: each requirement R1 to R14 whose status is open.

The coordinator also holds these items outside any tracked document. Map them too:
- `make gen-semantics` is paused by the owner (2026-10-19) while the concepts change;
- H12 and H16 of the hygiene lane wait for the owner;
- a draft of `AGENTS.md` waits for the owner's approval;
- typed editing is to become the eleventh concept of `semantics.md`;
- 13 integrated worktrees are to be removed, and the C1 branch verdicts applied;
- the Incremental direction (a general tool for changing computations) is deferred.

Deliver the map as one table: source, item, its place in `coherence.md` (step, decision, or
"missing"), and, for a missing one, a proposed place.

## Part B: truth

Check each claim of `coherence.md` against the code at `92c4baff8`. A claim is a table cell, a
count, a named declaration or a sentence that says how the code behaves. Report each false or
misleading claim with its evidence. Start with these, which carry the most weight:
- §2: the journal's four commands, and which come from the host and which from the tape
  (`Command`, `src/Effect4/Api/Runner.lean`; `NativeDecision`, `src/Effect4/Program/Admit.lean`).
- §3: the wire's fields and the job given to each (`Call`, `Reply`, `Header`,
  `src/Effect4/Api/HostSession.lean`).
- §4: the four limits on what a host may answer.
- §5: the table of runtimes. Is it true that nothing builds a Lean-to-C runtime? Read the C
  interop note first. Does the OCaml engine keep a tape but no host session?
- §6: the seam table, and the count of 15,631 hand lines that restate meaning out of 23,485.
  Re-measure with a command, and re-classify any file you judge differently.
- §7: each of F1 to F8.
- §8: the dependencies between the steps. Name any step that needs a later step.

## Part C: the model against the algebra and Effect

Test the model where it is thinnest. For each question, answer yes or no, with evidence.

1. **Two inputs.** Are the host and the tape the only outside inputs of a run? Check the load
   inputs, `Program.Config` (`src/Effect4/Program/Config.lean`), services and layers, the clock and
   the budget.
2. **A runtime is a host.** §3 says a runtime that runs an application is a host for that
   application's service. Does that hold under Effect's semantics of layers, requirements,
   interruption, scopes and finalizers (rc.112, `vendor/effect-4.0.0-rc.112/src/`)? Where does it
   break?
3. **The protocol from the journal.** Can every message the host protocol needs be derived from
   the journal's host commands? Check asynchronous calls (`awaitingAsync`), delayed cell reads,
   external handles and capabilities, cancellation and abandon.
4. **Rule S at its edges.** Classify each item below under rule S, or show that the rule has no
   place for it:
   - a ppx deriver;
   - hand C bound to OCaml, and Zarith's own C;
   - an opam package as a row's body;
   - a generated file that needs a hand fix, and a hand test;
   - the TypeScript in `harness/truth/session`, and the front of `apps/todo`.
5. **Over-engineering.** Is any part of the plan more than the behaviour needs? Look hardest at the
   platform seam (step 7) and the store as meaning (decision S-1). The owner's rule: elegance is
   minimality with respect to the desired behaviour.
6. **Rulings.** Does any step contradict a decisions row? Look at rows 391, 405, 408, 416 (9) and
   417 (2).
7. **The typed host.** F3 proposes that `eff_rows` generates the typed interface in Lean. Is that
   the minimal route to one source for both targets? Compare it with emitting the OCaml module type
   straight from the row table, as the TypeScript printer does.

## Part D: the documents

The owner finds the documents too many and too divergent. Find where an authority now states the
model differently from `coherence.md` and the corrected dictionary. Check at least `docs/STATE.md`,
`docs/core/system-map.md`, `docs/core/host-boundary.md`, `docs/ARCHITECTURE.md`,
`ocaml/README.md` and `docs/site/concepts/host-session-protocol.md`. Report:
- each contradiction, with both sentences;
- each name collision, for example the 2026-10-17 "seams" slices beside rule S's seams, and any
  "session" that still means the workspace;
- for each fact stated in more than one authority, the one document that should own it.

## The finding template

```text
ID          A<n> | B<n> | C<n> | D<n>
Severity    critical | high | medium | low
Kind        missing | false | gap | over-engineered | contradiction | collision
Where       the document and section, or the files and declarations, by name and path
Evidence    the quotation, the command and its output, or the counterexample
Why         the rule, ruling or behaviour at risk
Fix         the change to coherence.md, to an authority, or to the plan
Size        XS | S | M | L
```

A finding without evidence is not a finding. Parts B, C and D give fifteen findings each at most,
ranked by severity. Part A is a table, followed by its missing items as findings.

## Probes

- **OCaml:** build in your worktree's `ocaml/` with `opam exec --switch=effect4 -- dune build`.
- **Lean:** your worktree has no Lean build. Run a check from the main checkout, which is built, as
  `python3 /private/tmp/seams-lean-one.py lake env lean <file>`; it writes nothing there.
- Put every probe under the report folder's `probes/`, with the command that runs it.

## Rules

- Write only `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-20-coherence-audit/codex-review/`:
  `README.md` and `probes/`.
- Edit no tracked file in any checkout.
- Run none of these: `make`, `lake build Test`, `make gen-semantics`, `tsc`.
- Respect the owner's steers:
  - one owner per fact, and Lean owns meaning;
  - bloat is a modeling error, and over-engineering is one too;
  - coherence, not a count of consumers, is the measure;
  - no new program syntax, and no generic judgment record (row 414 (2));
  - never argue from rebuild cost.
- In a Lean probe, write no `simp_all`, `first |` or `try`.
- Cite code by path and declaration name, and literature by authors, title, venue and year.

## Your report

`README.md` opens with the one thing to know. Then:
- the ten findings that matter most, as a table;
- Part A's map, then its missing items;
- the findings of Parts B, C and D, ranked;
- the changes you propose to `coherence.md`, as a list the coordinator can apply;
- the decisions only the owner can make, with any that `coherence.md` §9 lacks.
