# Status at the end of 2026-10-01: what landed, where the work stands, what is in the way

Written by the coordinator at the owner's request ("give me a read; nothing new; a coherent
stopping place; then a documentation and focus pass"). Main is `69c78069` on
`refactor/phase1-phase3`, green (749 jobs; the gate 531 modules, 73924 declarations at
`[propext, Quot.sound]`; `check-schema-codec` passing). Evidence words as §7 of the system map.

## 1. Landed today (188 commits since `38686e44`, 14 merges)

| What | Where | Evidence |
| --- | --- | --- |
| Row 156 `ScopeLive`; the scope-handle posts; `E4-TYPED-CE-018` repaired | seat I2 (`c898ad04`) | proved |
| Row 150 `FoldLift`: the six fold-level Guard inductions gone | seat G (`2a99f045`) | proved |
| Row 154: the design basis exact at `6b3f2c92`; the glossary re-pinned | seat H2 (`84bdf454`) | tested |
| Rows 24, 16, 17 (part): minted binders, `Await` a record, codecs for the reading types; `check-host-protocol` on tsgo | seat J (`93360b3a`) | proved, tested |
| Rows 152, 153: membership at an exit type excludes shape defects; M5 over the expansion; rows 117 and 151 measured to their obstacles | seat D1 (`a3db653c`) | proved |
| The type language probed end to end: the corpus census (T), record terms (R), the Schema side per form (S), every wave law on one copy and both exactness theorems (P), the generator mechanism and conservativity (Q), every `Ty` traversal an algebra (U) | probes T, R, S, P, Q, U (merged; research only) | proved on copies, tested |
| lean4-typescript 0.7.0 in the package (optional fields, `index`, `new`, `objectWith`); pushed, tagged `v0.7.0`, pinned with its consumer diffs | seat W0; the pin `74dae8d2` | tested; main green |
| Sixteen ledger goals closed (`M6Ledger` 20 → 9 open, `M6Edits` 6 → 1); eight checked false with five clauses proposed | seat D3 (`7d50cfe6`) | proved |
| Row 128: the JSON codec and the Schema reader are exact embeddings (route (b), no guard); the defect id; row 179's one annotation policy | seat W1 (`cdd62673`) | proved |
| The owner's rulings: 165 (a), 163, 151 (a″), 117 as recommended; the push | recorded | — |
| Codex's eight reviews folded, each finding verified before it was recorded (two checker defects, one shortcut refuted, one profile mismatch, one missing premise) | rows 122, 170, 172, 179, 182 | tested by rerun or by reading |

The ledger: 37 open of 484 this morning, 21 open now (463 proved). The register: 186 rows, 37
repaired, 144 seeded. The decisions register: 183 rows, 34 of them written today (150–183).

## 2. In flight (four seats, told to stop at a coherent place and hand back; nothing new starts)

| Seat | Doing | State when told to stop |
| --- | --- | --- |
| D2 | M5's denotation lemma, arm by arm, under the three statement repairs (rows 170, 175; 176 under measurement; 183 found) | groups 1–3 of six committed; group 4 in progress |
| D4 | Row 151 (a″): the void at the public close (step one committed, `1ba84f74`); the finalizer row and the flips (step two) | step two in progress |
| J2 | Row 168: the ingest's parser off `typescript@5.9.2`; `check-tsgo`; seat J's four owed items | its roots build running |
| W2 | The wave's commit 2: Q's generator patches (landed on its branch), the conservativity script (repaired, confirmed by Codex), U's families (in progress) | the census footer and the rule checker's evidence validation building |

Not started, briefed, and held: D5 (row 134's five clauses, the field census, M6b/M6c, row 180),
W4 (the `Val` and `Ty` appends), W5–W10.

## 3. Where the two lines stand

**Wave 2, the typed state (the core milestone).** M5: the statement was false as declared three
times over (a malformed-reference root, an untyped completed view, a foreign service table) and is
now the honest one (rows 170, 175), with one representation question open (row 176: the type of a
built layer context) and one design finding (row 183: host adequacy can never admit a success at
a template row). M6: 16 of 24 goals closed; the other 8 are false as stated and need five clauses
of the typed state (row 134 (a)–(e), ruled). M7: the route theorem proved; its three lines wait on
M5 and M6; exit-handle validity up to registered bytes (row 180). The honest sentence: wave 2 is
finding the missing clauses as fast as it closes goals, and the instrument that would find them
first (the field census, row 181) is not built.

**The data wave.** Commits 0 and 1 landed (the package bump and pin; exactness at today's forms,
so S7 holds today). Commit 2 is on W2's branch in part. Commits 3–10 are not started; every law
they need is proved on probe P's copy, every generator change is measured on probe Q's and U's
copies, and the acceptance (rule checker at zero, conservativity green, p2's handler) is written.
The number images must nest (P), so commit 3 is not empty.

## 4. What is in the way (the owner's read, confirmed)

1. **Too much in parallel on one cone.** D1, D2, D3, D4 and D5 all touch `Laws/Program/Typed`
   (`Assembly.lean`, `PointTyped`, the `Preds` bundle, `Membership.lean`). Every merge after the
   first needed re-proofs at the merge (D3 over D1: two edits; D2 over D3: the `PointTyped`
   conjunct; D4 over both: the `Preds` field; D5 over all: the five clauses), and every seat ran
   its own roots build (750 jobs, 15–25 minutes) before its receipt while main rebuilt after each
   merge: the "constant builds". The cost is real: the merges are mine to repair, the builds
   serialize on one machine, and a seat's hours can be spent on a statement another seat is
   changing. **Change:** one seat at a time on the typed-state cone; at most two code seats in
   parallel on disjoint cones (one typed-state, one data-wave); a seat narrow-builds its modules,
   the coordinator runs the roots once at the merge (told to the four seats today).
2. **Statements found false by refutation, one goal at a time.** Eight command goals, the
   denotation lemma three times, and the bounded-expansion claim of system map §10.2 (corrected
   twice today). Each repair was the right one (the contract strengthened, never the statement
   weakened), but the method is expensive. The field census (row 181, S8) and D2's arm list are
   the instruments that would have found the gaps first; they land with D5.
3. **Instruments that pass on missing evidence.** Two research checkers (Q's conservativity,
   U's rule checker) reported success on empty or truncated input; Codex found both. One is
   repaired and confirmed, the other is being repaired. The rule for every checker from now:
   validate the evidence before counting the violations.
4. **The owner's backlog of rulings.** Rows 157–161, 166, 167, 169, 177–182 and row 134's five
   clauses are "recommended, proceeding" without the owner's word; rows 172, 176, 121/109 are
   open decisions. The seats proceed under the recommendations, which is what the owner asked,
   but the register should show the whole backlog in one table for one sitting.
5. **Documentation drift from speed.** Thirty-four decisions rows in a day, with long status
   cells; the system map's §10 amended twice; AGENTS.md's TypeScript bullet carrying interim
   sentences; STATE.md's landing paragraph grown by appending; W2's brief with five amendments
   and W4's with two. Nothing is wrong in them, but a reader starting now cannot find the ten
   facts that matter without reading the day's history.

## 5. The documentation and focus pass (proposed; the coordinator does it, no seats)

Once the four seats hand back and are merged (one roots build per merge, nothing else runs):

1. **`docs/STATE.md` rewritten from scratch, short:** true at HEAD (ten sentences), the
   documents, what is next (the serialized order: D2 → D4 → D5 on the typed state; W2 → W4 → W5
   on the data wave), and the owner's rulings in one table.
2. **`docs/core/decisions.md`:** every row landed today marked closed with one sentence and a
   pointer to its receipt (the long status cells moved to the receipts, which hold them already);
   the open rows' status cells cut to the decision and the recommendation; the owner's pending
   rulings listed in one table at the head of the register (rows and recommendations), so one
   sitting clears them.
3. **`docs/core/system-map.md`:** §10 made one consistent statement (the five places, S1–S8, the
   outcomes), the R-table and §9 statuses re-read against HEAD, the citations re-pinned by
   `check_citations.py --drift` (row 154's next pin), the vocabulary bullet of AGENTS and §4/§5 in
   one wording.
4. **`AGENTS.md`:** the TypeScript bullet reduced to the rule once J2 lands (one compiler; the
   history to the receipt); the "Working" bullet gains the one-seat-per-cone rule and the
   roots-at-the-merge rule.
5. **The register:** statuses current after D2 and D4 merge (CE-016, 020–023); the three
   `E4-FACE` rows cross-checked with W2's receipt.
6. **The data-wave README and briefs:** the commit table's statuses; W2's and W4's briefs
   rewritten clean from their amendments before W4 is dispatched (one brief, no history).
7. **The research folder:** the day's receipts and Codex copies are the history; one index
   (`docs/research/2026-10-01-landing/README.md`) listing receipts, briefs, Codex reviews and the
   status notes in order, so the folder is navigable.

Nothing in this pass changes code or proofs. It is reading and writing, one commit per document.

## 6. The stopping decisions (18:15, after reading each worktree)

| Seat | Where it is | Decision |
| --- | --- | --- |
| D2 | groups 1–3 of six committed (`5f8cbe18`); only `Membership.lean` dirty | stop now: commit the Membership additions if they build, receipt, hand back; groups 4–6 and the layer family stay owed with their obstacles |
| D4 | steps 1–4 all committed (`c0e608e4`), tree clean, the OCaml face regenerated | done: receipt, hand back, no roots build |
| J2 | steps 1–4 all committed (`e4997e6c`); its roots build running before the receipt | let the build finish, receipt, hand back |
| W2 | step 1 committed with its receipt (`cbe9a1c8`); step 2's item 4 (the rule checker with evidence validation, the census footer) dirty; U's `Fold.lean` extras possibly half applied | commit item 4 if it builds and its five controls pass; leave a half-applied patch uncommitted and listed; receipt, hand back |

Merge order, one roots build each, nothing else running: J2 (disjoint cone, plus one `open
scoped` line at the top of files the others touched), D4 (the typed state: `Sources.lean`, the
`Preds` bundle, `Assembly.lean`'s statements, `InterpR.lean`, `Stores.lean`, the OCaml face), D2
(`Assembly.lean`'s statements again, `Admission.lean`'s `PointTyped`, `Membership.lean`'s
additions, the new `Denotation.lean`; the one hand reconciliation is `Assembly.lean` against D4's
step three), W2 (the generator tools, the scripts, disjoint). Then nothing runs.

## 7. The formalization pass (the owner's plan: Pierce as the spine)

The owner wants the language's semantics categorized and organized formally, against a Pierce
book, so that the proof infrastructure, the typing and the obligations are solidified and
bounded, the rest of the language can be implemented against a stable frame, and the
documentation and the proof graph take their direction from it. The coordinator's reading of
that, to be done as the documentation pass, no seats, no builds beyond the four merges:

- **The book.** *Types and Programming Languages* (TAPL) as the spine: its chapter list is the
  checklist of what a typed language must state and prove, and ours maps onto it one judgment
  per chapter. *Advanced Topics in Types and Programming Languages* (ATTAPL) chapters 3 (effect
  types) and 8 (logical relations, Ahmed) for the two places TAPL does not reach: the requirement
  rows and the Kripke-world membership relation.
- **The document.** One new authority, `docs/core/semantics.md`, owning the judgments and their
  metatheory by chapter (the system map keeps the goal, the sorts and arrows, the requirements,
  and points to it; the decisions register keeps the decisions and points to it; no fact owned
  twice). Its sections, each with the TAPL chapter it instantiates, our names, the theorems
  with file:line, the ledger scope, and the status: syntax as free objects (`Ty`, `Eff`, `Term`,
  `Val`; ch. 3's grammars); evaluation as the machine's transition relation and the denotation
  (ch. 3, 8: `stepR`, `denoteR`, `run_eq_ref`); typing (ch. 8, 9 with the function-type cut of
  row 163 stated as the cut: `check` sound and complete for `HasTy`; `TypedProg` as the
  protocol-indexed judgment); progress and preservation (ch. 8: `machineTyped_not_halted`,
  `StepPreserves`, the lift); simple extensions (ch. 11: unit, tuples (row 159), records (119,
  165), variants (130), general recursion (`iterate`), lists, `null`/`undefined` (160)); exceptions
  (ch. 14: `exitOf`, `causeOf`, `catchCause`, the shape defects of row 152); references (ch. 13:
  `refOf`, `deferredOf`, store typings as worlds, `fits_mono`, `scopeLive_mono`, the row-156
  presence clause); subtyping (ch. 15–16: `sub`, width/depth/permutation at records (119, 178),
  the declared leaf edges (177), top `unknown`, bottom `never`, the join of row 73,
  `sub_trans_core`, `sub_antisymm_normal`); nominal types and variances (ch. 19–20 by analogy:
  `handle`, `app` with the per-name variance table, row 158); type reconstruction (ch. 22:
  `Ty.infer`, `var` templates, matching rows 73, 137); polymorphism as prenex templates (ch. 23,
  with no function values: the cut); effect rows and coeffects (ATTAPL ch. 3: `Requirement`, the
  closed-row premise of row 117, the per-position clause as a later probe); the membership
  relation as a Kripke logical relation without an arrow clause (ATTAPL ch. 8: `Fits`, worlds,
  monotonicity); the boundary as exact embeddings (Foster; Rendel and Ostermann: row 128); folds
  and the initial algebra (the coherence principle: `cata_ty`, the generated families of row
  182); concurrency, scopes and the host (beyond the book: the fiber machine, the protocols, the
  session; the papers review's references).
- **The bound.** Each chapter's standard lemma list (inversion, canonical forms, weakening,
  substitution, progress, preservation, monotonicity, transitivity, antisymmetry, decidability)
  is the closed list of obligations for that part of the language; an obligation not on a
  chapter's list is a design finding (a new chapter or a new row), never an ad-hoc theorem. The
  ledger's scopes are renamed or grouped by chapter so `#typed_state_obligations` reads per
  chapter, and the decisions register's rows are cross-indexed by chapter.
- **The order of work.** After the four merges: (1) the chapter skeleton with every existing
  theorem placed (reading only); (2) the obligation lists per chapter with status (from the
  ledger and the register); (3) the gaps as rows (the ones already known: 176, 181, 183, 134
  (a)–(e), the per-position coeffect clause; the ones the chapter lists expose); (4) the system
  map and the register pointed at it, STATE rewritten; (5) only then the next seats, each named
  by chapter.
