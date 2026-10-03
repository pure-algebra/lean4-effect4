# 2026-10-03 seat language receipt: controlled English, the dictionary and `make check-language`

**The one thing to know before merging:** the dictionary in `docs/core/controlled-english.md` now
owns every term's meaning. The glossaries of system map §9 and `docs/core/semantics.md` §3 moved
into it. Decisions row 142 placed the glossary in system map §9, so the move needs row 142
amended (proposal P1 below). Two lines of the owner's `docs/STATE.md` (523 and 536) still name
the old owners, and the brief forbids me to edit that file. The branch merges onto the lead's
`a32f3a2e` with no conflict (`git merge-tree`, tested).

## Base and head

- Branch `seat/language`, created from `394bc602` (the lead's `refactor/phase1-phase3`).
- The harness made this worktree on `origin/main` (`9187b9b6`). The guardrail refused
  `git reset --hard`, so I created `seat/language` at `394bc602` with `git switch -c`. The harness
  branch `worktree-agent-abd2a344cc83e51b1` is untouched.
- Commits: `9499f42e` (the slice), `de092d9a` (two checker refinements), and the commit that adds
  this receipt. Two spec edits ride in the receipt's commit: the judgment entry (Codex: `Fits` is
  a recursive definition) and the rule against nested double quotes (§2.8).

## Changed files

| File | Change |
| --- | --- |
| `docs/core/controlled-english.md` | new: the writing rules (W1–W30), the dictionary (§3.1–§3.8), the tree-name table moved from system map §9 (§3.9), the seven judgments and the four boundary behaviours (§4), the diagram convention and a Mermaid concept map (§5), the artifact skeletons (§6), the checker (§7) |
| `scripts/lib/language.py` | new: reads the dictionary, filler table, procedure verbs and limits from the specification; parses Markdown into prose units; the six rules |
| `scripts/check-language.py` | new: the report, `--show`, `--strict`, `--self-test` (31 red and green controls) |
| `Makefile` | `language` in `CHECKS`; the marker rule `$(CHK)/language` beside `$(CHK)/docs`; the help text. Not in `make check` |
| `AGENTS.md` | rewritten in the controlled English; every rule kept (map below); a writing-rules summary; the vocabulary as one line per core term with a pointer; the seven judgments; the parallelism rule; the authority map names the new owner |
| `docs/core/system-map.md` | §9 replaced by a pointer; layer 1's owner cell and criterion S4's check cell name the dictionary |
| `docs/core/semantics.md` | §3 replaced by a pointer |
| `docs/DESIGN-BASIS.md` | three pointers (DB-16, DB-17, "Literature names, corrected") name the dictionary |
| `docs/research/2026-10-03-seat-language-receipt.md` | this receipt, force-added |

## Commands and results

Each command ran in the worktree, at the head before this receipt's commit unless marked.

| Command | Result |
| --- | --- |
| `python3 scripts/check-language.py --self-test` | `PASS check-language self-test: 31 of 31 controls` |
| `python3 scripts/check-language.py --strict docs/core/controlled-english.md AGENTS.md` | `PASS check-language: no finding in docs/core/controlled-english.md, AGENTS.md; the other documents carry 2231 finding(s)` |
| `python3 scripts/check-language.py --strict docs/research/2026-10-03-seat-language-receipt.md` | PASS (this file) |
| `python3 scripts/check-docs.py` | `FAIL check-docs: 13 stale reference(s) in 1 of 71 documents`, all in `docs/STATE.md`, all present at the base (see "Open obligations") |
| `git diff --check` | no output, exit 0 |
| `make -n check-language` | prints the paths inventory step, `--self-test`, `--strict docs/core/controlled-english.md AGENTS.md`, the marker touch; exit 0 |
| `make help` | lists `language` among the checks |
| `git merge-tree --write-tree --name-only a32f3a2e seat/language` | tree `d0b66d54`, exit 0: no conflict |
| anchors of the specification against the merged tree `d0b66d54` (scratch script) | 388 anchors over 111 files; 5 anchored files differ; 0 failures |
| anchors declared in their files (scratch script over a declaration index) | 387 of 388 found as declarations; `#auto_census` is declared by a `syntax` whose keyword sits on the previous line |
| comparison of the moved sections with the dictionary (scratch script) | system map §9: 263 of 263 code spans present, 26 of 26 author-year names; semantics §3: 67 of 68 spans present (`let*` left out on purpose); `AGENTS.md` vocabulary: 45 of 45 |

No `lake` ran. The scratch scripts live in the session scratchpad and are not committed.

## Axiom output

No Lean declaration changed, so there is no axiom output.

## Evidence

- The checker's six rules: tested (31 controls, each red control fails when its rule is off).
- The specification and `AGENTS.md` pass strict mode: tested.
- The anchors: tested (388 pairs at the head and at the merged tree).
- The precision of the word rules: reading. I judged two random samples of 40 word findings by
  hand. Under the rules as written, 75 of 80 were true. Of the five false positives, `de092d9a`
  fixed three: two italic titles and one hyphenated qualifier. Two remain, both negated uses ("not
  an equivalence claim", "does not establish … equivalence").
- No rule of `AGENTS.md` is dropped or weakened: reading (the clause map below).
- Nothing of the moved glossaries is lost: tested (the span comparison above), with the
  deliberate omissions listed below.

All evidence is local to this worktree. None is host-only.

## The linter's counts, before and after

Both columns use the final dictionary; "before" reads each document at `394bc602`. The rules are
`length`, `qualifier`, `avoid`, `filler`, `line-cite` and `anchor`. Totals: before 2386 (length
1360, qualifier 170, avoid 71, filler 2, line-cite 783); after 2231 (length 1327, qualifier 166,
avoid 64, filler 2, line-cite 672). The anchor rule reads only the specification and finds none.

| Document | Before | After | length | qualifier | avoid | filler | line-cite |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `docs/DESIGN-BASIS.md` | 573 | 572 | 239 | 24 | 7 | 0 | 302 |
| `docs/core/semantics.md` | 159 | 134 | 32 | 13 | 6 | 0 | 83 |
| `docs/STATE.md` | 131 | 131 | 118 | 8 | 4 | 0 | 1 |
| `docs/design/design-language.md` | 129 | 129 | 57 | 5 | 0 | 0 | 67 |
| `docs/core/decisions.md` | 127 | 127 | 11 | 1 | 17 | 0 | 98 |
| `docs/core/traversal-census.md` | 104 | 104 | 96 | 0 | 0 | 0 | 8 |
| `docs/design/string-diagrams-notes.md` | 88 | 88 | 36 | 1 | 0 | 0 | 51 |
| `Test/contracts/schema-payload.contract.md` | 77 | 77 | 66 | 9 | 2 | 0 | 0 |
| `Test/contracts/faces.contract.md` | 51 | 51 | 45 | 6 | 0 | 0 | 0 |
| `docs/DESIGN-ISSUES.md` | 48 | 48 | 21 | 2 | 5 | 0 | 20 |
| `docs/core/system-map.md` | 135 | 40 | 33 | 2 | 5 | 0 | 0 |
| `Test/contracts/program-denotation.contract.md` | 39 | 39 | 37 | 1 | 0 | 0 | 1 |
| `Test/contracts/environment-context-key.contract.md` | 36 | 36 | 33 | 2 | 1 | 0 | 0 |
| `Test/contracts/scope.contract.md` | 36 | 36 | 34 | 1 | 1 | 0 | 0 |
| `Test/contracts/frames.contract.md` | 35 | 35 | 32 | 3 | 0 | 0 | 0 |
| `docs/core/host-boundary.md` | 35 | 35 | 12 | 6 | 2 | 0 | 15 |
| `docs/core/lcnf-route.md` | 32 | 32 | 25 | 4 | 0 | 0 | 3 |
| `docs/core/machine-state.md` | 31 | 31 | 17 | 7 | 1 | 0 | 6 |
| `Test/contracts/program-runtime-r.contract.md` | 29 | 29 | 26 | 2 | 1 | 0 | 0 |
| `Test/contracts/foundation-wave2.contract.md` | 26 | 26 | 16 | 10 | 0 | 0 | 0 |
| `Test/contracts/schema-representation.contract.md` | 25 | 25 | 23 | 1 | 1 | 0 | 0 |
| `Test/fixtures/schema-representation/README.md` | 23 | 23 | 19 | 4 | 0 | 0 | 0 |
| `docs/ARCHITECTURE.md` | 23 | 23 | 20 | 3 | 0 | 0 | 0 |
| `docs/GENERATED.md` | 22 | 22 | 20 | 1 | 1 | 0 | 0 |
| `Test/Counterexamples/REGISTER.md` | 20 | 20 | 9 | 0 | 1 | 0 | 10 |
| `Test/contracts/cause-exit.contract.md` | 20 | 20 | 18 | 2 | 0 | 0 | 0 |
| `ocaml/gen/NOTES.md` | 20 | 20 | 15 | 1 | 0 | 1 | 3 |
| `docs/core/api-surface.md` | 18 | 18 | 13 | 2 | 3 | 0 | 0 |
| `harness/truth/LANE.md` | 18 | 18 | 17 | 0 | 0 | 1 | 0 |
| `ocaml/eff/README.md` | 18 | 18 | 18 | 0 | 0 | 0 | 0 |
| `Test/contracts/program-denote-r.contract.md` | 15 | 15 | 14 | 1 | 0 | 0 | 0 |
| `Test/contracts/data-row.contract.md` | 12 | 12 | 6 | 5 | 1 | 0 | 0 |
| `Test/contracts/machine-scheduler-core.contract.md` | 12 | 12 | 8 | 0 | 0 | 0 | 4 |
| `tools/target/README.md` | 12 | 12 | 10 | 2 | 0 | 0 | 0 |
| `Test/contracts/machine-handles.contract.md` | 11 | 11 | 11 | 0 | 0 | 0 | 0 |
| `Test/contracts/schema-subalphabets.contract.md` | 11 | 11 | 8 | 3 | 0 | 0 | 0 |
| `Test/contracts/scope-machine.contract.md` | 11 | 11 | 7 | 4 | 0 | 0 | 0 |
| `Test/contracts/scope-restoration.contract.md` | 11 | 11 | 5 | 6 | 0 | 0 | 0 |
| `Test/contracts/program-sched.contract.md` | 10 | 10 | 9 | 1 | 0 | 0 | 0 |
| `Test/contracts/schema-recursor.contract.md` | 10 | 10 | 7 | 3 | 0 | 0 | 0 |
| `Test/contracts/typescript-target-expr.contract.md` | 9 | 9 | 6 | 3 | 0 | 0 | 0 |
| `docs/RUNTIME-COVERAGE.md` | 9 | 9 | 7 | 1 | 1 | 0 | 0 |
| `Test/contracts/schema-annotations.contract.md` | 8 | 8 | 8 | 0 | 0 | 0 | 0 |
| `ocaml/README.md` | 8 | 8 | 8 | 0 | 0 | 0 | 0 |
| `README.md` | 7 | 7 | 6 | 0 | 1 | 0 | 0 |
| `harness/README.md` | 7 | 7 | 7 | 0 | 0 | 0 | 0 |
| `generated/semantics.md` | 6 | 6 | 0 | 4 | 2 | 0 | 0 |
| `ts/eff/README.md` | 6 | 6 | 6 | 0 | 0 | 0 | 0 |
| `Test/contracts/schema-codec.contract.md` | 5 | 5 | 1 | 4 | 0 | 0 | 0 |
| `ts/eff/ingest/README.md` | 5 | 5 | 2 | 3 | 0 | 0 | 0 |
| `Test/contracts/schema-typescript-generation.contract.md` | 4 | 4 | 3 | 1 | 0 | 0 | 0 |
| `Test/fixtures/baseline/66ee4657-supplement-v1/README.md` | 4 | 4 | 4 | 0 | 0 | 0 | 0 |
| `ocaml/STANDARDS.md` | 4 | 4 | 4 | 0 | 0 | 0 | 0 |
| `.claude/skills/runtime-coverage/SKILL.md` | 3 | 3 | 2 | 1 | 0 | 0 | 0 |
| `Test/contracts/README.md` | 3 | 3 | 3 | 0 | 0 | 0 | 0 |
| `Test/contracts/machine-approximation.contract.md` | 3 | 3 | 3 | 0 | 0 | 0 | 0 |
| `Test/contracts/machine-completion.contract.md` | 3 | 3 | 2 | 1 | 0 | 0 | 0 |
| `Test/fixtures/baseline/66ee4657/README.md` | 3 | 3 | 1 | 1 | 1 | 0 | 0 |
| `tools/Conform/README.md` | 3 | 3 | 2 | 1 | 0 | 0 | 0 |
| `docs/UPSTREAM-BACKLOG.md` | 2 | 2 | 2 | 0 | 0 | 0 | 0 |
| `docs/design/README.md` | 2 | 2 | 2 | 0 | 0 | 0 | 0 |
| `harness/truth/corpus-known-differences.md` | 2 | 2 | 2 | 0 | 0 | 0 | 0 |
| `Test/Counterexamples/README.md` | 1 | 1 | 1 | 0 | 0 | 0 | 0 |
| `Test/contracts/machine-scheduling.contract.md` | 1 | 1 | 1 | 0 | 0 | 0 | 0 |
| `generated/AGENTS.md` | 1 | 1 | 1 | 0 | 0 | 0 | 0 |
| `AGENTS.md` | 34 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Test/contracts/machine-behaviour.contract.md` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Test/contracts/schema-authoring.contract.md` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Test/fixtures/traces/fiber-m3/README.md` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `docs/core/controlled-english.md` | new | 0 | 0 | 0 | 0 | 0 | 0 |
| `harness/truth/result.md` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Reading notes for the next slices:

- `docs/DESIGN-BASIS.md` carries 302 line citations because its "How to read a row" requires
  witnesses with `file:line` at a named commit. That convention conflicts with W25 (proposal P4).
- `docs/core/system-map.md` and `docs/core/semantics.md` dropped their glossary citations with
  the move; the dictionary cites the same names by path.
- `generated/semantics.md` has no prose of its own. Its findings come from the semantics registry
  and the producer (the mismatch table), so a later slice fixes them at the producer.

## The `AGENTS.md` clause map

Every clause of the old `AGENTS.md` is kept. Most keep their words, split into sentences of 25
words or fewer. The table lists each clause whose wording changed, and why.

| Old wording | New wording | Why |
| --- | --- | --- |
| "the always-loaded router" | "the router that every session loads" | plain words |
| `system-map.md` "…: the frame and the vocabulary's definitions" | "…: the frame"; a new entry `controlled-english.md` | the ownership move |
| `Test/`: "batteries, attacks and proof receipts; `Audit/AxiomGate.lean` is the gate" | "batteries, counterexamples and proof receipts; `Test/Audit/AxiomGate.lean` holds the gates: the axiom gate, the module-closure gate and the library-root gate" | the register's word, and the three gates the file runs |
| "is held to `ocaml/STANDARDS.md`: libraries…, …, every number…" | a list of the four rules | W16 |
| "Determinism is claimed only after fixing a complete compatible decision tape…" | "…a compatible decision tape that answers every decision…" | "complete" means completeness against a judgment (W8); same content |
| "A new representation is admitted by naming its sort's signature…" | "…enters the tree only by naming its sort's syntax signature…" | "admitted" is a judgment word; the sense of "signature" named |
| the Vocabulary paragraphs (free object, algebra and fold, exact embedding, simulation, located refusal, monoid action, Schema and program) | one line per term with a pointer; the rules inside them kept as their own lines ("Traversal", "Agreement of folds", "Widening", "Equivalent", "Foreign transformation") | the brief; the definitions and instances moved into the dictionary |
| "`run_eq_ref` at the empty host table" | "…at the empty row table" | "host table" is a synonym of the tree's `RowTable` |
| "is admitted by exact name in `AxiomGate.lean`" | "is exempted by its exact name…" | the gate exempts; admission is a judgment word |
| "The module-closure gate checks both roots." | "The library-root gate checks both roots." | `#effect4_axiom_gate` names that check the library-root gate; the module-closure gate is the `Test/All.lean` check |
| Do not say `"sound"`, … without naming the exact judgment, … | Name the exact judgment, observation, theorem or gate before you say `"sound"`, … Name its assumptions and the remaining host boundary too. | W2 (procedural sentences of 20 words or fewer) |
| "printed by `scripts/report-effect-runtime-coverage.sh`" | "that … writes" | "print" names the object printer (§3.1) |
| "a change to the machine or the syntax" | "…the program syntax" | the sense of "syntax" named |
| "(`lake build Test`, the trust gate)" | "(`lake build Test`, the axiom gate)" | "trust gate" is a synonym |
| "`make status` prints what is true at HEAD, …" | "`make status` gives …", the measured items as a list | "print" sense; W16 |
| "One `lake` at a time in a working tree." | kept, with the parallelism rule: `LEAN_NUM_THREADS=3 lake build <Module>` or a `make` target | the lead's addition (measured 2026-10-03) |
| the aesop paragraph | the same rules as a sub-list | W2 |
| "A proof graph is mandatory only for admission or refusal, …, and external semantic equivalence" | a list: "an admission or a refusal of any input (a program, a table, a reply, a codec value, …)", …, "an equal-observation claim against an outside implementation" | "admission" and "equivalence" qualified; scope unchanged |
| "Never an edit in place that throws away work to be repeated." | "Never edit in place in a way that throws away work to be repeated." | W4 (imperative) |
| the handoff fields in one sentence | "first, the one thing…", then a list | W16 |

The new rules are all additions:

- the writing-rules summary;
- "Same endpoint types do not make a pair exact, and a decoder with an encoder is not by itself a
  lawful optic";
- the seven judgments;
- "No open ledger goal does not mean the semantics is finished";
- the parallelism rule.

## What moved into the dictionary, and what I did not copy

- System map §9 (41 rows) became §3.9, one row each, with every site cited by name and path.
- Semantics §3 became entries in §3.2 and §3.3, with each Lean counterpart kept. Its rows were
  "syntax", the three senses of "elaborate", "print", "read", "render", "lift", "sugar", "census"
  and "gate".
- The `AGENTS.md` vocabulary became entries in §3.2 and §3.5. `AGENTS.md` keeps one line per term.
- The metaprogramming audit's vocabulary (`docs/research/2026-10-01-metaprogramming-audit/audit.md`)
  is adopted in §3.3. The note is history, so I left it unchanged.

Facts corrected while moving, each checked against the tree today:

- `typedState_load` and `denoteR_typed` are retired ledger-goal names. Their proofs are
  `loadsTyped` and `denotesTyped` (`src/Effect4/Laws/Program/Typed/LayerArm.lean`).
- `Ty` is declared in `src/Effect4/Program/TyCore.lean`, and `Store.Val` in
  `src/Effect4/Store/Carrier/Val.lean`.
- `LayerTy` is in `src/Effect4/Program/Typing/Rules.lean`, and `normalize_idem` in
  `src/Effect4/Program/Ty.lean`.
- `parkHandshake_of_reachable` is now a theorem (`src/Effect4/Laws/Program/Guard/Handshake.lean`).
- The old glossary's sugar examples `let*` and `try*` name no form in the tree. The sugar is
  `eff { ... }` and `eff do ...`, and the lifts are generated functions
  (`src/Effect4/Program/Authoring/Lifts.lean`), not macros.
- The JSON codec's retraction holds for every successful encoding (`decode_of_encode`), and record
  support is open in the bridge and the codec. `CTy.join` is the normalized union. Membership
  implies inhabitance (`inhabited_of_fits`). These four came from the lead's and Codex's reviews.
- "native machine" became "frame machine", and "host table" became "row table".
- "elaboration of scoped syntax" stays as the literature's word for `denoteR`, and our prose says
  "denote". The proposed words "surfaceElaborate" and "residualize" are not adopted.

## Where the tooling's words disagree with the dictionary

Each row names the site, the word the tool uses now, the dictionary word, and a proposed change
for the lead. The tooling files are outside this seat's scope, so none is edited here.

| Site | Tool word now | Dictionary word | Proposed change |
| --- | --- | --- | --- |
| registry claim `m7-never-halts` (`tools/Tools/SemanticsRegistry.lean`) | role `progress` | invariant consequence, not progress (`semantics.md` §2.4, `AGENTS.md`) | a new role `safety` |
| claims `m7-exits-typed`, `m7-stores-typed`, `obs-typed-admitted` | role `adequacy` | type safety; adequacy relates an operational semantics and a denotation | role `safety` |
| claim `m7-results-exit-hasty` | role `adequacy` | an agreement between two exit judgments | a new role `agreement` |
| claim `fair-scheduling` | role `adequacy`, title "Progress under weak fairness" | liveness | a new role `liveness`; title "Liveness under weak fairness" |
| claims `host-progress`, `store-safety` | role `progress` | liveness (an assumption); safety | roles `liveness`, `safety` |
| claim `fits-subn` | role `preservation` | subsumption (membership closed under the order) | a new role `subsumption` |
| claims `load-typed`, `load-typed-checked`, `load-typed-layer-free` | role `preservation` | initiation of the invariant (no step) | a new role `initiation` |
| claims `close-idempotent`, `close-twice`, `close-reentrant-add`, `provide-discharges`, `allows-answer`, `close-order-eq` | roles `preservation`, `inversion` | equations or characterizations, with no step relation | a new role `equation` |
| claims `session-success-prepared-membership`, `session-failure-shape-free` | role `preservation` | soundness of reply admission relative to membership and to the defect exclusion | a new role `soundness` |
| claims `typed-state-admitted`, `m7-exit-handles-valid`, `replay-externals`, `machine-typed-not-halted` | roles `preservation`, `inversion` | safety invariants over reachable states | role `safety` |
| claims `decode-iff`, `of-schema-exact`, `decode-encode`, `of-schema-schema` | roles `decidability`, `compatibility` | exactness; retraction | new roles `exactness`, `retraction` |
| claims `subn-refl`, `normalize-idem`, `cata-eff-congr-on` | role `compatibility` | reflexivity; idempotence; congruence | new roles, or `equation` |
| claim `hom-eq-cata-eff` | role `fundamentalProperty` | uniqueness of the fold out of an initial algebra | a new role `uniqueness` |
| claims `flush-fair`, `close-seq-protocol`, `provide-closed`, `m7-route` | role `fundamentalProperty` | bounded fairness; a protocol equation; closure; a conditional route | `liveness`, `equation`, `equation`, a new role `route` |
| claim `drivestate-lift` | role `simulation` | an invariant lift rule | a new role `invariant` |
| claims `run-eq-meaning`, `loop-agreement` | role `simulation` | adequacy (the design basis: "Adequacy, not 'simulation', for the equations") | role `adequacy` |
| the `Role` inductive | 14 words; `compatibility` labels 22 claims, many not compatibility lemmas | the dictionary's role words | extend `Role` with the words above (proposal P2) |
| ledger scope `M3bAdequacy` | "Adequacy" names handler adequacy | the role `adequacy` names Plotkin adequacy | rename the scope, for example `M3bHandlerAdequacy` (W22) |
| concept titles | "Invertible embeddings", "Free syntax objects", "external reply ingestion", "Semantic preservation …, and capstone M7" | exact embeddings; free objects; reply admission and application ("ingest" names the foreign-TypeScript contract); name the stage; M7 | retitle the four concepts |
| claim titles and cuts | "empty host table", "retained host table", "non-empty host tables", "has no host table" | row table | write "row table" |
| claim title of `subn-equiv-iff` | "Kernel of subN is syntactic normal form equality" | "kernel" is Lean's kernel; write `≡N` | "subN equivalence is equality of normal forms" |
| report text (`tools/Tools/Semantics.lean`) | "semantic axiom ceiling", column "Evidence at the ceiling", field `withinSemanticAxiomCeiling` | trust ceiling | "trust ceiling", "Within the trust ceiling", `withinTrustCeiling` |
| report text | "inherited placement", "## Placement" | declaration placement (placement alone is the obligation placement of `AGENTS.md`) | "declaration placement" |
| report text | "### Printed statements" | "print" is the object printer; this is Lean's display | "Statements as Lean displays them" |
| report text | "authored links to historical attacks" | counterexamples (an attack is an attempt) | "historical counterexamples" |
| report text | "theorems of the registry's concept-named modules" | semantics registry | "the semantics registry's" |
| `make help` and Makefile comments (`build`, `check`, `check-slow`, the header) | "axiom audit" | axiom gate | "axiom gate" |
| `Makefile` `$(CHK)/roots` | `PASS library-roots: fresh module, root-closure and axiom audit` | the module-closure, library-root and axiom gates; the target is `check-roots` | `PASS check-roots: the module-closure, library-root and axiom gates, fresh` |
| `make help` `status`; `README.md` | "document drift" | stale references (drift is a generated file that differs) | "stale references" |
| `README.md` | `make check-roots # fresh library-root and trust audit`; "codegen artefact" | axiom gate; artifact | "the module-closure, library-root and axiom gates, fresh"; "artifact" |
| `scripts/status.py` | label `attacks` for the register's counts | counterexamples | label `counterexamples` |
| `scripts/status.py` | "stale" for a marker older than its inputs, and for a reference that does not resolve | two senses of one word | markers "out of date"; references "stale" |
| 12 tracked documents | "trust gate" | axiom gate | normalize (the `avoid` rule lists them) |
| tree names (`src/Effect4/Program/Decision.lean`, `src/Effect4/Api.lean`) | `Program.Decision` (a value-decided fork) and `Api.Decision` (a run decision) | one word, two meanings, beside "decisions row" | rename `Program.Decision` (proposal P6) |
| tree names (`src/Effect4/Program/Eff.lean`, `src/Effect4/Data/Row.lean`) | two `Row` types: operation row and requirement row | operation row; requirement row | qualify in prose now; rename one later |
| tree names (`src/Effect4/Api/HostProtocol.lean`, `src/Effect4/Laws/Effects/Protocol.lean`) | two protocols: the host automaton and protocol typing | host protocol; protocol typing | qualify in prose |
| tree names (`src/Effect4/Store/Domain/Canonical.lean`, `src/Effect4/Program/Ty.lean`) | class `Canonical` and predicate `Ty.Canonical` | lawful prism; normal form | `Ty.Normal`, as the formal pass proposed |
| tree name (`src/Effect4/Codegen/Target.lean`) | `Artefact` | artifact | keep the code name; prose writes artifact |

## Proposed decisions rows (proposals only)

- **P1. Amend row 142.** The glossary of tree names, literature names, marks, laws and corrections
  lives in `docs/core/controlled-english.md` §3.9. System map §9 is a pointer. The dictionary owns
  every term's meaning; the system map owns the frame. Rows 13 and 36 ("written into `AGENTS.md`
  Vocabulary") read as history: the rules stay in `AGENTS.md`, and the definitions moved.
- **P2. The semantics registry's roles follow the dictionary.** Extend `Role` with safety, liveness,
  initiation, soundness, exactness, retraction, reflexivity, idempotence, congruence, uniqueness,
  equation, agreement, route and invariant. Relabel the claims as the mismatch table proposes.
  First: `m7-never-halts` is not progress.
- **P3. `make check-language` joins `make check`.** It costs about 3.5 s, refuses only the
  specification and `AGENTS.md`, and reports the other documents. The brief kept it out of this
  slice; the owner decides.
- **P4. The design basis cites witnesses by name and path.** Its "How to read a row" asks for
  `file:line` at a named commit (302 findings). Recommendation: cite the name and path (W25), and
  keep the commit in the status line.
- **P5. One spelling per word.** The tree mixes "behaviour" and "behavior", "normaliser" and
  "normalize", "artefact" and "artifact". The dictionary chose "artifact" for prose. The rest is open.
- **P6. Rename the colliding tree names.** `Program.Decision` first, then one of the two `Row`
  types; the formal pass's `Ty.Normal` and `EnvFits` are already proposed.
- **P7. Point the other definition sites at the dictionary.** The evidence words are defined
  again in `docs/GENERATED.md` (DI-32), `docs/DESIGN-BASIS.md` ("Evidence words") and
  `docs/core/semantics.md` §1 (which also requires `file:line`). Each becomes a pointer plus its
  document's own conventions.

## Open obligations

- `docs/STATE.md` is the owner's working copy. It names the old owners at line 523 ("the glossary
  of our words against Lean's") and line 536 ("the operating rules and the vocabulary"). Its
  committed version also carries the 13 stale references that make `check-docs` fail. All 13 exist at the
  base, and none involves a file this slice changed.
- The normalization of the other documents, in the order of the counts table, is later work.
- System map §1.1 still states the three senses of "signature". It is frame text and agrees with
  the dictionary; a later slice may make it a pointer.
- The checker does not measure W1, W3, W10, W24 or W29. The writer and the reviewer apply them.

No proof obligation was assigned to or landed by this seat, so there is no placement block.

## What this does not establish

A passing strict run means the measured rules hold in two files. It does not make a document
clear or correct. The precision figure is a hand-judged sample of 80 findings. The anchor check
proves only that each cited file contains each name.
