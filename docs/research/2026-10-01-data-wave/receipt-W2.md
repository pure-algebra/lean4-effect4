# Seat W2 receipt (data wave, commit 2): the generator extended for variable arity and the declared order

Brief: `brief-W2.md` here, with its amendments (at dispatch: probe Q's commit-2 text; 2: probe P's
leaf-order table, decisions row 177; 3: the checker's revisions, row 172 amended) and the
coordinator's two messages for step 2 (probe U, decisions row 182; the rule checker's evidence,
row 182 amended). Rules: `README.md` here, `2026-10-01-landing/plan.md` §4, `AGENTS.md`.
Worktree `/Users/pooks/Dev/lean4-effect4-seat-W2`, branch `seat/W2`, base `74dae8d2`.

Evidence words: **proved** (a kernel theorem compiled here, `#print axioms` at or below
`[propext, Quot.sound]`), **reproduced** (a byte comparison against a fresh producer run),
**tested** (a finite check run here: a `#guard`, a generator run with its exit code, a script,
a `dune` build), **reading** (read in code, not run), **assumed** (not checked). Logs are under
`W2/logs/` beside this receipt; each starts with its command and ends `# exit=… seconds=…`.

## The one thing

**Step 1 changes no `Ty` and no bytes: after the patches every producer writes today's files byte
for byte** (`make gen-variances gen-derived`, `make gen-lcnf`, `make check-gen`, `git diff
--exit-code` over the 62 generated paths: reproduced), and the conservativity check, landed with
row 172's revision repair, passes against the base. The leaf-order table is P's (row 177), read
from the core when the core declares it; the tree's core declares none until commit 4, so today's
literal rule is still written as `litRule` and the mechanism is shown on fixtures (one edge, the
wave's four with `nat ⊑ number` accepted and its converse rejected, proved; a cyclic table
refused). Step 2 (probe U) is in progress below; where it stops is named at the end.

## Step 1: probe Q's commit 2, amended by probe P's table and the checker's repair

### Commits (on `seat/W2`, base `74dae8d2`)

| Commit | What |
| --- | --- |
| `128f80d1` (1a) | `Fold-elim.patch` verbatim: the `elim` kind (eliminator, structural `beq` with its iff and the `DecidableEq` instance, structural `Repr`); the generator's new module header records the monadic-fold decision (step 3) |
| `e13a3e3f` (1b) | `View-variable-arity.patch` (three variable kinds, computed dispatch) with its `rules` section replaced by probe P's table read from the core (row 177); `Variances-commit2-mechanism.patch` without its `rules` list (the table's one home is the core) |
| `9986a92b` (1c) | the conservativity check, `scripts/check-conservativity.sh` over `scripts/lib/conservativity.py`, with row 172's revision repair, its sixteen controls and the `make check-conservativity` rule |
| `2d0d2b01` (1d) | `FoldOf-prod.patch` and `fold_of`'s sibling over a list of products holding the member (Q3) |
| `7821240c` (1e) | `Translate-array-mk.patch`; the closure manifest beside a redirected run's output (row 174 (i), not Q's patch verbatim, below); the wire-tag loader refusing a repeated key (row 174 (ii)) |
| `1d7d4ce9` (1f) | row 173's first three: `Audit-seed-keeps-notes.patch` (and `CasesPolicy.toJson` writing the top-level note), the cases policy re-seeded, `LcnfMl.tyOcaml` deleted |

### The conservativity proof: every producer writes today's bytes

| Step | Command | Result |
| --- | --- | --- |
| the roots, once | `LEAN_NUM_THREADS=4 lake build` (`build/roots.log`) | 748 jobs, exit 0; the module and axiom gate: 526 modules, 72,789 declarations, `[propext, Quot.sound]` with the exact implementation boundary (tested) |
| variances, derived | `LEAN_NUM_THREADS=1 make gen-variances gen-derived` (`gen/make-gen-variances-derived.log`) | exit 0, "PASS generate: requested producers ran in dependency order"; 24 generator runs |
| the drift | `git diff --exit-code --stat` over the Makefile's 62 `GENERATED_PATHS` entries, and the untracked ones (`gen/diff-after-variances-derived.log`) | exit 0, none untracked: **byte-identical (reproduced)** |
| per producer, before the make run | the patched `View.lean` on today's `Ty` (`gen/today-TyView.log`), `Fold.lean` on the Fold and ValFold groups (`gen/today-Fold.log`, `today-ValFold.log`), `Variances.lean` (`gen/today-variances.log`), each against the committed file with `cmp` | byte-identical (reproduced) |
| lcnf | `LEAN_NUM_THREADS=1 make gen-lcnf` (`gen/make-gen-lcnf.log`), then the drift (`gen/diff-after-lcnf.log`) | exit 0, the four artefacts rewritten, the engine's manifest still at `ocaml/gen/closure-api_engine.tsv`; drift exit 0, none untracked: **byte-identical (reproduced)** |
| the rest of the chain | `LEAN_NUM_THREADS=1 make -o ts/eff/node_modules check-gen` (`gen/make-check-gen.log`) | exit 0: eff, wire, cas, ts and readme re-run, the corpus re-cut (408 programs kept, 385 readable), "PASS check-gen: every Lean-only generated file is what its generator emits" (reproduced) |
| the conservativity check | `scripts/check-conservativity.sh 74dae8d2` against the tree (`conservativity/after-producers.log`) | PASS, 4 of 4: 295 vectors, 21 tag families, 862 verdict rows unchanged; C5 no change; C4 reports the four stale `Ty` constructors (not `--strict`, row 172) (tested) |

`readme` is a host producer (`bun`): the worktree has no install, and `make` would run
`bun install` into it. Its lockfile and `package.json` are byte-identical to the main checkout's
(`cmp`, tested), so `ts/eff/node_modules` here is a symbolic link to the main checkout's install
(gitignored, read only), and `-o ts/eff/node_modules` keeps `make` from reinstalling into it.

### Fixtures kept (each the red or green control of its piece)

`scripts/test-generators.py` over `Test/fixtures/generators/`: 14 of 14 as expected on a fresh
scratch tree over step 1's last commit (`gen/test-generators-step1.log`, 225 s; tested):

| Case | Kind | What it holds |
| --- | --- | --- |
| `elim-refuses-plain`, `elim-refuses-param` | red (tested) | probe Q's two refusals: no member under a container; a parameterised family |
| `elim-record` | green (tested) | the `elim` kind on the record fixture (today's `Ty` plus `record (fields : List (String × Ty))`), compiled, receipts `[propext]` or none |
| `elim-val-agrees` | green (proved) | on `Store.Val`, the generated eliminator is the hand one by `rfl`; `val_beq_agrees` `[propext]` |
| `fold-record` | green (tested) | the nested record family's fold group compiles; no monadic half (the decision) |
| `foldof-record` | green (proved; its red reproduced at the base) | `fold_of` over the record family: `members`, `isNever`, `isMember`, `renderRaw` (+`renderFields`), `closed` (+`closedFields`), `fieldTys` (+`fieldTysOf`, a paramorphism); every connector at most `[propext, Quot.sound]`; at the base all five refused (`gen/foldof-scan-base.log`) |
| `view-record` | green (tested) | the view at a field-list head without a table (today's literal rule) compiles |
| `view-no-arity` | red (tested) | a field-list head whose variance row has no arity word |
| `view-leaf-one` | green (tested) | table mode at today's one edge (`lit < string`): the view emits the table's laws, `hleaf`, no `litRule`, and compiles |
| `view-leaf-cyclic` | red (tested) | a cyclic table (`nat < int < nat`) refused by name, nothing written |
| `variances-module` | green (tested) | the producer's core variance module (`--lean-out`) compiles |
| `wave-view` | green (tested) | the wave fixture (record, map, tuple, app, the leaves, the four-edge table) through `elim`, fold and view |
| `wave-controls` | proved | `nat_sub_number` (accepted, derived, not an entry), `number_not_sub_nat` (its converse), `undefined_sub_unit`, `unit_not_sub_undefined`, `nat_number_not_an_entry`, through the restated laws, `[propext, Quot.sound]` |
| `lcnf-zipidx` | green (tested; its red reproduced at the base) | a root reaching `List.zipIdx` lowers, builds with `dune` and answers what Lean answers; a redirected run writes its manifest beside its output (`gen/lcnf-zipidx-base-dune.log`: "Unbound record field to_list" before the row) |

Beside them: the wire-tag loader's four guards in `Test/Store/DerivedCheck.lean` (built), and
the conservativity check's sixteen controls (`make check-conservativity`: 16 of 16, 9 s).

### Where this departs from the patches, and why

1. **The order's rule table (row 177).** Probe Q's `View-variable-arity.patch` read a `rules`
   section of `variances.json` and a core `Ty.edgeRule` written by the variances producer;
   row 177 rules probe P's table instead (`Ty.leafEdges` in the core, read by `sub` through
   `leafRule`). So the view reads the table from the environment and emits P's laws, and the
   producer's `Rule` list, closure check and `edgeRule` are not landed (one table, one owner);
   the producer keeps Q's arity words and core variance module. "The producer refuses a cyclic
   table": the view does, by name, before writing a line (`view-leaf-cyclic`).
2. **Today's one edge (`lit < string`).** The table mode is chosen by the environment: the tree's
   core declares no `leafEdges` in this commit (no `Ty` change), so the view writes today's text
   with `litRule` and its three lemmas, byte for byte; the mechanism at today's one edge is the
   `view-leaf-one` fixture, whose core declares the one-edge table and whose `sub` consults it.
   Declaring the table in the tree's core now would have changed `TyView.lean`, `sub` and the
   consumers of the literal vocabulary (22 lines in 5 files, probe Q), against "no bytes".
3. **The closure manifest (row 174 (i)).** Q's patch writes every manifest beside `--out`, which
   for the recipe's `ocaml/engine/api_engine.ml` would move its manifest out of `ocaml/gen/` (row
   70, `GENERATED_PATHS`) and leave the tracked one stale. Landed instead: a run whose `--out` is
   one of `ocaml/gen/roots.json`'s artefacts keeps `ocaml/gen/closure-<stem>.tsv`, any other run
   writes beside its output (tested both ways: `lcnf-zipidx`, and `make gen-lcnf` above).
4. **`fold_of`'s sibling** is +235/−43 non-blank lines against the base (beside Q's +28/−1),
   against the 60 to 120 lines Q assumed (measured, `git diff 74dae8d2`).
5. **`tyOcaml`** is deleted outright; the two call sites render `tyT`.

### Found on the way (not repaired here)

- A LCNF closure with no inductive type renders an empty `type` group, a syntax error that
  `Ml.checkModule` passes (`gen/lcnf-zipidx-notype-dune.log`, tested).
- `Conform.Effect4.LcnfMl.main` sits inside its namespace, so `lean --run` cannot reach it, and
  its compiled driver stops at an extern hole of the lowered library (`USize.repr`); both as at
  the base (`conform/lcnfml-rung.log`, tested and reading). Its live consumer is the compiler
  profile, which passes.
- For W4: probe P's copy writes the record field as `(name, optional, type)`, probe Q's (which the
  view generator reads) as `(name, type, optional)`; and P's record arm of `sub` uses
  `canonF`/`heads`/`attach.zip attach`, while the generated arm lemma proves Q's form
  `decide ((canon fs).map … = …) && ((canon fs).zip (canon gs)).attach.all …` (reading). Commit 4
  writes the production arm in the generator's form, or extends the arm-lemma emitter.

### Proposed lines for the coordinator's files (this seat edits no register)

- **Row 171 (an amendment to its status):** "Landed by seat W2 (commit 2): the `elim` kind, the
  view's three variable kinds and computed dispatch, the arity words and the core variance module,
  `fold_of`'s product position and field-list sibling (+235/−43, not the 60 to 120 assumed), the
  translator's `Array.mk` row; the order's exceptional rules are probe P's core table (row 177),
  not a `rules` section, so the producer's rule list and `edgeRule` are not landed. On today's
  `Ty` every producer writes today's bytes (reproduced: `make gen-variances gen-derived`,
  `make gen-lcnf`, `make check-gen`, `git diff --exit-code` over the 62 generated paths)."
- **Row 177 (an amendment):** "Mechanism landed (W2): the view reads `Ty.leafEdges` from the
  environment when the core declares it, refuses a cyclic closure by name, and emits P's laws and
  `sub_eq_leafRule_of_not_sameHead`; with no table in the core it writes today's literal-rule text,
  so the tree is unchanged until commit 4 declares the table with its four edges. Fixtures: the
  one-edge table (`view-leaf-one`), the wave's four edges with `nat ⊑ number` accepted and its
  converse rejected through the restated laws (proved), the cyclic table (refused)."
- **Row 174 (i) (an amendment):** "Landed as: the recipe's four artefacts keep
  `ocaml/gen/closure-<stem>.tsv` (row 70); any other `--out` writes its manifest beside it. Q's
  patch verbatim would have moved `api_engine.ml`'s manifest out of `GENERATED_PATHS`." (ii):
  "Landed: the Lean loader scans for a repeated key before `Json.parse`; the Python reader is the
  conservativity check's; four guards in `Test/Store/DerivedCheck.lean`."
- **Row 172 (an amendment):** "Landed (W2) as `scripts/check-conservativity.sh` over
  `scripts/lib/conservativity.py`, with the revision repair: sixteen controls (`make
  check-conservativity`), green at the base and against this commit's tree; `--strict` waits for
  the owner's word on promoting `refOf`, `deferredOf`, `var`, `unknown`."
- **Row 173 (an amendment):** "The first three landed (W2): the policy re-seeded with its notes
  kept (equal to the base's as JSON values, reformatted once), `tyOcaml` deleted, the Audit driver
  change; `make check-cases` and the conform compiler profile pass."
- **Row 119:** "The eliminator and the equality are generated (the `elim` kind, W2), never a third
  hand copy; the generated companions of `Store.Val` equal the hand ones (`rfl`, proved)."
- **Row 162:** "Commit 2 (W2) landed alone with byte-identical outputs."
- **A new decisions line, the monadic-fold decision:** "A block with a nested position gets no
  monadic half and no path fold (`tools/Effect4Gen/Fold.lean`'s header): nothing reads one
  (`git grep`, tested); when `Ty` becomes nested its block loses `foldMapAt_ty`, `TyMAlgebra`,
  `TyAlgebra.toM`, `TyMAlgebra.map`, `TyMAlgebra.toSeq`, `foldM_ty`, `foldM_eq_cata_ty`,
  `foldM_id_ty`, `foldM_natural_ty`; a later consumer adds the per-position `sequence` first."
- **For W4's brief:** the record field shape and the record arm's form (above, "Found on the
  way"); the view needs `canon`, `mem_canon`, `canon_eq_nil` in `Ty.lean` for a field-list head,
  `argVariance`/`Variance.select`/`holds_eq_select` (the core variance module) for an applied head,
  and the table's companions for the leaf table (`View.lean`'s header lists them).
