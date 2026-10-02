# Seat W2 receipt (data wave, commit 2): the generator extended for variable arity and the declared order

Brief: `brief-W2.md` here, with its amendments (at dispatch: probe Q's commit-2 text; 2: probe P's
leaf-order table, decisions row 177; 3: the checker's revisions, row 172 amended; 4: probe U's
generated families, row 182; 5: the rule checker's evidence, row 182 amended), and the owner's
stop relayed by the coordinator (no new steps: finish the item in progress, commit a half-done
item as far as it builds and name it, run the byte-identity check, hand back), with the
coordinator's sharpening of it. Rules: `README.md` here, `2026-10-01-landing/plan.md` §4,
`AGENTS.md`. Worktree `/Users/pooks/Dev/lean4-effect4-seat-W2`, branch `seat/W2`, base
`74dae8d2`; head: the branch's tip, the commit that last changed this receipt (the code's last
commit is `21249189`).

Evidence words: **proved** (a kernel theorem compiled here, `#print axioms` at or below
`[propext, Quot.sound]`), **reproduced** (a byte comparison against a fresh producer run),
**tested** (a finite check run here: a `#guard`, a generator run with its exit code, a script,
a `dune` build), **reading** (read in code, not run), **assumed** (not checked). Logs are under
`W2/logs/` beside this receipt; each starts with its command and ends `# exit=… seconds=…`.

## The one thing

**The branch changes no `Ty` and no bytes, and it merges clean.** After its last generator
change every producer still writes today's files: the derived groups regenerated in place with the
extras-merged fold generator, then `git diff --exit-code` over the Makefile's 62 generated paths,
exit 0, none untracked (reproduced; step 1's whole chain is below). `git merge-tree` is clean
against main's `f4881f74` (no file changed on both sides), against `68ddb9ed` (J2 merged; the
Makefile changed on both sides) and against the line's newest head `8506ee05` (D4 merged; the
Makefile and `tools/Tools/Variances.lean` changed on both sides). Step 2 stopped at the owner's
word: item 4 (the rule checker, which validates its evidence first, and the census's completeness
footer) landed, its log check confirmed by Codex at 23:16, but its `--tree` wrapper still passes
a failed or missing producer run (Codex 23:16, reported after the stop; owed); item 1 is half done
(the `--extras` mode for a plain block, which today's `Ty` is); the nested `ArgF` extension, the
prisms, the table emitter, D-U1 (a)'s expansion, the mirrors, U's 24-theorem battery and U's red
tables and `axioms.py` are owed, each with its obstacle under "Step 2". Generator inputs changed
on both sides of the merge (J2's manifest and guards; this branch's fold, view, variance and
wire-tag tools), so `make check-gen` on the merged tree is the interaction check this seat cannot
run.

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
| after step 2's generator change (`21249189`) | `LEAN_NUM_THREADS=1 python3 scripts/generate.py --only derived` in place (`gen/extras-derived.log`, 116 s), then the drift (`gen/extras-derived-diff.log`) | exit 0, 24 generator runs, the fold tool's three groups (Fold, ValFold, SchemaFold) among them; drift exit 0, none untracked: **byte-identical (reproduced)** |

`readme` is a host producer (`bun`): the worktree has no install, and `make` would run
`bun install` into it. Its lockfile and `package.json` were then byte-identical to the main
checkout's (`cmp`, tested), so `ts/eff/node_modules` here was a symbolic link to the main
checkout's install (gitignored, read only), and `-o ts/eff/node_modules` kept `make` from
reinstalling into it. The link is removed now ("Permissions, the worktree, and what is bounded").

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
the conservativity check's sixteen controls (`bash scripts/check-conservativity.sh --self-test`:
16 of 16, 9 s, `conservativity/self-test.log`; again inside `make check-conservativity
BASE=74dae8d2`, 4 s, `conservativity/make-check-conservativity.log`; tested). The ten mutations
(`Test/fixtures/conservativity/mutations.json`, probe Q's) are judged in process; the six revision
controls (row 172 amended) run as the command, so their exit codes are a caller's:

| Control | Expected | Got |
| --- | --- | --- |
| R1 a golden byte vector changes; R2 a frozen baseline file changes | REFUSE at C1 | REFUSE at C1 (verdict 1) |
| R3 an existing constructor moves in a generated manifest; R4 an existing constructor is re-typed; R5 a new constructor reuses a tag; R9 a tag row given twice in one object | REFUSE at C2 | REFUSE at C2 (verdict 1) |
| R6 a corpus verdict moves; R7 a golden program's typing verdict moves | REFUSE at C3 | REFUSE at C3 (verdict 1) |
| R8 an appended constructor the policy does not name | REFUSE at C4 | REFUSE at C4 (verdict 1) |
| G1 the wave appended, every addition named, goldens and verdicts untouched | PASS | PASS (verdict 0) |
| V1 invalid BASE; V1 with `--strict` | exit 1, named | exit 1: "the BASE revision 'no-such-conservativity-base' does not resolve to a commit (git rev-parse --verify <rev>^{commit}); nothing was compared" |
| V2 invalid CAND; V2 with `--strict` | exit 1, named | exit 1: "the CAND revision 'no-such-conservativity-candidate' does not resolve to a commit …" |
| V3 invalid BASE and CAND; V3 with `--strict` | exit 1, both named | exit 1: "the BASE revision '…' and the CAND revision '…' do not resolve to a commit …" |

A git execution error other than an unresolvable revision is a named refusal too (exit 1), and a
file absent at a revision is read as absent, never as an unreadable revision (reading:
`scripts/lib/conservativity.py`, `git()` and `Side`); neither has a control of its own. The home
is `scripts/lib/` beside the script's other helpers, and `make check-conservativity` runs the
self-test (with `BASE=<rev>` it also judges the tree).

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

## Step 2: probe U's generated families (decisions row 182), stopped at the owner's word

The coordinator's step-2 message (amendment 4) named five items and an acceptance; amendment 5
added the evidence validation; the owner's stop arrived while item 4's build ran. Where each
stands:

| Item | State | Commit |
| --- | --- | --- |
| (1) `--extras` merged with Q's `elim` kind, the no-flag output today's bytes | landed for a plain block: half of item 1 | `21249189` |
| (1) the extension to nested blocks with `ArgF` positions | owed, not started | — |
| (1) the prisms beside the view | owed, not started | — |
| (2) the table emitter, `ty-faces` and `ty-classes` as JSON, their generated modules | owed, not started | — |
| (3) D-U1 (a)'s expansion with an `eq_cata` connector per expanded definition | owed, not started | — |
| (4) the rule checker, its evidence validation, the census's completeness footer | landed; the `--tree` wrapper's producer checks owed (Codex 23:16, below) | `d1e76a19` |
| (5) the mirrors `of_ty` and `rand_ty` emitted into OCaml | owed; left to W4, as the message allows | — |
| acceptance: U's 24 agreement theorems as a battery, the two red tables refused, U's `axioms.py` | owed: they test items 1 and 2's output | — |

### Item 4, landed (`d1e76a19`), its `--tree` wrapper owed a repair

- **The completeness footer.** `#traversal_census` and `#exhaustive_gate`
  (`src/Effect4/Laws/Auto/Traversals.lean` +6, `Exhaustive.lean` +4) end each report with
  `#traversal_census done: N rows; M modules under S scanned` (the gate likewise), `M` counting
  the environment's modules under the scope. The one pinned consumer,
  `Test/Audit/TraversalCensus.lean`, gains the two footer lines (`9 rows; 1 modules under
  Test.Audit.TraversalFixture`, `3 rows; 1 modules under Test.Audit.ExhaustiveFixture`). Built:
  `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Auto.Traversals Effect4.Laws.Auto.Exhaustive
  Test.Audit.TraversalCensus`, 557 jobs, exit 0, 169 s (`build/census-footer.log`; tested). The
  Laws root, an importer that holds only imports, was not rebuilt here: the roots build is the
  coordinator's at the merge.
- **`scripts/check-ty-rule.py`** (253 lines): probe U's `check-commit4-rule.py`, its rule R1–R4
  and its exemptions by name (the derived `instReprTy.repr`; the pass-throughs
  `selectRefusal.match_1` and `Decision.arms.match_4`), behind an evidence check. Before any
  verdict it requires E1, a log that is not empty and holds no `error:` line; E2, in the main log,
  both sections under `Effect4` with their headers and footers and exactly the footer's count of
  rows between them; E3, every module the rule names among the census's rows
  (`Effect4.Program.Ty`, `Effect4.Program.Fold`, `Effect4.Laws.Program.TyView`,
  `Effect4.Laws.Program.Typed.Membership`), since the footer's module count cannot tell a partial
  import set; E4, complete sections under `OCaml5`, `Tools` and `Conform` in the mirror logs when
  given. Missing evidence exits 2 with a named message; a violation exits 1. `--tree [--logs DIR]`
  runs `Test/fixtures/ty-rule/Census.lean` (`import Effect4`, `import Effect4.Laws`) and the seven
  `CensusMirrors*.lean`, one Lean process at a time at `LEAN_NUM_THREADS=1`, then checks them.
  The fixtures sit under `Test/fixtures/`, which the trust gate's source inventory excludes
  (`Test/Audit/AxiomGate.lean`, reading).
- **The Makefile rule** `check-ty-rule` (its own `.PHONY`, after `$(CHK)/tools` and before `help`,
  beside `check-conservativity`); `check:`, `CHECKS` and the help text are untouched (amendment 2:
  they are J2's lines, and the coordinator wires both rules in after the merge).

**The controls** (`make check-ty-rule`, `ty-rule/make-check-ty-rule.log`: 7 of 7 as expected,
1 s; tested). The first five are the five the coordinator named (green, the deliberate violation,
and Codex's three missing-evidence logs); the last two are added here, because a truncation can
keep both headers and a census over a partial import set prints complete-looking sections.

| Control | Input (from `Test/fixtures/ty-rule/census-green.log`) | Exit | Message |
| --- | --- | --- | --- |
| green | the fixture | 0 | `0 violation(s)` |
| deliberate violation | one `fold` row made `structural` | 1 | `1 violation(s): R1 1` |
| empty log | an empty file | 2 | `check-ty-rule: REFUSE (missing evidence): …: the log is empty; no census was read` |
| compiler error only | `error: unknown module prefix Effect4` | 2 | `…:1: the log holds a compiler error (error: unknown module prefix Effect4); a failed run is no census` |
| truncated before the gate | the fixture cut at `#exhaustive_gate` | 2 | `…: no complete #exhaustive_gate section under Effect4` |
| rows cut inside the census | the fixture cut at its first `delegates` row | 2 | `…: the #traversal_census section under Effect4 has no completeness footer (a truncated census)` |
| a census over a partial import set | the `Effect4.Laws.*` rows dropped, the footers recounted | 2 | `…: the census reads no row of ['Effect4.Laws.Program.TyView', 'Effect4.Laws.Program.Typed.Membership']; it was not run over the whole tree (import Effect4 and Effect4.Laws)` |

**The baseline** (`python3 scripts/check-ty-rule.py --tree --logs …`, `ty-rule/baseline.log`,
133 s; tested): exit 1, `77 violation(s): R1 21, R2 13, R3 38, R4 5`, over complete evidence: the
footers `#traversal_census done: 122 rows; 356 modules under Effect4 scanned` and
`#exhaustive_gate done: 66 rows; 356 modules under Effect4 scanned`, and complete mirror sections
under `OCaml5`, `Tools` and `Conform` (`ty-rule/census.log`, `ty-rule/census-mirrors.log`). Probe U
counted 78 at `630e6c37`; the one row fewer is R4's `LcnfMl.tyOcaml`, deleted in step 1f. The
number is not the contract (row 182 amended) and it moves at the merge: W1 changed
`Schema/Codec.lean` and `Schema/Bridge.lean`, whose matches are R3 rows here, and D3 added
modules to the Laws root. The baseline's completeness rests on its logs alone: all eight producer
runs (the main census and the seven mirror fixtures) printed both sections with their footers and
no `error:` line, but the wrapper did not record their exit codes (the gap below).

Codex's 23:16 review confirms the log check: empty, error-only and truncated logs exit 2, and the
seven built-in controls pass. It found a gap in the `--tree` wrapper, owed below.

### Item 1, half done (`21249189`)

Probe U's `U/patches/Fold.lean` (+303/−1) merged into the fold generator beside Q's `elim` kind.
Both patches add their section just before `structure Args`; U's hunk was rejected there (Q's
`Elim` section holds the anchor), so the `Extras` namespace was placed after `end Elim` by hand; `Arg` gains the binder name, the block
reader records it, `--extras` and `--namespace` are parsed, and `run` hands off to `runExtras`.
+310/−1 lines (299 non-blank added). The generator's header lists the mode and its refusals.

- **Without the flag every output is today's** (reproduced): the three groups that run this tool
  (Fold, ValFold, SchemaFold) regenerated in place by `LEAN_NUM_THREADS=1 python3
  scripts/generate.py --only derived` (exit 0, 116 s, `gen/extras-derived.log`), then the drift
  over the 62 generated paths (exit 0, none untracked, `gen/extras-derived-diff.log`). The tool is
  a `--run` driver, outside the `Effect4Gen` library's roots, so that elaboration (with
  `-DwarningAsError=true`) is its build.
- **With the flag, on today's `Ty`** (`lake env lean -DwarningAsError=true -M 4096 --run
  tools/Effect4Gen/Fold.lean --extras --group TyExtras --imports Effect4.Program.Fold --out
  <scratch> Effect4.Program.Ty`, exit 0, 6 s, `gen/extras-ty-emit.log`): 522 lines, identical to
  U's `U/generated/ProbeU/TyFoldExtras.lean` but for the header's command and the namespace (three
  lines of `diff`, `gen/extras-vs-U.log`; reproduced), kept as `gen/extras-ty-emitted.lean.txt`.
  It compiles (`lake env lean -DwarningAsError=true`, exit 0, `gen/extras-ty-compile.log`) with
  eight receipts: `tyBuild_view`, `foldMap_head_eq_cata`, `foldMap_eq_cata`, `cata_fusion_ty` and
  `cata_prod_ty` at `[propext]`, `sizeOf_tyKids` and `cata_ofLayer_inv` at `[propext,
  Quot.sound]`, `cata_ofLayer_view` with none (proved, in scratch). No manifest group runs the mode,
  and no file is added to the tree.

### What is owed, with its obstacle

None of these was started, and none was half done, so the owner's stop is the first obstacle of
each. Each also has its own:

- **(1) The nested extension with `ArgF` positions.** `Extras.emitExtras` refuses a nested block
  by name ("holds a member under a container; its layer is `ArgF`'s"), so on commit 4's `Ty` (with
  `record (fields : List (String × Ty))`) the mode emits nothing. The extension gives the extras
  emitter the nested path's position language, with `LayerView`'s `ArgF` as the layer's argument
  type (U §3.5): the view, the layer algebra, and the head and paired folds read a field list as
  `List (String × R)`, and U's layer functions, written for at most two children, fold the child
  list instead. Its size is U's assumption (150 to 200 lines), not measured: nothing was written.
  The input to test it on is already a fixture here (`GenFix/Record/Ty.lean`, the record family).
- **(1) The prisms beside the view.** Not started; neither the tree nor U's patches emit them, so
  their shape is still to be written from the view's head test.
- **(2) The table emitter and the two tables.** U's `TableGen.lean` (133 lines) splices the face
  table's `schema` column into Lean as source text (the table's own comment: "`schema` terms are
  Lean source"), and D-U2 rules that column as `Representation` values. So the table needs a JSON
  encoding of `Representation`, and the emitter a printer of those values into Lean; neither U's
  patch nor the tree's generators has one. The emitted tables are typed by `TyTable` (item 1's
  output, which no group writes yet) and read by U's generic interpreters (`ProbeU/Faces.lean`,
  `Classes.lean`, `ClassRow.lean`, `Reflect.lean`, `Enum.lean`, 347 lines), which have no home
  under `src/` yet; landing them is part of the item. U's red tables (`red-extra-row.json`,
  `red-missing-row.json`) are this item's controls.
- **(3) D-U1 (a)'s expansion.** It expands each table-driven fold on the LCNF cut into a plain
  structural definition beside its `eq_cata` connector, so it needs (2)'s tables and the
  interpreters in the tree first.
- **(4) The `--tree` wrapper (Codex 23:16; reported after the stop, not repaired).** The wrapper
  calls each producer without inspecting the return code (`scripts/check-ty-rule.py:224-228`), the
  aggregate mirror-log check requires only the three top-level scopes so a lost Tools run still
  leaves "enough" evidence (`:133-143`), and the fixture set is discovered by `glob` with no check
  that each intended mirror fixture exists (`:233-234`). With a fake `lake` injecting exit codes,
  three cases still exit 0: the main producer emitting a complete report then exiting 7; one Tools
  mirror producer exiting 7 silently; one intended mirror fixture missing from the directory. The
  repair: refuse on every nonzero producer exit, naming the producer and status, and keep the
  producer logs; verify the intended fixture and module inventory against a list, not a glob; add
  those three cases to the self-test beside the existing controls. Evidence: Codex's
  `/private/tmp/codex-second-eyes-2026-10-01/2316-ty-rule/` (`run.py`, `run-extra.py`,
  `results.json`: expected exit 2, actual 0, in `tree-main-fails-after-output`,
  `tree-one-mirror-fails-silently` and `tree-missing-one-mirror-fixture`). The three causes are
  confirmed here by reading the cited lines (reading); the fake-`lake` runs were not repeated here.
- **(5) The mirrors `of_ty` and `rand_ty`.** Not started; left to W4 (the message's own
  alternative). Landing them needs `dune build` and `make check-ocaml` green with the emitted files.
- **Acceptance.** U's 24 agreement theorems are stated against the generated view, tables and
  interpreters (items 1 and 2), so their battery waits for those. The brief names "the
  `Test/All.lean` anchor" without a line, so the battery's anchor is the coordinator's to give.
  U's `axioms.py` reads the emitted modules' `#print axioms` and lands with them.

### Commits of step 2

| Commit | What |
| --- | --- |
| `d1e76a19` (2, item 4) | the census's and the gate's completeness footers with the re-pinned report; `scripts/check-ty-rule.py`; `Test/fixtures/ty-rule/` (the green log, `Census.lean`, the seven mirror censuses); the `check-ty-rule` rule |
| `21249189` (2, item 1, half) | the `--extras` mode in `tools/Effect4Gen/Fold.lean`, for a plain block |
| the head | this receipt and its logs |

## Merge notes

- **Against main's `f4881f74`** (the coordinator's named head): `git merge-tree --write-tree
  --name-only HEAD f4881f74` gives the tree `842ef929`, no conflict; no file changed on both sides
  since `74dae8d2` (main gained 39 commits; tested).
- **Against the line's head `68ddb9ed`** (`refactor/phase1-phase3` at the time of writing: J2's
  merge `b15d57b3` and its record): the tree `6ed1d634`, no conflict. One file changed on both
  sides, the Makefile: J2's `check-tsgo` in `CHECKS`, in `check:` and in the help text, and the
  truth link as a prerequisite of two checks; this branch's `check-conservativity` and
  `check-ty-rule`, each with its own `.PHONY`, after `$(CHK)/tools`. The merged Makefile holds both
  (tested: `git show 6ed1d634:Makefile`).
- **What a textual merge cannot show.** (a) Generator inputs changed on both sides: J2's
  `tools/Effect4Gen/manifest.json` (the Refusals group imports `Effect4.Api.Author` and adds
  `Effect4.Api.BuildRefusal`), `guards/refusals.lean`, `guards/runner.lean`, with their outputs
  `Api/RefusalsDerived.lean` and `Api/RunnerDerived.lean`; this branch's `Fold.lean`, `View.lean`,
  `Tools/Variances.lean` and `Tools/WireTags.lean`. The groups are disjoint, so the merged tree
  should write the line's bytes; that is assumed, and `make check-gen` on the merged tree tests it.
  (b) The census and the gate print one more line; the only `#guard_msgs` pin of their output in
  the tree is re-pinned here, and `68ddb9ed` adds none (`git grep`; tested). (c) The Lean cones
  overlap: the main line's new `Laws/Program/Typed` modules sit downstream of `FoldOf.lean`
  (through `Membership.lean`), and the Laws root imports the two census modules. None of the main
  line's 25 changed files under `src/`, `Test/` and `tools/` invokes `fold_of` or the census
  commands (`git grep` at `68ddb9ed`; tested), and every module that does, with `Membership.lean`,
  was rebuilt against this `FoldOf.lean` in step 1 (`build/foldof-dependents.log`, 385 jobs; tested);
  that the main line's changed `Typed` modules elaborate against it is assumed until the roots
  build at the merge. (d) The rule checker's baseline moves (above), and its
  `GENERATED_MODULES` names U's planned modules (`Effect4.Program.TyEq`, `TyFoldExtras`,
  `TyTables`), which W4 keeps or edits when the generated modules land.
- **Against the line's newest head `8506ee05`** (D4's merge, after `3a31867b` "Main green after
  J2"): the tree `73e26e23`, no conflict (tested). Two files changed on both sides: the Makefile
  (also `3a31867b`'s install rule) and `tools/Tools/Variances.lean`, where the line rewrote one
  docstring paragraph (the cross-check now names oxc) and this branch added the arity words and
  the core variance module; both merge clean. Two interactions to run after the merge: D4 changed
  `Laws/Program/Typed/Membership.lean` (+17), which invokes `fold_of` and so elaborates against this
  branch's `FoldOf.lean` (assumed until the roots build); and D4 re-cut the LCNF face
  (`ocaml/engine/api_engine.ml`, `ocaml/gen/api_gen.ml` and their two closure manifests) with the
  base's translator, while this branch adds the translator's `Array.mk` row and the manifest-path
  rule. `make check-gen` does not reach the `lcnf` group, so `make gen-lcnf` and the drift over the
  four artefacts and their manifests, on the merged tree, are what establish those bytes (step 1
  reproduced them at the base; on D4's code it is assumed).
- This branch touches none of the files the brief reserves for D2, D3, D4, J2 and W1 (the
  Makefile's shared lines included), so no order among the seats is forced by it.

## Permissions, the worktree, and what is bounded

- No permission was refused in this seat.
- `ts/eff/node_modules` was a symbolic link to the main checkout's install (gitignored, read only)
  for the one host producer, `readme`, in step 1's `make check-gen` (22:58Z), when the two
  `bun.lock` files were byte-identical (`cmp` when the link was made; tested). The main checkout's
  lockfile changed with J2's merge at 23:17:53Z (its modification time), so the link was removed at
  the end (the link only; the install is untouched). A later `make` here that reaches `readme` runs
  `bun install` into this worktree.
- Host-only or bounded evidence: `readme` (bun, through that install); the `lcnf-zipidx`
  fixture's `dune` build (`opam exec --switch=effect4`); the generator fixtures are finite cases.
  No TypeScript compiler ran: no TypeScript source changed.
- Not run, as the stop says: a roots build after step 1's (`build/roots.log`, 748 jobs, at
  `1d7d4ce9`), `make check-full`, and the conservativity check after step 2 (the generated paths are
  unchanged since its step-1 PASS, by the drift above).

## Found on the way (not repaired here)

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

## Proposed lines for the coordinator's files (this seat edits no register)

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
- **Row 182 (an amendment to its status):** "Seat W2, stopped at the owner's word, landed item
  4 whole (`scripts/check-ty-rule.py` validates its evidence, E1 to E4, before the rule; the census
  and the gate print a completeness footer; seven controls by `make check-ty-rule`, not in
  `check`; the baseline 77 at the branch's tree, U's 78 less `tyOcaml`) and item 1 for a plain block
  (the `--extras` mode reproduces U's 522 lines from today's `Ty`; without the flag every output is
  today's). Owed: the nested extension with `ArgF` positions, the prisms, the table emitter with the
  face table's Schema column as `Representation` values (U's emitter splices Lean text), D-U1 (a)'s
  expansion, the mirrors (to W4), U's 24-theorem battery, its red tables and `axioms.py`, and the
  `--tree` wrapper's repair (Codex 23:16: refuse a nonzero producer exit by name, keep the producer
  logs, check the fixtures and modules against a list, three new controls)."
- **The Makefile, after J2's merge (the coordinator's lines):** the help text names
  `check-conservativity` and `check-ty-rule` as instruments run by name. Neither joins `CHECKS`
  (both are plain rules, not `$(CHK)` markers, so the `check-%` pattern would ask for a marker that
  does not exist) nor `check:`, until the owner rules `--strict` (row 172) and commit 4 turns the
  rule on (row 182).
- **For W4's brief (the rule):** the append's acceptance is `python3 scripts/check-ty-rule.py
  --tree` exiting 0 over complete evidence; `GENERATED_MODULES` in the script names the generated
  modules by U's planned names and is edited with them; the extras mode needs the nested extension
  (item 1, owed) before commit 4's `Ty` can use it.
