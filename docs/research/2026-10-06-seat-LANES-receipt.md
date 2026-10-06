# 2026-10-06 seat LANES receipt: the diagnostics lane and the ingest's census run again

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-lanes-brief.md`, with the dispatch message
and the coordinator's message that adds `ts/eff/read.ts` and `ts/eff/test/read.test.ts`.
Evidence files: `docs/research/2026-10-06-seat-LANES-evidence/`.

**The one thing to know before merging:** the promoted table
`generated/tsdiag-agreement.tsv` is the table of the base's corpus. If the merged tree moves
`generated/corpus-index.tsv`, run `make gen-tsdiag` again and read its rows before the commit.

Six more facts stand beside it.

- **The fresh table has no `typed-errors` row.** Each of the 136 programs that the checker
  types is clean under tsgo (tested). Section 3 gives the counts by verdict.
- **Both foreign engines now read the two rows that Lean prints for the mask.** DI-88 parks
  the engines, and row 215 keeps forms out of them. The brief asks for this repair, because
  the census cannot hold `restore` without it. The native callback spelling stays refused
  (section 4.3).
- **`ts/eff/read.ts` gained one case, on the coordinator's word.** `childrenOf` gave a restore
  site no child. It is its own commit, `abed62fc`.
- **The truth runner's header moved to one file, and `make check-truth` passes.** The 73 truth
  modules are unchanged byte for byte (tested, section 3.2). `make check-corpus` did not run.
- **The install line of `scripts/check-ingest.sh` did not run.** Every other step ran in the
  script's order, and each passed (section 4.4).
- **The foreign corpus's pinned file count moved from 22314 to 22398.** The count is a function
  of the base's corpus too: it moves when the number of printable skeletons moves.

## 1. Base and head

Branch `seat/lanes`, in the worktree `/Users/pooks/Dev/lean4-effect4-lower`. The base is
`6d10fcc0`. The head is the commit that adds this receipt, and its parent is `9a2dc6df`.
Nothing is pushed.

| Commit | Part | Content |
| --- | --- | --- |
| `c6f8b535` | 1a | `harness/truth/module-imports.ts`, and `run-truth.ts` reads it |
| `3a3d047d` | 1b | the diagnostics lane's repair, and the promoted table |
| `abed62fc` | 2a | `childrenOf` enters a restore site; the walkers' red twin |
| `c540da33` | 2b | the mask probes, the coverage walker, the two engines, the tests |
| `476e3550` | both | the evidence folder |
| `49457227` | 2c | one more test: the mask's rows under a form that inserts a binder |
| `9a2dc6df` | both | more evidence: the truth lane's run and two later probes |

## 2. Changed files

| File | What changed |
| --- | --- |
| `harness/truth/module-imports.ts` | new: the three name lists of a printed module's imports, and `moduleImports` |
| `harness/truth/run-truth.ts` | `importHeader` is built from `moduleImports`; its own lists are gone |
| `harness/tsdiag/run-tsdiag.mjs` | the prelude's files by the compiler; the imports from the one file; a refusal of the lane's own defects; 11 controls on every run |
| `generated/tsdiag-agreement.tsv` | promoted by `make gen-tsdiag` |
| `ts/eff/read.ts` | `childrenOf`: the `restore` case, and a default that takes `never` in each switch |
| `ts/eff/test/read.test.ts` | a module with a layer under a restore site; the red twin's test |
| `ts/eff/test/red/walkers.red.ts` | new: four walkers that lack one case each |
| `tools/Drivers/ForeignCorpus.lean` | `maskProbes`, four programs, joined to the skeleton list |
| `ts/eff/ingest/check-coverage.ts` | a case for every constructor of four sorts; defaults that take `never` |
| `ts/eff/ingest/check-corpus.ts` | the pinned count of the foreign corpus |
| `ts/eff/ingest/ck.ts` | `walkProgram` enters a restore site; the printed seam and the foreign contract read the two rows |
| `ts/eff/ingest/oxc.ts` | the foreign contract reads the two rows |
| `ts/eff/ingest/test/foreign.test.ts`, `ts/eff/ingest/test/printer.test.ts` | the mask's spellings, its refusals, and Lean's goldens |
| this receipt and its evidence folder | text files only: logs, scripts and probes |

I edited no file of `src` or `Test`, and none of the coordinator's files.

## 3. Part 1: the diagnostics lane

### 3.1 The cause, reproduced

`make check-tsdiag` fails at the base (reproduced, `tsdiag-red-at-base.log.txt`). The lane's
summary reads: `refused-agree 118, refused-other 70, refused-unmapped 84, typed-errors 136`.
Every program reports TS2305 and TS2724 on its import of the prelude. The lane wrote that
table to its work folder. With `--promote` it would have written it over the committed table.

Two causes stood in `harness/tsdiag/run-tsdiag.mjs`.

1. The lane copied `harness/truth/prelude.ts` and the session files alone. The prelude
   re-exports `prelude-atoms.gen.ts`, `records.ts` and `tuples.ts`, so the copy exported no
   atom.
2. The lane wrote its imports by hand. Its list lacked every atom after `getOrElse`, and every
   helper but `Host`, `Sql` and `Kv`. It lacked the type `MaskRestore` and the export `Data`
   (reading).

### 3.2 The repair

**One file holds the imports, and both lanes read it.** `harness/truth/module-imports.ts`
holds the names of `effect`, the prelude's helpers and its types. `moduleImports` gives the
two import lines for a module that reaches the prelude at a given path. The atoms still come
from `ts/eff/profile.gen.ts`. `run-truth.ts` and the diagnostics lane call it with the same
path.

I chose this over a header that the corpus tool writes, for three reasons.

- The helpers and the types are names that the prelude exports. Lean holds no one list of
  them: `recordHelperNames` (`ts/eff/wire.gen.ts`) names `recordRaw`, which the prelude does
  not export (reading).
- Two tools write the two corpora: `harness/truth/Truth.lean` and `tools/Drivers/Corpus.lean`.
  A header from one of them leaves the other lane on a list of its own.
- One TypeScript file serves both runners as they are. bun imports it, and node 22.23.2
  imports it with no flag (tested).

**The compiler names the prelude's files.** The lane opens the tree's prelude as the one root
of a project, under the corpus's options. It copies each file of `harness/truth` that the
compiler read: 8 files at this head. The lane keeps no list of them and no parser of its own.
A new file beside the prelude needs no edit of the lane (tested, control K2 below).

**The lane refuses its own defects.** A diagnostic of the project's options, of a copied file
of the prelude or of a module's header is no fact about a program. The lane names it and
stops, and it writes no table. Before 2026-10-06 such a defect became 136 `typed-errors` rows.

**The lane runs 11 controls on every run**, before it compares or writes a table. One project
is clean: `succ` on a number checks, and `succ` on a Boolean gives TS2345. Ten projects are
defective, and the lane must refuse each by its reason:

- a header that names what the prelude does not export (TS2305);
- the prelude without one of its files, once for each of the 7 files beside `prelude.ts`
  (TS2307);
- a file of the prelude that does not check (TS2322);
- an option that the compiler does not know (TS5023).

The truth lane's generated modules did not move. `run-truth.ts --emit` over the committed
manifest writes 73 shipped modules and 73 unannotated modules. Before and after the edit they
are the same bytes, and the shipped ones equal `harness/truth/generated` (tested). The truth
project type-checks in place under tsgo 7.0.0-dev.20260629.1, with the new file in its file
list (tested). The release lane's own closure of the runner holds the new file (tested).
`make check-truth` passes at `49457227`: 72 programs agree, with the 1 signed divergence
(tested, `check-truth.log.txt`).

### 3.3 The table, by verdict

Compiler: tsgo 7.0.0-dev.20260629.1. Runtime: effect 4.0.0-rc.112. The lane's summary line
gives each count (tested).

| Verdict | Committed at `f772efd8` (363 rows) | The base, red (408 rows) | This head (408 rows) |
| --- | --- | --- | --- |
| `typed-clean` | 134 | 0 | 136 |
| `typed-errors` | 0 | 136 | 0 |
| `refused-agree` | 158 | 118 | 181 |
| `refused-unmapped` | 42 | 84 | 62 |
| `refused-silent` | 22 | 0 | 22 |
| `refused-gap` | 6 | 0 | 5 |
| `refused-other` | 1 | 70 | 2 |

Of the 363 rows of `f772efd8`, 359 are the same bytes in the new table (tested, a join by
name). Four moved, and 45 rows are new.

- `g158` is now typed and clean. It was `refused-gap` under `requestNotSubtype`.
- `g141` and `g277` changed their refusal reason, and kept `refused-agree`.
- `g255` gained one observed code, 2345, and kept `refused-unmapped`.

The rows that the brief asks for, by refusal reason:

| Verdict | Reason | Rows | Programs |
| --- | --- | --- | --- |
| `refused-other` | `scopeExpected` | 1 | `g165`: predicted 2345, observed 2739 |
| `refused-other` | `term` | 1 | `g299`: predicted 2345, 2769 or 2554, observed 2322, 7005 and 7034 |
| `refused-unmapped` | `predicateNotBool` | 39 | `g18 g22 g23 g28 g40 g45 g47 g51 g56 g64 g71 g85 g90 g91 g93 g95 g98 g99 g125 g128 g142 g162 g170 g190 g191 g194 g229 g248 g254 g255 g264 g268 g279 g301 g307 g332 g346 g370 g389` |
| `refused-unmapped` | `cause` | 16 | `g5 g62 g76 g77 g88 g101 g111 g126 g171 g186 g214 g233 g281 g326 g336 g387` |
| `refused-unmapped` | `errorNotAdmitted` | 7 | `g79 g134 g169 g205 g246 g339 g365` |
| `refused-gap` | `term` | 1 | `g133`: `Deferred.make<number, number>()`; the printer drops the refused request |
| `refused-gap` | `requestNotSubtype` | 2 | `g302`, `g341`: `Scope.make("parallel")`; the printer drops the refused request |
| `refused-gap` | `valueNotSubtype` | 2 | `g257`, `g329`: `undefined` provided for a number service; tsgo accepts it |
| `refused-silent` | `errorNotAdmitted`, `cause`, `predicateNotBool` | 13, 6, 3 | as the table lists them |

The observed codes of the 62 `refused-unmapped` rows are 2345, 2322, 2375, 2769, 2739, 2740,
1107, 1345, 7005 and 7034 (tested, the table's column). I did not extend `codesOf`
(`src/Effect4/Codegen/Diagnostics.lean`), as the brief rules.

### 3.4 The controls of the lane

| Control | Result |
| --- | --- |
| The tsgo command line over the lane's work project | the same 671 pairs of program and code as the lane; none outside `programs/` (tested) |
| K0: the lane in a skeleton tree with no `harness/truth/node_modules` | `PASS`, the same table (tested) |
| K1: a prelude that does not check, with `--promote` | refusal `prelude.ts: TS2322`, exit 1, table kept (tested) |
| K2: a later file that the prelude re-exports | `PASS`, 9 files, 12 controls (tested) |
| K3: the one list without the atom `some` | the table differs, exit 1 (tested) |
| K4: the prelude imports a file outside `harness/truth` | refusal by name, exit 1 (tested) |
| K6: the one list names what the prelude does not export, with `--promote` | refusal `the header of a module: TS2305`, 408 times, exit 1, table kept (tested) |
| K7: the tree's prelude lacks a file that it imports | refusal `prelude.ts: TS2307`, exit 1 (tested) |

`tsdiag-lane-controls.sh.txt` runs K0 to K8, and `tsdiag-lane-controls.log.txt` holds the run.

## 4. Part 2: the ingest's census

### 4.1 The cause, reproduced

The coverage step refuses at the base: `missing eff coverage: restore` (reproduced,
`ingest-red-at-base.log.txt`). The script stops there, so no later step ran since `85c61eb8`.
The same step would then refuse `getInterruptible`, which no skeleton of the corpus builds
(reading).

### 4.2 The corpus and the walkers

**The corpus builds the form.** `maskProbes` (`tools/Drivers/ForeignCorpus.lean`) holds four
programs. Each is well typed and readable, and its round trip gives it back (tested by a
probe, `MaskProbe.out.txt`).

| Probe | Shape |
| --- | --- |
| `mask-restore` | one restore site under its mask |
| `mask-nested` | two masks, and a restore site of each saved state inside the inner one |
| `mask-gen` | a generator that binds the saved state with `const` |
| `mask-layer` | a layer and a reference to it under a restore site |

The driver writes 22398 sources, 84 more than at the base (tested). `check-corpus.ts` pins the
new count.

**Three hand walkers lagged at `restore`.** Each took a constructor with no case as a leaf,
without a word.

| Walker | File | Lagged at |
| --- | --- | --- |
| `childrenOf` | `ts/eff/read.ts` | `restore` |
| `walkProgram` | `ts/eff/ingest/ck.ts` | `restore` |
| the coverage walker | `ts/eff/ingest/check-coverage.ts` | `restore`, `catchIf` and `LayerTerm.mergeAll` |

Each now has a case for every constructor, a leaf too. Each switch ends in a default that
takes `never`. So tsgo refuses the file when a constructor of the generated types has no case
(tested: `controls.out.txt`, B1 to B4, each with TS2345).

**I chose the type level, as the coordinator prefers.** The constructor lists are the
generated types of `ts/eff/eff.gen.ts`, and no second list exists. The control that fails is
`bun run typecheck` of `ts/eff`, a step of `make check-ts-reader` and of the ingest's script.
`ts/eff/test/red/walkers.red.ts` is the red twin: four walkers, each with a case for every
constructor of a sort but one. `ts/eff/test/read.test.ts` runs tsgo on the red project and
pins each refusal: TS2345 with `restore`, `ret`, `getInterruptible` and `ref`. The coverage
walker also checks a node's tag against the schema's cases when it runs.

**The lag of `childrenOf` was a defect of two readers.** Lean prints a module whose layer
declaration sits under a restore site, and Lean reads it back (tested by a probe,
`MaskProbe.out.txt`). The TypeScript reader refused that module with `shape "module"`
(reproduced, `probes.out.txt`). The oxc engine walks through `childrenOf`. With the two rows
read and `childrenOf` as at the base, it lifts a layer constant under a restore site to a
wrong program. The reference keeps its definition's index, and the key table is empty
(reproduced, `controls.out.txt`, A1). The probe `mask-layer` now holds both walkers to the
case: with either walker as before, the corpus refuses `baseline-mask-layer` (tested,
`controls.out.txt`, A1 and A2).

### 4.3 What the two engines read

Both engines read the mask's two printed rows, in their printed spelling alone.

- **The getter.** `Effect.uninterruptibleMask((r) => Effect.succeed(r))`: one arrow of one
  plain parameter, whose body answers that parameter. The head may come through any import of
  `effect`. It lifts to `withFiber getInterruptible`.
- **A restore site.** `pipe(body, saved)` with two arguments, where `saved` is a binder. It
  lifts to `restore (var i) body`. `Function.pipe` is the same head.
- **The printed seam of `ck.ts`** reads `pipe(body, saved)` with any term for `saved`, as
  Lean's reader does. The oxc seam already read both rows through the table.

Every other use is refused, and the two engines refuse alike (tested,
`ts/eff/ingest/test/foreign.test.ts`). The same file pins the two rows under a form that
inserts a binder: a saved state bound outside keeps its level (tested, three cases).

| Source | Verdict of both engines |
| --- | --- |
| the native callback spelling, `(restore) => restore(e)` | `E-ARG-CLOSURE`, `unknown closure: Effect.uninterruptibleMask` |
| a callback with another body, two parameters, a default, `async`, a block or no argument | the same refusal |
| `body.pipe(saved)`, `saved(body)`, `pipe(body, saved, saved)` | `E-OP-RECEIVER`, `unresolved receiver: saved` |
| `pipe(body, name)` where no binder holds `name` | `E-OP-RECEIVER` |
| `pipe(body, Effect.flatMap(k))` | piping, as before |

The reading is syntactic, as every reading of the engines is. A binder that is no saved state
lifts to a `restore` that the checker then refuses (`maskRestoreExpected`).

At the base the two engines refused the getter with different codes: `E-ARG-DYNAMIC` and
`E-NODE` (reproduced, `probes.out.txt`).

### 4.4 Each step of the script

I ran a copy of `scripts/check-ingest.sh` from the worktree's root, through the slot script.
The copy differs by two lines (`check-ingest-noinstall.diff.txt`): the install line is gone,
and `repo_root` is the current folder. The environment is the Makefile's: `EFFECT4_CORPUS` and
`E4_LEAN_CORPUS` name the worktree's `.lake/corpus`. `TMPDIR` names the seat's scratch folder.
`make corpus` ran first, as the rule's prerequisite. Every result below is tested, in one run
at `c540da33` (`ingest-run.log.txt`). One test followed that run, in `49457227`. The script's
two steps in `ts/eff` then ran again: exit 0, and 738 tests pass.

| Step | Result |
| --- | --- |
| the lock file's sum, before and after | equal: `55adfdf4…5145` |
| `bun install --frozen-lockfile` | **not run** |
| `bun ts/eff/ingest/cli.ts --help` | exit 0 |
| `lean_run tools/Drivers/Corpus.lean --foreign … 400 4` | `foreign 22398; isolated 21; products 11520; forms 19 at four depths` |
| `bun ts/eff/ingest/check-coverage.ts` | `PASS oracle coverage: 26 Eff, 6 statements, 12 actions, 10 layers, 58 native rows; 19 forms at four depths` |
| `cli.ts gate`, the printed corpus | `PASS printed: 408 exact JSON/wire comparisons on each parser` |
| `cli.ts gate`, the foreign corpus | `PASS foreign: 22398 exact JSON/wire comparisons on each parser with shared form lowering, exact key tables and complete verdict agreement; batch bound 500` |
| `check-corpus.ts inclusion` | `PASS inclusion: 408 printed modules, 323 lifted by both engines`; 85 refused alike: `E-FAIL-NOT-DOCUMENTED` 61, `E-ARG-DYNAMIC` 21, `E-REF-UNBOUND` 3 |
| `check-metamorphic.ts printed` | `PASS source edits: printed, 408 fixtures × 6 transformations × 2 engines` |
| `check-metamorphic.ts foreign` | `PASS source edits: foreign, 22398 fixtures × 6 transformations × 2 engines` |
| `check-metamorphic.ts negative`, the refusals | `PASS`, 22 fixtures |
| `check-metamorphic.ts negative`, the witnesses | `PASS`, 2 fixtures |
| `bun run typecheck` in `ts/eff` | exit 0 (tsgo 7.0.0-dev.20260629.1) |
| `bun test` in `ts/eff` | 737 pass, 0 fail, 27 files |
| `render-readme.ts --check` | `PASS ingest README: generated tables match` |
| `dune build --root ocaml eff/effect4_eff.cma` | exit 0 (the effect4 switch) |
| `ocamlc … check-wire.ml` | exit 0, with warning 24 on the file's name |
| `check-wire` over both corpora | `PASS OCaml exact decoder and JSON oracle: 22806 programs` |
| `bun ts/eff/ingest/check-fidelity.ts` | `PASS fidelity: four original/reprinted programs agree` |
| the script's last line | `PASS ingest`, exit 0 |

### 4.5 The install line

The line did not run. `lock-vs-install.py.txt` compares the lock with the install, and it
installs nothing. It reports: 47 packages in `ts/eff/bun.lock`, 18 installed at the locked
version, none at another version, 29 of another platform (tested). The link in this worktree
names the coordinator's packages.

Proposal: delete the line. The Makefile's rule `ts/eff/node_modules` is then the one place
that installs, and it already keeps a link. The script keeps its two comparisons of the lock's
sum. It gains one read-only comparison of the installed versions with the lock, and it stops
with the name of the Makefile's rule when one differs.

## 5. Commands and results

`SLOT` is `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Each `make` call writes
`-o build -o ts/eff/node_modules -o harness/truth/node_modules`. Each result is tested. The
evidence folder holds each script and probe of the scratch folder, with `.txt` after its name.
`acceptance.log.txt` holds the five targets at `c540da33`, and `acceptance-at-head.log.txt` at
`49457227`.

| Command | Result |
| --- | --- |
| `SLOT make … check-tsdiag`, at the base | exit 2: the table differs; `typed-errors 136` |
| `bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out <scratch> --emit`, before and after `c6f8b535` | `emitted 73 of 73 programs`; `diff -r` with `harness/truth/generated` is empty |
| `node …/tsgo --noEmit -p harness/truth/tsconfig.json` | exit 0; `--listFiles` names `harness/truth/module-imports.ts` |
| `SLOT make … gen-tsdiag` | `tsdiag: wrote generated/tsdiag-agreement.tsv`, then `PASS check-tsdiag` |
| `SLOT make … check-tsdiag`, at `c540da33` | `11 controls hold`; `PASS check-tsdiag`; at `49457227` make has nothing to do |
| `bash tsdiag-lane-controls.sh` | K0 to K8 as section 3.4 lists them |
| `bash tsdiag-cli-crosscheck.sh` | 671 pairs from the command line, 671 from the lane, equal; 0 outside `programs/` |
| `SLOT bash <copy of the script>`, at the base | exit 1 at the coverage step |
| `SLOT lake build Drivers.ForeignCorpus Drivers.Corpus` | `Build completed successfully (157 jobs).` |
| `SLOT lake env lean -DwarningAsError=true MaskProbe.lean` | exit 0; four probes typed, readable, round trip the same |
| `SLOT make … corpus`, then `SLOT lake build Tools.GeneratedStamp`, then the copy of the script | section 4.4; exit 0 |
| `bash controls.sh` | A0 exit 0; A1 to A3 exit 1; B0 exit 0; B1 to B4 TS2345 |
| `bash probes.sh` | section 4.2 and 4.3; `probes.out.txt` |
| `bun run check-styles.ts <scratch>/foreign`, in `ts/eff` | `PASS styles construction: 22398 indexed files, 11541 configurations`; tsgo's API and oxc accept every source |
| `bash foreign-mask-types.sh` | tsgo exit 1; 7 of 84 sources have a diagnostic (finding 9) |
| `SLOT make … check-ts-reader`, at `c540da33` and at `49457227` | `files 481: matched 416, mismatched 0, refused with oracle 0`; 737 tests pass, then 738 |
| `SLOT make … check-ingest-smoke`, at both commits | `PASS printed: 408` |
| `SLOT make … gen-fixtures`, at both commits | `PASS generate: requested producers ran in dependency order`, then nothing to do; `git status` empty |
| `SLOT make … check-docs`, at both commits | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `SLOT lake build` of the 12 imports of `harness/truth/Truth.lean`, then `SLOT make … check-truth` | `Build completed successfully (494 jobs).`; `PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; the regenerated modules type-check` |
| `python3 scripts/check-truth-release.py --self-test` | `self-test: 88 of 88 controls as expected` |
| `bun test` over the four host tests of the truth lane | 23 pass |
| `python3 scripts/check-language.py --strict` on this receipt | `PASS`, no finding |

## 6. Axiom output

No declaration of `src` or `Test` changed. `tools/Drivers/ForeignCorpus.lean` is a tool,
outside the axiom gate. The gate did not run.

## 7. Evidence

Every result of this receipt is tested, reproduced or a reading, and none is proved. No
theorem is stated.

- **Bounded.** Each count is over one corpus: 408 printed programs (400 at depth 4, and the 8
  wire programs), and 22398 foreign sources. The diagnostics table is a function of that corpus.
- **Host-only.** The table rests on one compiler and one runtime: tsgo 7.0.0-dev.20260629.1
  and effect 4.0.0-rc.112. The fidelity step rests on bun 1.4.2 and the pinned runtime.
- **One machine.** Every run is on this Mac: node 22.23.2, bun 1.4.2, OCaml 5.1.1 and dune
  3.24.2 of the effect4 switch.
- **The corpora.** The printed corpus is the worktree's `.lake/corpus`, cut at the base by
  `make corpus`. No run read the coordinator's corpus. As I write, the coordinator's
  `generated/corpus-index.tsv` has the same bytes as the worktree's (tested, `cmp`).

## 8. Landed theorems and their placement

None.

## 9. Open obligations

None of proof. Nine findings stand open, and I repaired none of them.

1. **Three more hand copies of the import header exist.** `harness/truth/session/run-keyed.ts`
   copies the names of `effect` and the type list, and both equal the one file today.
   `printedHeader` of `ts/eff/ingest/fidelity/roundtrip.ts` lacks `Data`, has 10 of the 43
   atoms, and has no helper and no type. `asModule` of `ts/eff/ingest/check-corpus.ts` lacks
   `Data` and `pipe`.
2. **The inclusion step will misread a printed restore site.** Its wrapper imports no `pipe`,
   so the foreign contract would refuse the site with `E-OP-RECEIVER`. No program of the
   printed corpus holds the form today.
3. **`copy_prelude` of `scripts/lib/truth_host.py` lists the prelude's four files by hand.**
   The truth lane and the corpus lane use it. A later sibling fails them, with an error of the
   module system.
4. **The two engines refuse five shapes with different codes.** They do so at the base and at
   the head alike (reproduced, `probes.out.txt`). Row 168 owes the ruling. The shapes:
   - a known head as a pipe segment;
   - the mask as a call segment;
   - a literal as a segment, in two spellings;
   - a wrong count of arguments.

   A second probe reads 23 spellings near the mask's rows (`probes-2.out.txt`). It gives three
   more shapes of that kind: a call of the getter's answer, `undefined` as a segment, and
   `pipe()`. At the base the engines disagree on 22 of the 23, and at the head on those three.
5. **`check-tsdiag` and `check-ingest` run in a sweep only.** Both reds stood for that reason.
6. **`docs/STATE.md` describes both lanes as red** in four lines. They are stale at the merge.
7. **The census over the pinned projects did not run.** A unit with `pipe(e, binder)` moves
   from `E-OP-RECEIVER` to a lift in both engines.
8. **The `Files` table of `ts/eff/README.md`** does not name `test/red/walkers.red.ts`.
9. **tsgo types 77 of the 84 mask sources of the foreign corpus** (tested, an extra probe:
   `foreign-mask-types.out.txt`). No lane types that corpus, and `check-styles.ts` reads syntax
   alone. Four sources of the style `named` import `currentTimeMillis` from `effect/Effect`,
   which does not export it. `generated/row-citations.tsv` already records the row `clockNow`
   as refused. Three sources of the curried style fail at the restore site, because tsgo gives
   the continuation's parameter the type `unknown`. Both causes hold for the style, with or
   without a mask.

## 10. Proposals

### 10.1 The Makefile

1. Give `$(CHK)/tsdiag` every file that the lane reads. Today it names `prelude.ts` and the
   session files. It lacks `harness/truth/module-imports.ts`, `ts/eff/profile.gen.ts`,
   `ts/eff/eff.gen.ts`, `prelude-atoms.gen.ts`, `records.ts` and `tuples.ts`. A wildcard over
   `harness/truth/*.ts` cannot lag behind a new sibling.
2. Add `harness/truth/module-imports.ts` and `harness/truth/tuples.ts` to `TRUTH_SOURCES`.
3. Add four folders to `TS_EFF_SOURCES`: `ts/eff/ingest/fidelity`, `ts/eff/ingest/census`,
   `ts/eff/ingest/fixtures` and `ts/eff/test/red`. The lanes read them, and the variable does
   not name them.
4. Put `check-tsdiag` in the tier that runs with a merge. It needs node and the corpus that
   `check-gen` already cuts. One run of the lane took 1.3 seconds here (tested, one run).
5. Split the ingest's first steps into a target of that tier: the foreign corpus and the
   coverage step. They need one run of the corpus driver and one run of bun.

### 10.2 Can `childrenOf` be generated?

Yes, from what the TypeScript generator already reads.

- **The Lean side.** `emitNodeLenses` (`tools/Effect4Gen/Authoring.lean`) writes `Node.child`
  from the constructor declarations alone. It writes one arm for each node-typed argument of
  a constructor, at that argument's rank. It reads no table.
- **The TypeScript side.** `tools/Drivers/TsGen.lean` reads every family of the closed world,
  with each constructor's arguments and their sorts. `emitFamilyJson` and `emitFamilyWire`
  already write one switch for each family.
- **What an emitter of `childrenOf` needs.** It needs the seven node sorts: the constructors
  of `Node` (`src/Effect4/Program/Node.lean`). It needs the carrier rule of the three spines,
  which the generator has. A `nil` and `cons` family is an array, and its children are its head
  and its tail. The types `IrNode` and `Child` move to the generated file.
- **What it does not need.** `tools/Effect4Gen/binders.json` holds binders, and a child has
  none. A generated walk that tracks binder depths would need it.

The coverage walker could then fold over the generated children. `walkProgram` could too, but
the two engines stay two walks by DI-88, so that step is the owner's.

### 10.3 Every hand traversal of `Eff` in `ts/eff` and `harness/`

I searched `ts/`, `harness/`, `tools/target/` and `scripts/` for a case of a constructor's
name, outside the generated files (reading, one `git grep`).

| Traversal | File | Hand copy | Lagged at `restore` |
| --- | --- | --- | --- |
| `childrenOf` | `ts/eff/read.ts` | yes | yes |
| `walkProgram` | `ts/eff/ingest/ck.ts` | yes | yes |
| the coverage walker | `ts/eff/ingest/check-coverage.ts` | yes | yes, and at `catchIf` and `mergeAll` |
| `CompilerReader.eff`, a reader with a case for each printed head | `ts/eff/ingest/ck.ts` | yes | yes: it read neither row |
| the walk of `Normalize.finish` | `ts/eff/ingest/oxc.ts` | no: it calls `childrenOf` | through `childrenOf` |
| `readEff` and its table | `ts/eff/read.ts`, `ts/eff/templates.gen.ts` | no: the rows are generated | no |
| `effJson`, `writeEff` | `ts/eff/json.gen.ts`, `ts/eff/wire.gen.ts` | no: generated | no |
| `expandTemplate`, over the form templates | `ts/eff/ingest/forms.ts` | hand, with no default | not a walk of `Eff` |

`harness/` and `tools/target/` hold no traversal of `Eff`. Seat MASK's commit edited the
hand files of the OCaml estate (reading of its file list). I did not read them.

### 10.4 Where the one file of imports lives

`harness/truth/module-imports.ts` stands beside the prelude, whose exports it names. The
ingest's two copies (finding 1) could read it only by an import from `ts/eff` into
`harness/truth`. The other direction exists today. Two options: move the file to `ts/eff`, or
accept that one import. I recommend the move only if the ingest's copies are to be removed.

## 11. Proposed decisions rows (proposals only)

One row, as a record of row 289's two repairs.

| Field | Text |
| --- | --- |
| Question | What the repair of the two red lanes landed, and what it leaves open |
| Landed | (1) One file holds a printed module's imports. (2) The diagnostics lane copies the prelude's files as the compiler names them, refuses its own defects, and runs its controls on every run. (3) The table is promoted with no `typed-errors` row. (4) The foreign corpus builds four mask programs. (5) Both engines read the mask's two printed rows, and refuse every other use alike. (6) Three hand walkers have a case for every constructor, held by the type check |
| Bounds | DI-88 and row 215: no foreign spelling of a form is read, and the native callback spelling is refused |
| Open | the install line of the ingest's script (owner); three hand copies of the header; the generation of `childrenOf`; the Makefile's prerequisites and tiers; the five residual refusals of row 168 |

## 12. Not run

- `bun install --frozen-lockfile`, and any other install or download.
- `make check-ingest` and `scripts/check-ingest.sh` as a whole, because of that line.
- `make check-corpus`, `make check-target`, `make check-host-protocol` and the release lane's
  host run. `run-truth.ts` changed, and `make check-corpus` runs it too: the merge owes that
  lane.
- `make check`, `make check-full`, `make check-gen`, `make check-slow`, `make check-ocaml`,
  `make check-schema-ts` and `lake build`.
- The census over the pinned projects (`cli.ts census`).
- `tsc`, and any `typescript` below 7.
- Any git command in the coordinator's checkout, and any push.
