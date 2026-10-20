# 2026-10-20 seat Opus receipt: retire the truth differential

**The one thing to know before merging:** `make check-sweep` fails at `check-docs` on two
mentions of `make gen-truth` in `docs/core/decisions.md`, rows 319 and 322. Only the
coordinator edits the register. The Bun runner `harness/truth/run-truth.ts` stays, against the
brief's deletion list: the reader lane's `bun test` reaches it through the ingest's fidelity
tool.

## Base and head

- Branch `refactor/phase1-phase3`, in the checkout `/Users/pooks/Dev/lean4-effect4`, with no
  worktree.
- Base: `fa7bdc304` (`fa7bdc304b51027313a2b3d02c32df400c0e91df`).
- First commit: `9be0db77c` (`9be0db77ca4e330e6f2d8f8e5c79442ad10560c0`),
  `Truth: retire the differential; keep the corpus producer`.
- Head: the commit that adds this receipt, `Docs: the truth harness after the differential's
  retirement`. Its parent is the first commit.

## The inventory

The owner retired the truth lanes from the gates on 2026-10-18. On 2026-10-20 the owner asked
to retire the old truth modules. The slice keeps a file that a live gate, the printed
TypeScript programs or the codec lane reads. It deletes a file that none of them reads. The
consumer column names each reader, found by reading its source (evidence: reading).

| File | Class | Consumer | Kept or deleted |
| --- | --- | --- | --- |
| `harness/truth/prelude.ts` | kept, live | every printed module; the target lane (`tools/target/profile.ts`, `tools/target/prelude.test.ts`); the diagnostics lane (`harness/tsdiag/run-tsdiag.mjs`); the to-do project; the ingest's fidelity tool | kept; three comments now cite deleted tests |
| `harness/truth/control.ts`, `records.ts`, `tuples.ts`, `prelude-atoms.gen.ts` | kept, live | the prelude re-exports them (`PRELUDE_SOURCES`) | kept; the generated comment no longer names a deleted control |
| `harness/truth/session/`, 22 files | kept, live | the prelude imports `keyed-protocol.ts`; `apps/todo/server.ts` imports three; the diagnostics and service-identity lanes; `make gen-host-protocol` writes two | kept |
| `harness/truth/service/`, 5 files | the host-protocol lane, retired on 2026-10-18 | `scripts/check-host-protocol.py` runs it; `apps/todo/EmitTodo.lean` and `apps/todo/consumer.ts` name it | kept |
| `harness/truth/schema-codec/`, 3 files | kept, live | the codec lane, run by hand: the acceptance check of moves J and G | kept |
| `harness/truth/node_modules`, an untracked link | kept, live | the prelude resolves `effect` through it for the target lane's queries; the codec lane | kept |
| `harness/truth/run-truth.ts` | kept, live; on the brief's deletion list | `bun test` of the reader lane imports `ts/eff/ingest/fidelity/roundtrip.ts` through `ts/eff/ingest/test/fidelity.test.ts`; that module reads this file at load and runs its `--observe` mode | kept, unchanged |
| `harness/truth/IngestPrint.lean` | kept, live; decided by consumers | the same module reads it at load and runs it | kept, unchanged |
| `harness/truth/prelude-inventory.ts` | kept, live | `run-truth.ts` imports it | kept |
| `harness/truth/tsconfig.json` | kept | no gate; `scripts/check-host-protocol.py` extends it; `src/Effect4/Codegen/Diagnostics.lean` and the probes copy its options | kept; the include list drops the deleted files |
| `harness/truth/Truth.lean` | kept, the corpus | `make gen-truth-corpus` | trimmed to the corpus, the host inputs and the manifest writer: 2779 lines to 1521 |
| `harness/truth/corpus.json` | kept, the corpus | `tools/target/profile.ts` and `tools/target/profile.test.ts` read `name`, `type`, `scopeKey` and `hostRows`; `tools/Tools/RowTypes.lean` reads `hostRows`; the OCaml engine's cross face reads `run` (`ocaml/engine/test/reference/corpora.ml`) | kept, regenerated with those fields alone |
| `harness/truth/generated/*.ts`, 93 files | kept, the corpus | `ts/eff/check.ts` in the reader lane; `tools/target/profile.ts` in the target lane | kept, regenerated |
| `harness/truth/result.json`, `result.md` | differential | `scripts/check-truth.py`, `scripts/check-corpus.py`, `scripts/check-truth-release.py`; the keys of the reader and target lanes | deleted |
| `harness/truth/corpus-results.tsv`, `corpus-known-differences.md` | differential | `scripts/check-corpus.py` | deleted |
| `harness/truth/tapes/`: `pKv`, `pSqlCatch`, `pSqlExit`, `pSqlFail`, `pSqlOrDie`, `pSqlite` | differential | the base `Truth.lean`; `scripts/check-truth.py` | deleted |
| `harness/truth/build-ledger.tsv`, `build-ledger.run.json` | differential | `scripts/check-truth-release.py`, `scripts/lib/truth_ledger.py` | deleted |
| `harness/truth/check-truth.ps1`, `LANE.md`, `RELEASE-LANE.md` | differential | the lanes' notes and the Windows runner; documents cite them | deleted |
| `harness/truth/select-controls.ts`, `P2b.lean` | differential | `scripts/check-truth.py`; `harness/authoring-branches/check-helper.py`, run by hand, copies the first | deleted |
| `harness/truth/records.test.ts`, `catch-if.test.ts`, `native-queries.test.ts`, `prelude-inventory.test.ts`, `if-case.test.ts` | the prelude's tests under Bun (`TRUTH_HOST_TESTS`) | `scripts/check-truth-release.py --host-tests`; no live lane runs them | deleted |
| `harness/truth/maps.test.ts`, `tuples.test.ts` | the prelude's tests under Bun, outside `TRUTH_HOST_TESTS` | none since 2026-10-03 | deleted |
| `harness/truth/records.typecheck.ts`, `tuples.typecheck.ts`, `folds.typecheck.ts`, `term-rows.typecheck.ts`, `literals.typecheck.ts`, `queue-steps.typecheck.ts`, `mask.typecheck.ts`, `maps.typecheck.ts` | compiler controls | `scripts/check-truth.py`; the diagnostics lane's script reads the prelude's closure alone, and its key's wildcard only hashes these files | deleted |
| `harness/truth/corpus-check/`, ignored, 560 files on disk | differential | `scripts/check-corpus.py` wrote it | untracked; left on disk |
| `scripts/check-truth.py`, `check-truth-release.py`, `check-corpus.py`, `lib/truth_ledger.py`, `lib/truth_host.py` | differential | each other; no target since 2026-10-18 | deleted |
| `scripts/check-host-protocol.py` | the host-protocol lane, retired on 2026-10-18 | no target; it reads the kept `session/` and `service/` | kept |
| `scripts/generate.py` | live | a comment cites the truth manifest's timing | kept |
| Makefile `gen-truth` | producer | no gate | renamed `gen-truth-corpus`: Lean alone, after the derived group, with no Bun run |
| Makefile `gen-truth-ledger`, `TRUTH_HOST_TESTS` | differential | none | deleted |
| Makefile `clean-check`'s line for `harness/truth/truth-check-*` | differential | the work folders of `scripts/check-truth.py` | deleted |
| Makefile `TRUTH_GENERATED` | live | the keys of the reader and target lanes | kept, without `result.json` and `result.md` |
| Makefile `CHECK_ENVIRONMENT`'s `EFFECT4_RELEASE_NODE_MODULES` | differential | `scripts/lib/truth_host.py` alone | deleted |
| Makefile `harness/truth/node_modules`, `$(GEN)/host-protocol`, `PRELUDE_SOURCES`, the diagnostics key's wildcard, the link line of `doctor` | live | as above | kept |

## Changed files

The first commit holds the deletions and the trim:

- 37 deleted files, 29666 lines: the rows marked "deleted" above.
- `harness/truth/Truth.lean`: the driver takes `--corpus <dir>` and writes `<dir>/corpus.json`
  and `<dir>/generated/<name>.ts`. The recorder's events, schedule and fiber numbering go. So do
  the sync run, the tapes and their reader, and the mode of the generated corpus. Three imports
  and every receipt but one go too.
- `harness/truth/corpus.json`: regenerated with `name`, `type` and `run` per program.
- `harness/truth/generated/*.ts`, 93 files: regenerated. Each changes one header line.
- `harness/truth/tsconfig.json`: the include list and the comment drop the deleted files.
- `Makefile`: `gen-truth` becomes `gen-truth-corpus`, with Lean alone and no Bun run. The
  release lane's target, its test list and the work-folder cleanup go. `TRUTH_GENERATED` drops
  the two result files, and `CHECK_ENVIRONMENT` drops `EFFECT4_RELEASE_NODE_MODULES`.

The second commit holds the documents:

- `docs/GENERATED.md`: the truth row describes the producer alone. The retirement paragraphs
  say that the differential is gone.
- `docs/ARCHITECTURE.md`: the row of `harness/truth`.
- `harness/README.md`: the paragraph on `truth/` and the list of outside oracles.
- Docstrings and comments that named a deleted file now cite `git:fa7bdc304:<path>`:
  `Test/Api/PackagesContract.lean`, `Test/Codegen/TermRows.lean`,
  `Test/Dogfood/P4RateLimiter.lean`, `Test/Program/BoundsControls.lean`,
  `Test/Program/MaskClaims.lean`, `Test/Program/NativeAtomContract.lean`,
  `Test/Program/QueueFaces.lean`, `Test/Program/TypingCheckContract.lean`,
  `tools/Drivers/Corpus.lean`, `tools/Tools/RowTypes.lean`, `tools/target/corpus.ts`,
  `harness/truth/prelude.ts` and `ts/release/package.json`.
- `tools/Effect4Gen/PreludeAtoms.lean` and its output `harness/truth/prelude-atoms.gen.ts`: the
  generated comment no longer names its deleted compiler control.
- The repairs of `make check-sweep`: 27 path citations, on 25 lines of six documents:
  `Test/Counterexamples/REGISTER.md`, `Test/contracts/faces.contract.md`,
  `docs/DESIGN-ISSUES.md`, `docs/UPSTREAM-BACKLOG.md`, `docs/core/controlled-english.md` and
  `harness/authoring-branches/README.md`.
- This receipt.

Left uncommitted: the sweep's 12 path citations, on 8 lines of `docs/core/decisions.md`, as the
brief asks.
`tools/view/make_videos.py` is the owner's untracked file.

## Commands and results

Every Lean and make command ran through the runner, one at a time, from the checkout.

1. `python3 /private/tmp/seams-lean-one.py lake build $(python3 scripts/lean-imports.py harness/truth/Truth.lean)`,
   at the base file's 19 imports: `Build completed successfully (1292 jobs)`, exit 0.
2. `python3 /private/tmp/seams-lean-one.py lake env lean -M4096 $(python3 scripts/lean-imports.py --dynlibs harness/truth/Truth.lean) --run harness/truth/Truth.lean <scratch>/base/corpus.json --tapes harness/truth/tapes`,
   the base producer into the scratch folder: `wrote 93 programs`, exit 0, 12.2 s.
3. The same command with `--corpus <scratch>/new`, on the trimmed file: `wrote 93 programs`,
   exit 0, 6.6 s.
4. `python3 /private/tmp/seams-lean-one.py make gen-derived`, after the generator's comment edit:
   `PASS generate: requested producers ran in dependency order`, exit 0. One output moved,
   `harness/truth/prelude-atoms.gen.ts`.
5. `python3 /private/tmp/seams-lean-one.py make gen-truth-corpus`:
   `wrote 93 programs to harness/truth: corpus.json and generated/`, exit 0, 23.9 s. Its
   outputs equal the scratch run of step 3, byte for byte.
6. `python3 /private/tmp/seams-lean-one.py make check-ts`: exit 0, 34.8 s.
   - `PASS check-tsgo: no typescript below 7 under ts/, harness/ or tools/`.
   - `target conformance [effect@4.0.0-rc.112/adapter]: PASS; 104 expected, 104 attempted, 104 resolved, 0 mismatching, 0 refused`.
     `bun test tools/target` passed 28 of 28.
     `PASS assignability: no pair the order accepts is refused by the target`, over 742 pairs.
   - `files 501: matched 416, mismatched 0, refused with oracle 0, accepted without oracle 74, refused without oracle 11`.
     `bun test` in `ts/eff` passed 802 of 802.
   - `PASS check-tsdiag: no program this checker types is refused by TypeScript`, with 12
     controls over 408 programs.
   - `PASS printed: 408 exact JSON/wire comparisons on each parser with shared form lowering`.
   - `PASS service identity: checked API emissions, inferred requirements, two TS2375 controls, four runtime outcomes`.
7. `python3 scripts/check-docs.py`, read-only, before the sweep: 42 stale references in 7 of
   105 documents, 40 paths and 2 make targets.
8. `python3 /private/tmp/seams-lean-one.py make -k check-sweep`: exit 2, in 5 min 26 s.
   - `PASS check-roots: the module-closure, library-root and axiom gates`, in 244.8 s.
   - `check-docs` repaired 39 path citations, on 33 lines of 7 documents, then
     `FAIL check-docs: 2 stale reference(s) in 1 of 105 documents`: rows 319 and 322 of
     `docs/core/decisions.md` name `make gen-truth`.
   - `PASS check-language self-test: 48 of 48 controls`, then
     `FAIL check-language: 1 finding(s) in 2 strict document(s)`: a sentence of 27 words in
     `AGENTS.md`, the one on the five modeling rules. The slice leaves `AGENTS.md` unchanged, so
     the finding predates it.
   - `PASS census: recorded`, `PASS schema-pins: recorded` and `PASS tools: recorded`.
   - `PASS check-gen: every Lean-only generated file is what its generator emits`.
9. `python3 -I scripts/check-language.py --show docs/research/2026-10-20-retire-truth-differential/receipt.md`:
   no finding.

The flag `-k` lets the sweep run every check past the first failure, so each check has a result.

## The byte comparison

The renamed target ran once in place. A script compared its outputs with the committed files at
`fa7bdc304`, and with the base producer's run of step 2 (evidence: reproduced).

- **The modules.** All 93 equal the committed bytes, but for one header line:
  `Regenerate: make gen-truth` becomes `Regenerate: make gen-truth-corpus`. The rename causes
  it. The base producer's run gives all 93 committed modules byte for byte.
- **The kept fields.** The manifest keeps `generated`, `scopeKey`, `hostRows` and `programs`. A
  program keeps `name`, `type` and `run`. `run` keeps `outcome`, `exit`, `exitKind` and
  `fiberCount`. `generated`, `scopeKey`, `hostRows`, every name, the names' order and every
  `type` without `requiresEmpty` equal the committed values.
- **The dropped fields.** No live consumer reads them. At the top they are `format`, `fuel` and
  `regenerate`. In a program they are `scenario`, `wellTyped`, `straight`, `moduleSource`,
  `moduleRefusal`, `expr`, `module`, `moduleInferred`, `runSync`, `genericRows`,
  `runtimeInstanceRows` and `client`. Below those, they are `type.requiresEmpty`, `run.events`,
  `run.schedule`, `run.internal`, `run.frames` and `run.fibers`. The manifest goes from 3508680
  bytes to 29212.
- **`run` differs in nine programs**, for three named causes.
  1. The tapes are deleted. `pSqlite`, `pKv`, `pSqlFail`, `pSqlCatch`, `pSqlExit` and
     `pSqlOrDie` have no built-in host answer. So each run parks at its first host call, with
     the outcome `frontier` and no exit.
  2. The fiber numbering of the comparison is deleted. The exit of `pLateSeen` writes the
     machine's ids, `{"interrupt":3}` and `{"fiber":1}`, where the numbering wrote 2 and 3.
  3. Move G (`3197fde57`, 2026-10-20) changed the defect encoding after the last recording of
     2026-10-15. `pTextOrDie` and `pCatchIfMiss` now write `{"die":"lost"}` and `{"die":3}`.
     The base producer writes the same, so this drift predates the slice.
- **The OCaml engine's reader.** Its cross face reads `run` of 14 programs (`truth_names`,
  `ocaml/engine/test/reference/corpora.ml`). All 14 runs equal the committed ones.

## Axiom output

No module under `src/` changed, so the brief owes no `#axiom_audit`. The changed Lean files are
eight batteries' docstrings, three tool modules' docstrings, one generator's comment and the
script `harness/truth/Truth.lean`. The sweep's roots check builds `Test` and elaborates
`Test/All.lean`: `PASS check-roots: the module-closure, library-root and axiom gates`.

## Evidence

- Reproduced: the regenerated modules and the manifest's kept fields, against the committed
  bytes and against a run of the base producer. One run at this slice; no gate holds the drift.
- Tested: the six lanes of `make check-ts`, on tsgo 7.0.0-dev.20260629.1 and effect
  4.0.0-rc.112. These are finite host runs over named inputs: host-only evidence.
- Tested: the roots, census, schema-pins, tools and drift checks of `make check-sweep`. Its
  documents check and its language check fail, for the reasons in the commands above.
- Reading: the consumer of each file in the inventory, from the sources that the table names.
- Not run: `make check-ocaml`. The brief does not order it. Its cross face reads `run`, and
  the comparison shows that the 14 runs it reads stay unchanged.

## Landed theorems and their placement

None. The slice changes no theorem and states no new claim.

## Kept, and the owner may want it gone

1. `harness/truth/run-truth.ts`, 1167 lines, with `harness/truth/IngestPrint.lean` and
   `harness/truth/prelude-inventory.ts`. The fidelity tool's `--observe` run is their one use.
   The runner's manifest mode reads fields that the trimmed manifest no longer writes, and its
   comments name deleted scripts.
2. `run` in `harness/truth/corpus.json`, with the value wire and `fixtureRun` in `Truth.lean`.
   The OCaml engine's cross face reads it, and reports without gating.
3. `tools/target/corpus.ts`, and the request kinds `truth-widenings` and `p2b-target` of
   `tools/target/checker.ts` with their types in `tools/target/oracle.ts`. Their callers were
   the deleted scripts. The target lane only compiles them.
4. The retired host-protocol lane: `scripts/check-host-protocol.py`, `harness/truth/service/`,
   and the parts of `harness/truth/session/` that only it runs.
5. `harness/truth/tsconfig.json`, which no gate reads.
6. `ts/release/`, the release lane's install recipe. `harness/ref-catalogue` names it by hand.
7. The ignored folder `harness/truth/corpus-check/`, 560 files on disk. The slice deletes no
   untracked file. Remove it by hand.
8. The `.gitignore` lines for `harness/truth/truth-check-*/`, `corpus-check/`, `archive/` and
   the two Lean logs, and its comment on the differential. The brief does not give the file.
9. Five docstrings under `src/` say that the truth lane tests a form:
   `src/Effect4/Codegen/Classes.lean`, `src/Effect4/Laws/Codegen/ListFold.lean`,
   `src/Effect4/Laws/Codegen/Mask.lean`, `src/Effect4/Program/Bounds.lean` and
   `src/Effect4/Laws/Program/Bounds.lean`. They name no deleted file, and an edit would rebuild
   the core.

## Open obligations

1. The coordinator edits rows 319 and 322 of `docs/core/decisions.md`, which name
   `make gen-truth`. Then `check-docs` passes. Proposed text: "the truth lane's producer of
   the time (now `make gen-truth-corpus`)".
2. The coordinator decides whether to commit the sweep's 12 path citations in
   `docs/core/decisions.md`.
3. The sentence on the five modeling rules in `AGENTS.md` has 27 words, so `check-language`
   fails. The file is the coordinator's.
4. `.github/workflows/lean_action_ci.yml` runs
   `make check-truth check-corpus check-schema-codec`. The gates retired these targets on
   2026-10-18, so its job `ts-gates` fails at make.
5. `harness/authoring-branches/check-helper.py` copies the deleted `select-controls.ts` and
   `if-case.test.ts`. It fails until the files come back from `git:fa7bdc304` or the packet
   retires. No gate runs it.
6. The owner's `README.md` says that the sweep includes the release comparison. That comparison
   is gone.
7. `docs/core/controlled-english.md`: the anchor of "differential" is now a Git citation. The
   entries "oracle" and "lane" name the truth lane as an example. A live anchor, such as
   `ocaml/engine/test/test_diff.ml`, is the owner's choice.
8. Face 8 of `Test/contracts/faces.contract.md`, the executed image on rc.112, keeps its row.
   Its evidence is retired, and its status is the owner's.
9. The row of `host-protocol` in `docs/GENERATED.md` and its section on the host protocol still
   name `make check-ts` for the keyed lane, retired on 2026-10-18.

## Proposed decisions rows (proposals only)

- **The truth differential is deleted, and the truth corpus stays.** `make gen-truth-corpus`
  writes `harness/truth/corpus.json` and the 93 printed modules from Lean alone. Two kept
  readers hold retired pieces. The OCaml engine's cross face reads `run`. The ingest's fidelity
  tool runs `run-truth.ts --observe` and `IngestPrint.lean`. The options:
  1. keep both;
  2. delete `run` with the cross face;
  3. move the observation mode beside its one caller, in `ts/eff/ingest/fidelity`, and then
     delete `harness/truth/run-truth.ts`;
  4. retire the fidelity tool.

  Recommended: options 2 and 3, in one later slice.
- **Rows 319 and 322 name the retired target.** Rewrite each `make gen-truth` as in open
  obligation 1.

## The deleted files' lines

`git diff --stat fa7bdc304 9be0db77c` over the 37 deleted paths:

```text
 harness/truth/LANE.md                     |   248 -
 harness/truth/P2b.lean                    |   239 -
 harness/truth/RELEASE-LANE.md             |   254 -
 harness/truth/build-ledger.run.json       |    80 -
 harness/truth/build-ledger.tsv            |    81 -
 harness/truth/catch-if.test.ts            |    54 -
 harness/truth/check-truth.ps1             |    83 -
 harness/truth/corpus-known-differences.md |    24 -
 harness/truth/corpus-results.tsv          |   401 --
 harness/truth/folds.typecheck.ts          |   100 -
 harness/truth/if-case.test.ts             |    61 -
 harness/truth/literals.typecheck.ts       |   287 -
 harness/truth/maps.test.ts                |    32 -
 harness/truth/maps.typecheck.ts           |    15 -
 harness/truth/mask.typecheck.ts           |    49 -
 harness/truth/native-queries.test.ts      |    34 -
 harness/truth/prelude-inventory.test.ts   |    22 -
 harness/truth/queue-steps.typecheck.ts    |    78 -
 harness/truth/records.test.ts             |   141 -
 harness/truth/records.typecheck.ts        |    79 -
 harness/truth/result.json                 | 24563 --------------------------------------------------------------------
 harness/truth/result.md                   |   101 -
 harness/truth/select-controls.ts          |    62 -
 harness/truth/tapes/pKv.jsonl             |     5 -
 harness/truth/tapes/pSqlCatch.jsonl       |     3 -
 harness/truth/tapes/pSqlExit.jsonl        |     3 -
 harness/truth/tapes/pSqlFail.jsonl        |     3 -
 harness/truth/tapes/pSqlOrDie.jsonl       |     3 -
 harness/truth/tapes/pSqlite.jsonl         |     5 -
 harness/truth/term-rows.typecheck.ts      |   270 -
 harness/truth/tuples.test.ts              |    20 -
 harness/truth/tuples.typecheck.ts         |    40 -
 scripts/check-corpus.py                   |   376 --
 scripts/check-truth-release.py            |  1101 ----
 scripts/check-truth.py                    |   235 -
 scripts/lib/truth_host.py                 |   177 -
 scripts/lib/truth_ledger.py               |   337 -
 37 files changed, 29666 deletions(-)
```
