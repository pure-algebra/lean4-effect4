# 2026-10-05 seat M0 receipt: the release's truth lane and its build ledger

**The one thing to know before merging:** only `make check-truth-release` holds the two new
committed files, and that target is in no sweep. After seat T3b's merge, write the build ledger
and its run record again with `make gen-truth-ledger`, which needs a release install assembled
by links.

The slice is tooling only. It changes no Lean file, no machine semantics and no committed
artifact of the pinned lane. The lane note is `harness/truth/RELEASE-LANE.md`. It defines the
words of this receipt: build, pin, release, driver, work copy, ledger line, entry and run
record.

## Base and head

- Branch `seat/m0-release-lane`, worktree `/Users/pooks/Dev/lean4-effect4-m0`, base `f3086de1`.
- `afee3701`: the lane, the build ledger, the run record, the make targets and the lane note.
- `7724a1c2`: a passing lane lists its expected differences.
- `b106d795`: the pinned lane's host tests run on both builds.
- `aded1cec`: the promote refuses a ledger that it could not read whole.
- `b2d63c0d`: the identity rule as a pure function with its controls.
- `fb324abe`: one word of a docstring.
- `38b3ea1c`: this receipt and its evidence folder, in their first form.
- `8cdda516`: the ledger's reader takes a line whose empty trailing columns were trimmed.
- `96e11df9`: a host that does not finish is a refusal with one line. This is the code head,
  and `out/` was written at it.
- Head: the commit that brings this receipt and its evidence to the code head. The seat's
  final message gives its hash.
- Nothing is pushed.

## Changed files

| Path | What |
| --- | --- |
| `scripts/lib/truth_host.py` | 108 lines added, none removed. `release_install`, `select_release`, `compiler_refusal`, `link_install` and the table `RELEASE_ENTRY_POINTS`. `select`, `compiler` and `copy_prelude` are as at the base |
| `scripts/lib/truth_ledger.py` | New. The build ledger's pure part: its grammar, the observation of a runner result, the comparison |
| `scripts/check-truth-release.py` | New. The lane, the promote, and 88 controls (`--self-test`) |
| `harness/truth/build-ledger.tsv` | New. One ledger line for each of the 39 programs of the manifest |
| `harness/truth/build-ledger.run.json` | New. The run record: what the entries were measured on |
| `harness/truth/RELEASE-LANE.md` | New. The lane note |
| `Makefile` | `check-truth-release` (a marker rule, in `CHECKS`), `gen-truth-ledger`, and the help text. Neither target is in `check` or in `check-full` |
| `docs/research/2026-10-05-seat-M0-receipt.md` | This receipt |
| `docs/research/2026-10-05-seat-M0/` | The evidence: `evidence.sh`, `red-controls.py`, `specifiers-against-oxc.ts`, and `out/` |

No file under `src/`, `Test/`, `tools/`, `generated/` or `vendor/` changed. `lakefile.toml`,
`docs/core/decisions.md`, `docs/STATE.md`, `harness/truth/Truth.lean`, `harness/truth/prelude.ts`,
`harness/truth/run-truth.ts`, `scripts/check-truth.py`, `ts/eff/package.json` and the lockfiles
did not change.

## Commands and results

`<S>` is the seat's scratch folder, under the session's scratchpad. `<P>` is the pin's install,
`/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules`, read only. `<R>` is the release install,
`<S>/release/node_modules`. `<slot>` is `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.
The machine has macOS 26.2, bun 1.4.2, node v22.23.2, Python 3.13.14 and GNU Make 3.81.

Every make command below carries `-o build -o ts/eff/node_modules`. In this worktree a plain
`make check-truth` would run a bare `lake build` and `bun install --frozen-lockfile`, and the
brief forbids both. The two flags tell make not to remake those two targets.

### The worktree and the release install

| Command | Result |
| --- | --- |
| `<slot> lake build Effect4 Effect4.Laws.Api.Frontier Effect4.Laws.Program.Denote Test.Counterexamples.Machine.Semantics.InterruptEscape Test.Program.Gen Tools.GeneratedStamp Tools.ProfileJson` | `Build completed successfully (448 jobs).` |
| `<slot> lake env lean -M4096 --run harness/truth/Truth.lean <S>/corpus.fresh.json --tapes harness/truth/tapes`, then `cmp` with `harness/truth/corpus.json` | `wrote 39 programs`; the bytes are equal |
| `ln -s <P> ts/eff/node_modules` and `ln -s ../../ts/eff/node_modules harness/truth/node_modules` | Two ignored links in the worktree, to the pin's install |
| `mkdir -p <R>`; `ln -s /Users/pooks/.bun/install/cache/effect@4.0.1@@@1 <R>/effect`; `ln -s <P>/@typescript <R>/@typescript`; the same for `@types`, `bun-types` and `undici-types` | The release install: five links, no driver, nothing downloaded |
| `diff -rq /Users/pooks/.bun/install/cache/effect@4.0.1@@@1/src vendor/effect-4.0.1/src` | Exit 0, 496 files on each side |

### The pinned lane must not move

| Command | Result |
| --- | --- |
| At the base: `EFFECT4_EFFECT_NODE_MODULES=<P> <slot> make -o build -o ts/eff/node_modules check-truth` | `PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; the regenerated modules type-check` |
| The same command at the code head `96e11df9` (`out/check-truth.log`) | Exit 0. Last lines: `PASS: 38 programs agree on exits, schedules and sync exits; 1 signed divergence(s)` and the same `PASS truth:` line |
| `git diff --exit-code f3086de1 --` over the pinned lane's sources and committed artifacts (`out/pinned-artifacts.txt`) | Exit 0: no byte differs |
| The lane's output at the base against the head's, line by line, temporary folder name and test time aside | No line differs |
| `git diff --numstat f3086de1 -- scripts/lib/truth_host.py` | `108 0` |

### The release lane

| Command | Result |
| --- | --- |
| `EFFECT4_EFFECT_NODE_MODULES=<P> EFFECT4_RELEASE_NODE_MODULES=<R> <slot> make -o build -o ts/eff/node_modules check-truth-release` (`out/check-truth-release.log`) | Exit 0. `self-test: 88 of 88 controls as expected`, then the lane's lines below |
| The control | `effect@4.0.0-rc.112 through the work copy (33 sources) reproduces result.json, result.md, 39 modules and 6 tapes byte for byte` |
| The release | `effect@4.0.1, 34 of 39 programs run; not run, the install has no @effect/sql-sqlite-bun: pSqlite, pSqlFail, pSqlCatch, pSqlExit, pSqlOrDie` |
| What each build ran on (also `harness/truth/build-ledger.run.json` and `out/run.json`) | `effect@4.0.1 ran on bun 1.4.2; tsgo 7.0.0-dev.20260629.1 type-checks its 64 sources; modules: 34, sha256 60a2893025fd06a1; tapes: 1, sha256 b3832d633fddddd0; host tests: 23 pass in 4 file(s)`. The pin's line: 68 sources, 39 modules `07ac4adeb4adea7c`, 6 tapes `0f40a831dab3bd86`, 23 pass |
| The last line | `PASS truth-release: 39 programs match harness/truth/build-ledger.tsv: 30 agree with both builds, 8 with effect@4.0.0-rc.112 only (5 not run on effect@4.0.1), 1 with effect@4.0.1 only, 0 with neither` |
| `make gen-truth-ledger`, with the same variables and flags | `promoted harness/truth/build-ledger.tsv and harness/truth/build-ledger.run.json` |
| The lane six times in a row (`out/six-runs.txt`) | Six passes. The release's `result.json` has one SHA-256 in all six |
| The lane inside `sandbox-exec -p '(version 1)(allow default)(deny network*)'` (`out/no-network.txt`) | Exit 0, the same PASS line. Inside the same sandbox `curl https://registry.npmjs.org/` fails to resolve the host |
| The lane with `EFFECT4_RELEASE_NODE_MODULES` unset; set to `<P>`; set to an install without the compiler (`out/selection-refusals.txt`) | Three refusals, exit 1: `set EFFECT4_RELEASE_NODE_MODULES ...`; `must contain effect@4.0.1 (found effect@4.0.0-rc.112 ...)`; `must contain @typescript/native-preview@7.0.0-dev.20260629.1` |

### The red controls

`out/` holds the output of each. The first five change one committed file, run the lane and put
a kept copy back.

| Control | Result |
| --- | --- |
| A, the brief's. The entry `p42`, `4.0.1 exit`, flipped from `yes` to `no: x` | make exits 2. `FAIL truth-release: p42: 4.0.1 exit: the ledger says "no: x", observed "yes"`, and one more finding: the line then needs a reason and a slice. Put back |
| B, the addendum's first. `pProvideMerge` keeps its schedule difference, and its expected `4.0.1 exit` is altered | make exits 2. One finding: `FAIL truth-release: pProvideMerge: 4.0.1 exit: the ledger says "no: machine success 2, host success 3", observed "yes"`. No finding names its schedule. Put back |
| C. The run record names another module digest and another bun version | make exits 2. Two findings, each with the record's path, the recorded value and this run's value. Put back |
| D. A ledger line cut to five columns, then the promote | The promote exits 1: `the ledger on disk has 39 line(s) and 38 could be read`. The file's bytes do not change. Put back |
| E, a green control. The trailing tabs of the ledger's 30 agreeing lines trimmed, as an editor may leave them | make exits 0 with the same PASS line. Put back |
| The addendum's first, on real data (`red-controls.py`): for each of `pProvideMerge`, `pProvideTwice` and `pMergeAll`, the observed exit is altered, then the observed sync exit | Six refusals. Each names the program and the altered field, for example `pMergeAll: 4.0.1 exit: the ledger says "yes", observed "no: machine success 3, host success 99"`. None names the schedule |
| The addendum's second, on real data: the observation of `pBind` removed from the release result; of `pGen` from the pin result | `(the result is refused) pBind: the runner reports no result for it`; the same for `pGen` |
| The addendum's second, on real data: a field absent (`pFork`, `runSyncAgree`) or null (`p42`, `scheduleAgree`; `pKv`, `exitAgree`) | `pFork: 4.0.1 sync: the ledger says "yes", observed "n/a"`, and the same form for the two others |
| The addendum's second, on real data: `pSqlite` said to have run; a result for `pSqlite` slipped in | Both refused: `the runner reports no result for it`; `the lane did not select it, and the runner reports it` |
| `python3 docs/research/2026-10-05-seat-M0/red-controls.py` as a whole | `red controls on real data: 14 of 14 as expected` |
| `python3 scripts/check-truth-release.py --self-test` | `self-test: 88 of 88 controls as expected`. It reads no install and runs no host |

### Other checks

| Command | Result |
| --- | --- |
| The 34 rows of the release result against the audit's `out/truth-401/result.v401.json` (`out/audit-comparison.txt`) | Equal in every field, frames and events included |
| The lane's import scanner against oxc-parser 0.147.0 on every source of the work copy (`out/specifiers-against-oxc.txt`) | 33 sources, 107 specifiers, no difference |
| `shasum -a 256` over the committed modules and tapes, as the lane note writes it | The two digests of the run record's pin entry |
| `python3 scripts/check-docs.py` | `PASS check-docs: every path, link, citation and make target in 73 documents resolves` |
| `python3 scripts/check-language.py --show` on the lane note and on this receipt | No finding |
| `python3 scripts/status.py` | It runs. It lists `truth-release` among the checks |
| The marker's keying, by real runs | A fresh marker runs nothing. A touched ledger, script or install folder runs the lane. An unset or changed variable runs it too |
| `find ~/.bun/install/cache -maxdepth 2 -newermt "2026-10-05 12:45:00"` | Empty: bun's cache gained nothing during the session |
| A package linked from a folder outside any install, importing `effect`, under `bun --no-install` | `Cannot find package 'effect'`. With `--preserve-symlinks` it loads. A stand-in package, not the driver |

## Axiom output

No Lean declaration changed. The Lean commands that ran are the narrow build and the Lean
phase of the pinned lane.

## Evidence

| Claim | Evidence word | Bound |
| --- | --- | --- |
| The pinned lane passes at the code head, and its committed artifacts are the base's bytes | reproduced | The pinned lane's own comparison with a fresh run, and `git diff` against the base |
| The pin, through the work copy, gives the committed `result.json`, `result.md`, 39 modules and 6 tapes | reproduced | Each lane run compares the bytes |
| On `effect@4.0.1`, 30 programs agree with the machine on all three fields, and 4 more ran | tested | One machine, bun 1.4.2, 34 programs; host only |
| `pProvideMerge`, `pProvideTwice` and `pMergeAll` agree on the exit and the sync exit. The release lacks one `forked`, `started`, `exited` triple of the machine's schedule | tested | The entry is the exact edit between the two schedules |
| The cause of that triple is the scope link | reading | The audit's F12. This seat ran no probe of the cause |
| `pInterruptEscape` agrees with the release on all three fields, and differs from the pin as the signed `U-01` pair | tested | One fixture |
| Five programs need the driver and have no observation on the release | tested | The lane did not run them. The 4.0.1 driver is not on this machine |
| The modules that the release ran are the committed modules, and its one tape is the committed tape | reproduced | Byte comparison in each lane run |
| tsgo 7.0.0-dev.20260629.1 finds no diagnostic in the release's work copy, and reads `effect` declarations from the release install only | tested | 64 sources. A typed stub stands for the driver. The five programs are outside it |
| The pinned lane's four host test files pass on both builds | tested | 23 tests |
| The lane needs no network, and nothing was downloaded | tested | A sandbox that denies the network, on macOS; bun's cache unchanged |
| The ledger's groups are the audit's four groups | tested | The comparison above |
| The lane refuses each fault of the controls | tested | 88 kept controls on a small manifest; four red controls on the committed files; 13 on the real results |
| The Windows branch of `link_install`, and bun as `bun.exe` under WSL | assumed | Written after `select`; not run |

No statement here is proved. Every host run is a finite probe on one machine.

### The build ledger against the audit's four groups

| Group | Programs | Pin | Release | Slice |
| --- | --- | --- | --- | --- |
| Both builds | 30 | `yes` on the three fields | `yes` on the three fields | none |
| The schedule on the release | `pProvideMerge`, `pProvideTwice`, `pMergeAll` | `yes` on the three fields | exit `yes`; schedule `no: the host lacks machine rows 13-15 (forked 0 5, started 5, exited 5 success)`, rows 19-21 and fiber 7 for `pMergeAll`; sync `yes` | `M2 scopes` |
| The release only | `pInterruptEscape` | exit `no: machine interrupt [{"interrupt":0}], host fail [{"fail":42}]`; schedule `no: machine row 4 (exited 0 interrupt) is host row 4 (exited 0 fail)`; sync `yes` | `yes` on the three fields | `M5 the failure walk` |
| Not run | `pSqlite`, `pSqlFail`, `pSqlCatch`, `pSqlExit`, `pSqlOrDie` | `yes` on the three fields | `not-run` on the three fields | `driver` |

The groups and their members are the audit's. One representation differs. The audit ran the
five driver programs against a stub and recorded their deaths as disagreements. There
`pSqlOrDie` even agrees on the schedule, because both sides exit with a defect. The ledger
records no observation for the five.

### What the run record holds

`harness/truth/build-ledger.run.json` holds the SHA-256 of the manifest. For each build it
holds:

- the `effect` version, and the driver or `null`;
- the bun version and the runner's deadline;
- the compiler and its version;
- the programs that ran and those not run;
- the count and the digest of the modules, and of the tapes;
- each rewritten import specifier.

The lane compares the record with each host run, as the pinned lane compares `result.json`.

## Landed theorems and their placement

None. No theorem lands and no obligation is stated. The lane is a finite check of two builds
on the three fields that the runner compares. It states no claim of its own.

## Open obligations

1. **After seat T3b's merge, two files must be written again.** They are
   `harness/truth/build-ledger.run.json` and `harness/truth/build-ledger.tsv`. The command is
   `make gen-truth-ledger`, with `EFFECT4_RELEASE_NODE_MODULES` set. Run `make gen-truth` and
   `make check-truth` first.
   - The run record always changes then. It holds the manifest's SHA-256 and the modules'
     digest, so the lane fails until the promote.
   - The ledger changes where an entry moves, where a schedule's rows shift, and where a
     program comes or goes. The three schedule entries name row numbers.
   - Write `reason` and `slice` for each new line that has an entry other than `yes`.
2. **The release install is not kept.** `<R>` is in the session's scratch folder. Assemble one
   with the recipe of the lane note before the next run.
3. **The pinned lane does not read the ledger.** `run-truth.ts` still refuses every unsigned
   disagreement with the pin. The first slice that turns a program toward the release meets
   that rule: `make gen-truth` and `make check-truth` then fail (reading of
   `harness/truth/run-truth.ts` and `scripts/check-truth.py`). Proposal B below.
4. **Five programs are not run.** They wait for the owner's word on the driver's download
   (the migration plan's F6). A linked driver does not load; the driver needs a real install.
5. **The cause of the three schedule differences is not tested.** It belongs to M2.
6. **The generated corpus did not run on the release.** `scripts/check-corpus.py` selects the
   pin only.
7. **Windows is not run.** No PowerShell wrapper exists for the release lane.
8. **The worktree holds leftovers that git ignores:** the two links to the pin's install,
   `.lake/truth-release/` and the markers under `.lake/check/`.

### What the seat did not verify

- `make check-truth-release` without the two `-o` flags. The coordinator's checkout has a full
  build and its own install, and the seat did not run there.
- `make check`, `make check-full`, `make check-corpus` and `make check-language`. The corpus
  lane's marker is now stale, because it names `scripts/lib/truth_host.py`. The functions that
  it calls did not change.
- The pinned marker's keying. `Effect4/Laws.trace` is absent after a narrow build, so here the
  pinned lane runs on every call.
- The lane with a release install that holds the driver.
- That the stub and the two rewritten imports are neutral. The control covers the copy only.

### What happened on the way

- **One scripted red control did not fail at first.** GNU Make 3.81 compares whole seconds. A
  ledger changed in the second of the marker's own touch ran nothing. The evidence script now
  moves the marker aside first. The seat read the output and repeated the controls.
- **The first two evidence runs put files back with `git checkout --`.** A guardrail later
  refused that form. The final evidence uses a kept copy. The files were clean before each
  change.
- **A safety check refused one `rm` of the old evidence files.** The seat did not repeat it,
  and the evidence script overwrites each file in place.
- **A `curl` probe ran inside the sandbox that denies the network,** as its red control. It
  ran twice by hand and once in each run of the evidence script. Each time it failed to
  resolve `registry.npmjs.org`, and nothing was fetched.

### Noticed in passing, outside the slice

- **The pinned lane does not compile `harness/truth/tuples.typecheck.ts`** (reading).
  `harness/truth/tsconfig.json` names it, and `scripts/check-truth.py` does not copy it into
  its work folder. The release lane compiles it on both builds with no diagnostic (tested).
- **No Makefile rule, script or workflow names** `harness/truth/maps.test.ts`,
  `harness/truth/tuples.test.ts` or `harness/truth/maps.typecheck.ts` (reading, by `git grep`).
- **`harness/truth/tuples.ts` is not a prerequisite of the pinned marker** (tested, from make's
  database).
- **Seat T3b's branch tip `e112352f` changes `harness/truth/prelude.ts` too,** not only
  `harness/truth/Truth.lean`. It changes no import line. No path is changed by both branches.

## Proposed decisions rows (proposals only)

| Proposal | Options | The seat's recommendation |
| --- | --- | --- |
| A. `check-truth-release` in the sweep | (a) as landed: in no sweep; (b) in `check-full` now, where the sweep fails unless the variable names an install; (c) in `check-full` and in the workflow once a tracked manifest installs the release | (a) now, (c) after the owner's word on the download. The lane runs with no network. On a machine it needs bun, node, Python, the pin's install, and `EFFECT4_RELEASE_NODE_MODULES` naming an install with `effect@4.0.1`, the pinned compiler and the bun types |
| B. The pinned lane's rule once a slice turns a program | (a) `run-truth.ts` takes its exit status from the ledger's pin entries, and the signed `U-01` pair becomes one ledger line; (b) `scripts/check-truth.py` accepts the runner's failure where the ledger's pin entries hold; (c) each slice signs its new difference in the runner, as `U-01` | (a), in the first slice that turns a program (M2 or M5). `truth_ledger.observe` and `truth_ledger.judge` take one build, so the pinned lane can call them |
| C. The release install | A tracked `package.json` and lockfile for the release lane, with `effect@4.0.1`, the driver, the pinned compiler and `@types/bun`, and a make rule like the pin's | Open it with the owner's word on the download. The five programs then run, and their ledger lines are promoted |
| D. The documents | `docs/GENERATED.md` names the ledger and the run record among the promoted files; `README.md` names the two targets | Add them. The seat did not edit either file: the brief does not name them |
| E. The pinned lane's three gaps above | Copy `tuples.typecheck.ts` into the pinned work folder; name or delete the three unnamed files; add `tuples.ts` to `TRUTH_SOURCES` | A small follow-up slice. It moves the pinned lane, so it is outside this one |
| F. The entry points in the Lean profile | `rc112` (`src/Effect4/Program/Profile.lean`) lists the prelude's imports in the pin's spelling. `RELEASE_ENTRY_POINTS` maps its two `effect` paths and the package module `unstable/sql` | Move the profile's list in M8, from this table |
