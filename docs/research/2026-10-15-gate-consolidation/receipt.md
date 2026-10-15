# Gate consolidation receipt

Status: the owner stops the PC work at gate consolidation. S3 and A1 remain for the Mac.

## The one thing to know

The full behaviour lane passes, and its final no-op run takes 17.15 seconds.
The fixture writers now import shared data. Their batteries retain the controls and proofs.
The source moves keep declaration names and program bodies.
The broad sweep still exposes an existing foreign-ingest gap and a stale slow-lane certificate, recorded below.
Read `a1-reuse-audit.md` before resuming A1 on the Mac.

Base: `d7f99c991603d0df7c5746e1ba3327d078cc163b`.
The proposal lands at `ab12f43cb`. The first cache and conformance slice lands at `d4e2d3a6b`.
The code slice lands at `370300fba78b2b53bd2730854ea4b681463b4223` on `gates/consolidation`.
`changed-files.txt` lists that slice's paths, measured by `git diff --name-only d4e2d3a6b 370300fba`.
The receipt and handoff follow in a separate commit. The owner receives both through `refactor/phase1-phase3`.
These two commits remain local for the requested push and Mac transfer.

## Before measurements

All times are seconds from `time.monotonic` around the named Make command.
`before.json` holds the measurements. `environment.json` holds the measured tool versions.
The Linux source remains at the base commit throughout this run.
Cold means absent check markers, with compiled libraries and installed dependencies present.
The separate clean library build takes 16 minutes, 32.17 seconds.
Warm repeats the command without a source edit.
The core edit appends one comment to `src/Effect4/Codegen/Names.lean`.
The last phase rewrites tracked files with identical bytes, retaining that comment.
This simulates checkout timestamp changes. It performs no branch checkout.
The script restores the original source in its `finally` clause.
The schema TypeScript step fails because its recipe omits a required module build.
Some baseline runs overlap the development build. The timings are single samples under that load.

| Step | Cold markers | Warm | Core comment edit | Same-byte rewrite |
| --- | --- | --- | --- | --- |
| `check` | 1.428 | 1.048 | 0.826 | 1.013 |
| `check-native` | 22.133 | 0.234 | 11.31 | 24.051 |
| `check-compiler` | 8.644 | 0.239 | 8.275 | 9.567 |
| `check-ocaml` | 117.604 | 1.099 | 98.651 | 100.304 |
| `check-schema-codec` | 3.38 | 0.501 | 3.113 | 3.005 |
| `check-schema-ts` | 1.247 (exit 2) | 1.161 (exit 2) | 1.441 (exit 2) | 1.199 (exit 2) |
| `check-truth` | 19.414 | 0.529 | 20.281 | 19.558 |
| `check-target` | 13.649 | 0.515 | 15.602 | 13.632 |
| `check-ts-reader` | 6.112 | 0.966 | 1.123 | 6.175 |
| `check-host-protocol` | 91.033 | 0.508 | 101.738 | 99.473 |
| `check-corpus` | 64.629 | 0.508 | 66.592 | 69.586 |
| `check-tsdiag` | 3.024 | 0.954 | 1.069 | 3.467 |
| `check-ingest-smoke` | 1.289 | 0.94 | 1.083 | 1.72 |

## After measurements

`after.json` holds the measurements. `measure-before.py` and `measure-after.py` hold their drivers.
The development checkout owns its Bun installation during this run.
The table keeps the original steps for comparison.
The OCaml row runs `.lake/check/ocaml`; the public `check-ocaml` also runs native and compiler.
The separate service-identity step now belongs to `check-ts`.

| Step | Cold markers | Warm | Core comment edit | Same-byte rewrite |
| --- | --- | --- | --- | --- |
| `check` | 3.224 | 1.633 | 1.373 | 1.408 |
| `check-native` | 17.948 | 1.093 | 1.052 | 1.084 |
| `check-compiler` | 11.049 | 1.443 | 10.617 | 1.451 |
| `check-ocaml` | 128.855 | 5.831 | 105.957 | 5.793 |
| `check-schema-codec` | 5.856 | 1.137 | 6.166 | 1.176 |
| `check-schema-ts` | 8.383 | 1.111 | 1.15 | 1.121 |
| `check-truth` | 24.121 | 1.218 | 23.205 | 1.234 |
| `check-target` | 17.157 | 1.177 | 1.198 | 1.155 |
| `check-ts-reader` | 8.753 | 2.106 | 2.126 | 2.082 |
| `check-host-protocol` | 98.252 | 1.239 | 100.223 | 1.236 |
| `check-corpus` | 68.207 | 1.224 | 68.119 | 1.219 |
| `check-tsdiag` | 5.864 | 2.044 | 2.105 | 2.06 |
| `check-ingest-smoke` | 4.358 | 2.043 | 2.064 | 2.078 |
| `check-service-identity` | 4.971 | 1.146 | 4.935 | 1.148 |

The first warm aggregate takes 18.245 seconds. It also primes the tsgo policy marker in 0.251 seconds.
The same-byte aggregate takes 18.138 seconds. It runs no comparison, generator or package install.
Each timing is one sample. The final verification follows the source cleanup and sweep.

The core edit still reruns the derived and LCNF producers where their import closures reach that source.
The keys include the Makefile, so a recipe edit invalidates every check conservatively.
This slice does not claim that every source edit becomes cheap.

## The implementation

Make owns commands and ordering. `scripts/lib/gate_cache.py` owns content keys and successful result records.
Keys contain workspace source closures, file bytes, package pins, tool versions and selected environment values.
They distinguish an absent environment variable from an empty value.
Source hashes let a shared pass skip compilation before testing.
A fresh Lake trace would require that compilation before looking up the pass.
Keys include each installed Lean package's Git commit and local file changes.
Runtime package versions identify the selected OCaml switch.
The store sits beside Git's common directory, so linked worktrees share successful checks.
A failed command publishes no pass. A changed input during the command also prevents publication.
Generators keep local outputs. Their content keys detect missing or changed outputs.
The Bun install follows this rule too. Linked installs are checked and kept.
Make's dry-run, touch and question modes publish no successful check.
A shared successful check never substitutes for an absent generated file.

The public lanes are `check`, `check-ts`, `check-ocaml`, `check-full`, `check-gen`, `check-sweep` and `check-kernel`.
The internal step aliases remain callable for diagnosis.
Root wiring appends imports for orphan modules. It excludes the slow lane and rejects core imports of law modules.
Document repair cites the last revision containing a deleted path. It leaves unknown paths unresolved.

## Fixture imports

Each scenario owns one `runSet`, shared by its battery and its writer.
`builtInputs` admits each scenario variant. The battery retains the controls over those builds.
`RunSet` stores names and existing `NamedRun` values. It introduces no program representation.
The source moves change no proof statement or proof body.

| Writer | Workspace sources | Law sources |
| --- | --- | --- |
| `mask` | 118 | 0 |
| pool | 150 | 0 |
| queue | 186 | 0 |
| semaphore | 149 | 0 |
| scenarios | 209 | 0 |

The import-reader controls require every engine writer to reach no law module or battery command.
The OCaml seam scan reads core sources only. Its key includes those sources.
The core root cannot import the law graph.
The scenario writer previously reaches 923 workspace sources, including 595 law sources.

## Cuts and retained controls

| Item | Decision | Evidence or consumer |
| --- | --- | --- |
| `scripts/check-generator-bootstrap.py` | remove | the derived producer owns bootstrap admission |
| `scripts/test-derived-plan.py` | remove | the producer and regeneration checks exercise the live plan |
| `scripts/test-conform-runner.py` | remove | outside oracle comparisons remain; the old suite passes before removal |
| `scripts/test-lean-imports.py` | keep and wire | import closures now identify check inputs and fixture boundaries |
| `Test/fixtures/schema-census/reference.ts` | remove | unused reference; the live host comparisons remain |
| `tools/conform-red/Probe2Neg.lean` | remove | its reflected declarations no longer exist |
| `tools/conform-red/RulesNeg.lean` | replace | `Test.Program.SelectRulesRed` checks the intended error and both service requirements |
| service identity | keep and wire into `check-ts` | two TS2375 controls and four runtime outcomes pass |
| program structure | keep and wire into `check-sweep` | selected-family and six refusal controls |
| session snapshot | keep | the live graph research consumer reads it |
| release packets | keep | the named-install release lane still reads them |
| hand OCaml carrier | keep | LC8 owns its replacement |

The sweep finds two stale controls outside these planned cuts.
The trust fixture still calls `restingDifference`, removed with the identity pin under decisions row 375.
Remove that obsolete block; retain the exact implementation admissions and semantic axiom-ceiling controls.
The Ty-rule scratch harness copies its script without the shared import reader that the script imports.
Copy `scripts/lib/lean_imports.py` into each scratch tree. All 18 controls then pass.

## Verification

The fixture comparison reproduces all 11 files byte for byte.
Command: `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only fixtures --output-dir .lake/fixture-verify`.
The narrow build passes for the 56 changed battery modules and the audit tool.
`landing-modules.json` lists the modules. `landing-audit.lean` records the exact audit command.
The landing audit walks those modules, `Effect4.Library.Stream.ArrayModel`, and `Effect4.Laws.Program.Typing.HasTy`.
Its output follows.

```text
#axiom_audit: 2820 declarations within [propext, Quot.sound], 8 of them modulo planned goals; 2 planned goals
```

The planned goals already exist. The source moves change no theorem statement or proof body.
Direct imports now name the laws and commands that the moved data no longer imports.
The select-rule controls serve residual-program-typing. They read `inv_select` and test two service requirements.
They establish no progress or host agreement.

The Python controls pass: 15 cache cases, 14 import-reader cases, four root cases, and one citation-repair case.
The cache integration uses two linked Git worktrees.
The document check passes across 113 authority documents.
The strict language check passes for `AGENTS.md` and `docs/core/controlled-english.md`.
Other documents retain 2057 reported findings after the generation notes are corrected.

## The remaining sweep work

The unmodified `check-ingest` fails with `missing eff coverage: defs, invoke`.
Its constructed foreign corpus does not generate these forms.
A local corpus probe adds them and then reaches `missing action coverage: raceAllFirst`.
That probe does not establish support for definition blocks or program arguments in each foreign reader.
The driver returns to its original bytes before the final checks.
`foreign-corpus-probe.patch` retains the experiment as evidence, not a proposed landing.

The remaining work must decide the supported fragment and repair the corpus and per-style count controls together.
This task does not weaken the coverage list or manufacture an ingest pass.
The continuation uses `make -o .lake/check/ingest check-sweep` to exercise the other sweep steps explicitly.
That command is a partial sweep. It does not establish a passing `check-sweep`.

The partial sweep reaches `Test.Slow` and fails in `Test/Program/LayerSharingCertificate.lean`.
Its `once_s220` and `twice_s301` states do not meet the pinned command, exit and finished-state claims.
The subsequent `twice_count` axiom-ceiling error follows these failed proof elaborations.
It is not evidence of a dependency on a registered planned goal.
The source closure of this certificate contains no file changed by this task from the base.
Command: `python3 scripts/lean-imports.py --closure Test/Program/LayerSharingCertificate.lean`, intersected with `git diff --name-only d7f99c991`.
The certificate needs a separate repair against the current machine.
This task changes neither the certificate nor its axiom ceiling.

## The Mac boundary

The owner requests this stopping point before A1 implementation.
S3 at `435f599d494f882d03db0ea403e71881698f74e2` remains unmerged here.
A1 at `fd33698271a39bb50c543b3723fdb0dfa9968a95` remains unbuilt here.
The audit reviews A1 source and proposes reuse; it introduces no A1 proof or implementation change.
The Mac should integrate S3 with its OCaml comparisons before continuing A1.

The audit prioritizes the generated reference fold and a single persisted JSON writer.
It retains distinct duplicate-key policies, the existing normalization laws, and the exact bridge's actual scope.
It also identifies a cycle diagnostic that can name a key outside the cycle.
The new `Todo.Data` module supplies A1's fixture data without importing its battery.

## Final verification

`final-validation.json` records the final behaviour and document runs.
The source checkout holds the refactor over the base commit in a WSL-linked worktree.
`validated-files.json` records the task's file hashes and confirms that the tested and committed source bytes match.

| Command | Seconds | Result |
| --- | --- | --- |
| `make --no-print-directory check-full` | 362.744 | pass |
| the immediate `check-full` repeat | 17.15 | pass; no comparison, generator, or install runs |
| `make --no-print-directory check-docs` | 1.727 | pass |
| `make --no-print-directory -o .lake/check/ingest check-sweep` | 323.095 | fails in the unchanged slow certificate |

The full lane uses native TypeScript `7.0.0-dev.20260629.1` and the Schema host's TypeScript `7.0.2`.
The Schema host uses `@effect/tsgo` `0.38.0` for its language-service checks.
`full-final.log` records the outside comparisons and their registered differences.
`warm-final.log` records the immediate repeat.
`ingest-failure.log` and `sweep-except-ingest.log` retain the sweep failures.
`sweep-result.json` records the partial sweep's exit status.

The whole-tree gate checks 1,810 modules and 139,410 declarations.
Its semantic and test ceiling remains `[propext, Quot.sound]`.
Its exact implementation boundary admits `Classical.choice` for 22 modules and 48 declarations.
It counts 23 planned goals and 26 declarations resting on them, with no other declaration reaching `sorryAx`.
The library-root gate reaches 278 API/utility modules and 850 Laws-only modules, with no core import of Laws.
The source moves introduce no planned goal.

`reuse-validation.json` and `second-worktree.json` record the remaining checks.

| Check | Seconds | Result |
| --- | --- | --- |
| `make check-ocaml` after a comment edit in `Effect4.Laws.Api.Runner` | 7.059 | pass; no comparison reruns |
| `make clean-check` | 0.204 | pass; shared results remain |
| `make check-full` after local marker removal | 28.87 | pass; shared results, no comparison, generator, or install runs |
| `make status` | 15.263 | pass; reports content-key state and remaining timestamp-based generation markers |
| `make check-native check-compiler check-schema-codec` in the second linked worktree | 6.271 | three shared passes; no new pass and no compiled project artifacts |

The second worktree starts without compiled project artifacts or copied check markers.
It has pinned package checkouts and links to the same installed host packages.
The test checks three outside comparisons. It does not claim that missing generated outputs can be skipped.
The shared store remains local to this WSL host; Mac identities select different keys.

The proof-comment probe restores the original file in its `finally` clause.
`finish-validation.py`, `verify-reuse.py`, and `verify-second-worktree.py` record the commands and assertions.
Their absolute paths identify this PC's validation trees.
`make status` runs after local marker removal, so unused sweep markers appear as never run locally.
The earlier sweep evidence remains in its logs and shared records.
