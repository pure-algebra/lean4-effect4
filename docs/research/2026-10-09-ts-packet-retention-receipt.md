# Shared target packet retention receipt

Integrate only the unique repair commit and this receipt.
The integration branch already contains the shared dependency commits.
The repair retains early helper failures without claiming that missing compiler inputs exist.

## Commits and files

Repair base: `d45ee275540b96958518b9ac6b9b9ef5a320ff11`.
Repair head: `d50961eb2f9dec8db9e3f3266ec3aff7d177caa8`.
Branch: `codex/ts-packet-retention`.
This receipt follows the repair head in a documentation commit.

The local dependency `209cd67c` copies integration commit `b4d8439b`.
The local dependency `d45ee275` copies integration commit `846ed8c0`.
Do not apply those copies to the integration branch.
The earlier tuple blocker branch remains available.

| Unique path | Change |
| --- | --- |
| `harness/ts_packet.py` | Protect preparation and retain available failure inputs |
| `harness/test_ts_packet.py` | Five focused controls with the real runtime and pinned compiler |
| `docs/research/2026-10-09-ts-packet-retention-plan.md` | Contract and completion criteria |
| `docs/research/2026-10-09-ts-packet-retention-receipt.md` | This receipt |

No generated helper, emitted caller, TypeScript setting, Lean declaration, root, or semantics registry changes in the unique repair.

## Defect and repair

The shared packet loads helper exports through Bun before entering its original exception handler.
A helper initialization failure therefore loses its temporary inputs and records no failure file.
A copied helper that throws an explicit sentinel error reproduces that behavior before the repair.
Both `failure.txt` and `compiled-inputs` are absent in that original finite probe.

The repair starts the protected region before dependency setup and helper copying.
The input inventory exists before preparation begins.
On failure, the handler records the original error and copies every available named input exactly.
It skips only names whose input file does not yet exist.
It manufactures no caller header, observer, configuration, or manifest.
The caller's raw emitted file and manifest remain in its output directory.
A failed context never yields a compiled packet or writes a successful receipt.

Success retains the original strict inventory behavior.
A missing required input still raises during successful retention.
The existing package-version and occupied-output checks remain unchanged.

## Commands and measured results

```sh
EFFECT4_TS_INSTALL=/Users/pooks/Dev/lean4-effect4/ts/release/node_modules python3 harness/test_ts_packet.py
```

The final run passes five tests in 0.557 seconds.
The tests use Bun and the actual pinned tsgo executable, without mocks of runtime or compiler behavior.
The compiler version check requires `7.0.0-dev.20260629.1`.
The package checks require Effect `4.0.1` and that same compiler version.

| Control | Result |
| --- | --- |
| Helper initialization throws during export discovery | Exact five available input files and original failure text remain |
| Strict compiler rejects a number assigned to string | Exact nine prepared input files and TS2322 remain |
| Strict compiler accepts a valid Effect caller | Every required input retains identical bytes; a missing required name still raises |
| A helper file is absent during copying | Exact three existing inputs remain; later inputs remain absent |
| Output is occupied or either package version differs | Existing refusals remain; wrong versions create no evidence directory |

The compiler-failure control captures prepared bytes before temporary-directory cleanup.
It compares every retained file against those bytes.
The early-failure control compares every retained helper and generated re-export against the actual prepared source.
Both failure controls require the absence of a successful receipt.
These are finite Python, runtime, and compiler controls.
They establish no general target simulation or Lean theorem.

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-09-ts-packet-retention-plan.md docs/research/2026-10-09-ts-packet-retention-receipt.md
git diff --check
```

The strict language and whitespace checks pass before the receipt commit.
No Lake build runs for this Python-only repair.
No new Lean declaration needs an axiom gate result, and no axiom evidence is claimed.
No sweep or push runs.

## Final read-only catalogue review

The review reads the coordinator's integration tree and runs no Lake process there.
Its working diff includes root imports, exposures, claim placement, and generated semantics.
The review checks shared proof consumers, independent models, caller inventories, source bytes, and retained observations.

The PubSub and Stream claim pointers match their actual declarations and simulation roles.
Their titles retain the formal reading and allocated-cell premises.
SynchronizedRef's proposed expansion explicitly leaves wrapper acquisition, cancellation, cleanup, and composed agreement open.
Its existing laws prove typing and consume Ref and Semaphore laws.
The independent models do not read stored Step syntax.
No additional production defect or new outside-runtime overclaim is found in this bounded review.

The catalogue runner requires its exact ordered twelve-case inventory.
It requires nine exact reconstructions and three named frozen refusals.
The compiler discovers each required caller, and the four shared helper files occur in the retained input inventory.
The deliberately sticky control returns the same batch twice.
The positive repeated-pull caller separately requires clean ends and an empty pending cell.
Machine expected results and installed-runtime observations remain separate comparisons.
Only selected Stream collection and SynchronizedRef reply/final-value observations compare against installed Effect 4.0.1.
PubSub's pure readings are not represented as a public runtime-wrapper comparison.

The retained PubSub vendor hash, extracted source bytes, extract hash, and probe hash match their files.
The extraction matches the exact vendored interval.
The model hashes explicitly describe the historical work-in-progress review, rather than the final integrated tree.
Three unchanged core files still match those historical hashes; the later Model header has a different hash.
The source challenge retains its finite interpretation and exact numeric-admission limit.
It claims no Lean transcription theorem or current unbounded host relation.

The coordinator subsequently retains the combined load report in `docs/research/2026-10-09-module-catalogue-audit.log`.
That report supplies all three law prefixes required by the catalogue brief.
This review reads the measured output; it does not rerun the report.

| Law prefix | Reuse ratio | Load-bearing count |
| --- | --- | --- |
| `Effect4.Laws.Library.Stream.Array` | 66% | 2 of 3 |
| `Effect4.Laws.Library.SynchronizedRef` | 72% | 0 of 10 |
| `Effect4.Laws.Library.PubSub` | 70% | 17 of 23 |

These values belong to the loaded integration environment and its semantics registry roots.
They measure direct theorem citations, rather than all clients or whole-module agreement.
The combined audit reports 906 compiled declarations across nineteen selected modules, with only `propext` and `Quot.sound`.
Its root reachability, independent-model imports, and core/law separation checks pass.
The original missing load reports are therefore closed by the coordinator's retained combined report.

The tuple target annotation and frozen reader exclusions retain their separate existing evidence.
This retention repair changes neither boundary.
