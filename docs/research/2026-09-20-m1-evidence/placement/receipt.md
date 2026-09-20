# Placement receipt — 2026-09-20

The placement is applied and its 68 planned module checks have passing evidence. The compiler lease is released. The coordinator still owns `make gen-architecture` and `make check`; this receipt does not claim either ran or passed. Building `Test.Audit.AxiomGate` compiled the audit implementation. The whole-tree `#effect4_axiom_gate` command runs from `Test/All.lean` and remains part of that final sweep.

The base and current commit are `8b64039f918b702b17281f7c438ef3fc6d7eea64`. Placement changes are uncommitted; this seat made no commit or push. No Phase B proof work was started.

## Changes and comparison

`moves.tsv` records all 47 old and new paths with hashes: 40 handwritten files and seven generated files. Store carriers and domain operations now have separate owners, including `Store.Domain.Clock`. Program codecs and wire support moved under the Store domain. Fold connectors moved into Laws, typed-state tools beside their Program owner, cross-target drivers into `tools/Drivers`, and generated authoring forms into Codegen. Declaration namespaces remain unchanged.

The six checker fold laws were extracted verbatim into `Laws.Program.Typing.FoldAgreement`. Two neutral fixture files under `tools/TestSupport` contain the exact shared CAS entry and host resource-row declarations. The original three fixture batteries retain their commands in the same order. `source-checks.json` records all 47 move comparisons and 99 import-only body comparisons. The comparison removes imports, comments, whitespace, and explicitly renamed physical provenance paths, then compares the remaining declaration, proof, and name tokens. The extracted theorem suffix and fixture blocks were also compared as exact text.

The generator manifest changed only import/output locations. The architecture direction rule did not change. The axiom gate changed only the three exact module IDs of the moved metaprogramming tools. Existing warning flags, `roots.json` dependency, and serial producer/build calls were retained. The Makefile typed-state check now invokes the same eight modules separately, in the same order.

At the recorded source-check time, `README.md`, `ocaml/gen`, `ocaml/engine/api_engine.ml`, `generated`, `Test/contracts`, and `Test/fixtures/baseline` had no tracked diff from the base. `git diff --check` exited 0. `source-sha256.tsv` captures the placement source snapshot; subsequent coordinator validation may regenerate deterministic outputs.

## Commands and results

The source preparation ran `python3 /tmp/m1-tools/prepare-placement.py --refresh-plan`, then `--check`, then `--apply`. The selected producer pass used `--regenerate-derived`; the Driver emitted commands and exited before each producer started. Every Lean process ran serially with `LEAN_NUM_THREADS=1`. Direct Lean invocations used `-DwarningAsError=true`; Lake builds inherited that flag from the project configuration.

Eleven existing producer groups ran once each for placement: Json, Schema, Program, Pin, Api, Value, Runner, TyView, ValFold, Forms, and FormsLaws. All eleven generated declaration/proof comparisons and output-module builds passed. Seven Main/default Canonical outputs passed separate `Effect4Gen/Check.lean` invocations at the unchanged heartbeat limit. The four View/Fold/Forms outputs use their actual producer comparisons, narrow builds, and embedded checks; the Canonical shape checker is not applicable to them. Seven retired generated paths were removed only after these checks. `producer-commands.json` preserves the exact executed argument lists, and `derived-checks.json` records applicability. This seat invoked no LCNF, CAS, EFF, or architecture producer during placement.

`module-results.json` and `module-results.tsv` contain the 65 affected checks plus the `Effect4`, `Effect4.Laws`, and `Test.Audit.AxiomGate` checks. There were 60 final direct-invocation results, seven checks reused from a freshly completed dependency build, and one Forms tool check supplied by its two freshly completed producer elaborations. Reuse required an actual successful `Built` diagnostic, not a replay, stale cache, or timestamp. The Truth harness passed a direct Lean invocation because it is not a Lake target. The final root logs are `placement-build-logs/065-Effect4.log`, `066-Effect4.Laws.log`, and `067-Test.Audit.AxiomGate.log` inside the archive.

## Retained failures and scope

`failed-attempts.json` records five failed invocations and their resolutions. The aggregate Canonical checker reached the unchanged 200000-heartbeat limit; separate applicable file checks passed without another producer run. Applying that checker to TyView refused because it has no Canonical shape declaration. Lake rejected Forms and the Truth harness as unknown targets; their correct entry points supplied the checks described above. The first Laws-root build rejected imports placed after the module description; moving those imports into the leading block fixed the root without changing declarations.

The initial serial coordinator was stopped after its current compiler completed so later checks could reuse fresh dependency evidence. Its process exit 143 is retained as orchestration history, not a failed Lean proof. No compiler process was interrupted or run concurrently.

`logs-and-scripts.tar.gz` preserves 167 diagnostic, generated comparison, script, and state files losslessly. Its contents were read back and compared against every source file. `archive-manifest.tsv` gives each member's size and SHA-256. The preparation script snapshot includes the corrected import-block placement and per-file checker applicability; it is an audit record, not a command to reapply to the already moved tree.

No theorem statement or proof body was intentionally changed in this slice, no new proof obligation was filled, and no claim of runtime equivalence follows from these placement checks. The full trust and architecture results belong to the coordinator's subsequent sweep.
