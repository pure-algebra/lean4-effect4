# Generated files

This map names the generated artifacts, their producers and the checks that currently
cover them. It owns this inventory and the generation rule; `docs/ARCHITECTURE.md`
owns the surrounding module boundaries. It is the Phase 0 step 0.2 inventory,
expanded from the five-scout plan (untracked working notes under `docs/research/`).
Step 0.4 adds provenance stamps. The LCNF outputs remain unstamped until the
approved Phase 1 regeneration. The legacy Schema assurance report also remains
explicitly unstamped under the owner amendment.

## The rule

An artifact with no row in this map may not be committed. Every generated artifact
has one producer command and one designated gate. The associated row names its producer and gate; its generated header or data
sidecar records what it was cut from. A row with no gate records an owner and a date below; these
are explicit migration debts, not passing checks.

The three tiers are:

- **build artifact**: produced by the build system or build setup and never committed;
- **committed projection**: generated output kept in Git, to be stamped and checked
  byte for byte; the gaps in that requirement are recorded below;
- **vendored input**: copied from an identified source, with provenance recorded.

Source outputs carry a comment line; data and vendored inputs carry the same
line in an adjacent `.cut-from` file, under the owner’s 2026-09-08 format amendment:

```
cut-from: rev=<git describe --always --dirty> toolchain=<lean version> inputs=<sha256>
```

`tools/Tools/GeneratedStamp.lean` computes `inputs` from sorted import names and
Lake `depHash` values across the import closure, current source hashes for that
closure, the producer source, and explicit run-time inputs. Local diagnostic paths
and logs are excluded. Sources are resolved in the current workspace/package rather than at an absolute path
left by a different checkout. Producers also compare Lake's recorded source hash against
the resolved source before emitting a stamp; source edits require a rebuild. The revision is informational and is never compared.
The stale check compares the input digest without regeneration. The drift check
regenerates into temporary files and compares every output byte except the
informational revision field. Data bytes are compared in full. Neither a compiler
check nor a host test establishes that a committed output matches today's Lean source.

`bash scripts/generate.sh` — with no argument or with `--all`, which name the same thing —
runs the one named order (DI-33): **derived, specs, eff, wire, cas, ts, readme**. Each family's
inputs are an earlier family's outputs, and `readme` is last because
`bun ts/eff/ingest/render-readme.ts` reads three `.gen.ts` files that `ts` has just written;
it is a host producer, so it writes `ts/eff/ingest/README.md` in place and its `--check` is
its drift form. `--only derived|specs|eff|wire|cas|ts|readme` selects one family; `--only lcnf` is
the explicit Phase 1 engine regeneration route and is not in the order. The entry point
holds the Lean lane and gives each Lean invocation a 600-second timeout. It runs
the producers every time. If only the informational revision differs, it retains
the existing output bytes.

**Truth is a host-lane family and is not in that order.** Its two commands are in its row
below and must be run in sequence by hand or through `bash scripts/check-truth.sh`, because
the Lean half reads the committed tapes that the bun half re-records: the two producers are a
fixed point, not a pipeline stage. Putting it in `--all` would let one run regenerate a tape
and a corpus that had never been compared with each other.

## Stream example outputs

The stream example lane produces two ignored build artifacts under `harness/streams/`,
rather than committed projections. `census.json` is produced by
`bash scripts/generate-effect-stream-census.sh` from the executable doc fences in the
pinned Stream, Channel, Pull, Queue, Scope, Sink, PubSub and Fiber modules. It records
source spans, SHA-256 digests, programs and expectations. `result.json`
is produced by `bun harness/streams/run.ts`; its per-row input digest includes the
vendored source tree, runner, compiler/declarations, runtime and deadline. The designated
gate for both is `bash scripts/check-streams.sh`. Its evidence is bounded host output
agreement, separately reported type checking and execution without an output oracle;
no Lean stream relation is claimed. Neither file is a committed projection or a
replacement for the runtime coverage report.

## Schema codec comparisons

The S-3 codec gate `bash scripts/check-schema-codec.sh` produces a temporary
TypeScript data module from the public `Ty.encode` results for
`Test/Codegen/SchemaGenerationContract.lean`'s representative cases. Its producer
is `harness/truth/schema-codec/Emit.lean`. The paired `check.ts` compares these
fresh outputs with pinned rc.112 `Schema.toCodecJson`, decodes and re-encodes them
on the host, and checks the rejected legacy Result/Cause shapes. The temporary
module is a build artifact, removed after each run; no codec golden is copied
into a committed generated file. This is finite host evidence, separate from
the universal checked-boundary laws in `Laws/Schema/Codec`.

## Host protocol projections

### Keyed session protocol

`harness/truth/session/protocol.gen.ts` and `harness/truth/session/tape.schema.json`
are deterministic committed projections of `src/Effect4/Api/HostProtocol.lean`, produced
by `bash scripts/generate-host-protocol.sh` through `tools/Tools/HostProtocol.lean`.
The TypeScript adapter and Lean JSON driver both use the datum's record fields and
transition table. The schema describes record structure; `Envelope` remains responsible
for the actual machine's row/request/completion judgment. This schema is a tape schema,
not a published content-address encoding (DI-01/04).

`bash scripts/check-host-protocol.sh` freshly regenerates and compares both files,
compares provenance except its informational revision, emits admitted Eff fixtures and binding plans, runs the printed expressions on rc.112,
typechecks those same generated expressions, and replays the actual recorded tapes in
Lean. Its finite controls include missing/stale/duplicate keys, wrong row/request/value,
receipt reordering, explicit application reordering, zero application fuel, and empty
public chunks. Inputs are the protocol/session/typing library, fixture and projection
drivers, host binding and comparator, pinned toolchain and Effect installation. No success
stamp skips this gate. Its latest working receipt is kept under the ignored `.work/`
folder beneath `harness/truth/session/`; it is not a committed projection or an oracle.

The v1 serial adapter in `harness/truth/session/Session.lean` is explicit and separately
version checked. V2 never fills in missing keys from a replay's expected request.

## Conform outputs

`src/Effect4/Laws/Program/Typing/Specs.lean` is the committed ordinary specification
projection. Its configuration (`tools/Conform/Effect4/specs.json`) and checker declarations
are inputs, not generated output. Source descriptions and conformance reports are build
artifacts under `.lake/conform/`; `scripts/check-conform.sh` produces them freshly and retains
source/compiled-input hashes, process status and the exact generated files. The compiler
profile's OCaml is an inspected execution artifact, not a replacement for `ocaml/gen`.

## Commands and current coverage

The family names in the file table refer to all four columns in this table: producer
command, inputs, consumers and designated gate. Commands run from the repository root
unless a working directory is stated. Hold `.lake/LANE.lock` for any Lean process,
use `LEAN_NUM_THREADS=3`, and use `-M4096` for Lean drivers. Run one Lean process at a time.
A command listed here is a reproduction instruction, not a claim that it was run for
this inventory. `cut-from` is the header stamp; a cached gate verdict is separate.

The **evidence** column is the word, or words, a family's claim carries, ruled 2026-09-09
(DI-32): *proved* for a theorem, *reproduced* for a byte comparison against a fresh producer
run, *tested* for a finite checker or host run over named inputs, *stamped* for a verifying
trace — the inputs were the ones the producer saw, and nothing about the committed bytes. The
words **co-occur**, and a finite checker run is *tested*, never *reproduced*. A family whose
only word is *stamped* carries no claim that its committed bytes match a fresh run.

| Family | Producer command | Inputs | Consumers | Designated gate and present limit | Evidence (DI-32) |
| --- | --- | --- | --- | --- | --- |
| Typing specs | `bash scripts/generate.sh --only specs` | `Conform.Cli.EmitSpecs`, configured checker imports, `tools/Conform/Effect4/specs.json` | `Effect4.Laws.Program.Typing.Inversion` | `bash scripts/check-generated.sh`; fresh bytes plus ordinary Laws elaboration | reproduced; kernel checked |
| Derived Json | `lake env lean -M4096 --run tools/Effect4Gen/Driver.lean --group Json` | `tools/Effect4Gen/manifest.json`, `tools/Effect4Gen/guards/json.lean`, `Effect4.Store.Canonical` | `Effect4.Store.Derived.Schema`, Effect4 library | `bash scripts/check-generated.sh`; fresh byte comparison, plus `lake build Test` for shapes | reproduced; tested |
| Derived Schema | same driver, `--group Schema` | manifest, `tools/Effect4Gen/guards/schema.lean`, `Effect4.Store.Derived.Json` | Effect4 library | `bash scripts/check-generated.sh`; fresh byte comparison, plus `lake build Test` for shapes | reproduced; tested |
| Derived Program | same driver, `--group Program` | manifest, `tools/Effect4Gen/guards/program.lean`, `Effect4.Program.Native`, `Effect4.Store.Canonical` | `Effect4.Api`, program wire | `bash scripts/check-generated.sh`; fresh byte comparison, plus `lake build Test` for shapes | reproduced; tested |
| Derived Pin | same driver, `--group Pin` | manifest, `tools/Effect4Gen/guards/pin.lean`, `Effect4.Store.Pin`, `Effect4.Store.Node` | store | `bash scripts/check-generated.sh`; fresh byte comparison, plus `lake build Test` for shapes | reproduced; tested |
| Eff | `lake env lean -M4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff` | `src/OCaml5/Eff/World.lean`, `src/OCaml5/Eff/Emit.lean`, imported Lean declarations | `effect4_eff`, `effect4_engine` | `bash scripts/check-generated.sh`; fresh byte comparison, plus `bash scripts/check-ocaml.sh dune-tests` | reproduced; tested |
| Engine structure | `python3 scripts/generate-engine-structure.py` (also run after Eff generation) | `ocaml/eff/program-structure.json`, actual `ocaml/engine/api_engine.ml`, parser/producer | `E4_program`, engine structural checks | fresh generated bytes and parser refusal controls; historical engine shortages remain explicit | migration in progress; no engine execution cutover |
| Eff goldens | same EffGen command | `src/OCaml5/Eff/Goldens.lean` | `ocaml/eff/test/dune` | `bash scripts/check-generated.sh` for fresh bytes; `bash scripts/check-ocaml.sh dune-tests` for behavior | reproduced; tested |
| Wire goldens | `lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff` | `Effect4.Program.Wire.Corpus`, `src/OCaml5/Tools/EffWire.lean` | `ocaml/eff/test/test_lean_wire.ml` | `bash scripts/check-generated.sh`; fresh byte comparison and missing-file refusal | reproduced |
| CAS goldens | `lake env lean -M4096 --run src/OCaml5/Tools/CasGoldens.lean ocaml/engine/cas/goldens` | Store Word and Genesis, Machine Stores, `Test.Store.NodeContract` | `ocaml/engine/cas/test/dune` | `bash scripts/check-generated.sh` for fresh bytes; `bash scripts/check-ocaml.sh engine-tests`, red as declared in the OCaml sweep | fresh-byte producer and comparison wired; execution remains separately declared |
| LCNF | exact command in each output's first comment, run with `lake env` before `lean` | `src/OCaml5/Tools/LcnfGen.lean`, `src/OCaml5/Lcnf/`, named import and roots; engine also reads `ocaml/engine/externs.txt` and `ocaml/engine/tools/api_engine_prelude.ml` | `effect4_gen`, `effect4_engine` | `bash scripts/check-generated.sh --stale`, red as declared until Phase 1; `bash scripts/check-ocaml.sh gen-check` in sweep for the seam; neither regenerates LCNF | stamped (the acceptance test of a regeneration is DI-19's conformance suite) |
| TypeScript | `bash scripts/generate-ts-eff.sh` | `OCaml5.Eff.World`, native rows, ingestion taxonomy, forms, profile, `lakefile.toml`, `src/Effect4/Codegen/Print.lean` | TypeScript readers, checkers and tests | `bash scripts/check-ts-eff.sh`; byte comparison, in sweep | reproduced; tested (the corpus check against Lean's own oracles) |
| Truth | corpus: `lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes`; other outputs and the tapes: `bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes` | Eff corpus, `harness/truth/prelude.ts`, the committed tapes (the package rows' recorded answers, read by Lean and re-recorded by rc.112 on every run), pinned rc.112 and `@effect/sql-sqlite-bun`, `ts/eff/package.json` and `bun.lock` | truth differential, TypeScript corpus check | `bash scripts/check-truth.sh`; fresh generation and comparison plus bounded host observations, and `tsc --noEmit -p harness/truth/tsconfig.json` over the regenerated modules and prelude before any byte is compared (DI-49; recorder inclusion follows in S6b); `python3 scripts/test-truth-stamp.py` for the stamp's inputs. Not a `scripts/generate.sh` family | reproduced (the tapes and corpus); tested (the named bounded host corpus; recorded package-row fixtures are single-fiber — DI-23) |
| Schema TypeScript | `lake env lean -M4096 harness/schema-generation/EmitFixture.lean` for Person, `EmitCoverageFixture.lean` for AllRepresentations, `EmitMultiFixture.lean` for TwoRoots; redirect stdout to named output | `Effect4.Codegen.Schema`, fixture declarations | three runtime checks in `harness/schema-generation/` | `bash scripts/check-schema-typescript-generation.sh`, host lane in sweep | reproduced; tested (three host runtime checks) |
| Runtime census | `python3 scripts/generate-data-stamps.py census` (runs the census producer and stamps identical data) | pinned rc.112 sources listed by output | `docs/RUNTIME-COVERAGE.md`, `Test/Audit/RuntimeCoverage.lean` | `bash scripts/check-effect-runtime-census.sh`, in sweep | reproduced (the census data); proved (only where a row's witness theorem is joined in `Test/Audit/RuntimeCoverage.lean`) |
| Schema assurance | `python3 scripts/generate-data-stamps.py assurance` (runs the assurance producer and stamps identical data) | schema sources, frozen batteries, pinned host sources listed by generator | schema assurance report | `bash scripts/check-schema-structural-assurance.sh`, manual by owner decision; owner: Schema assurance lane, 2026-09-08 | stamped (and the stamp itself is deferred: the frozen fingerprint is refused) |

The truth manifest and TypeScript profile use `tools/Tools/ProfileJson.lean` for the JSON
view of the existing `Ty`/`Row` data. Truth metadata additionally records every requirement
key, the actual scope key, and the three Host fixture rows, so target checking does not infer
requirements from an empty/nonempty flag or transcribe row types. This is a shared tool
projection, not a new canonical type representation. Changes in JSON object-field ordering
are producer changes; they do not change program wire ordinals or historical stored bytes.

The two files `ocaml/eff/goldens/val_ref.hex` and
`ocaml/eff/goldens/val_handle.hex` are hand-derived test fixtures, as recorded in
`ocaml/eff/test/dune`. They were incorrectly attributed to EffGen in the first
inventory; EffGen does not write them. They remain independent fixtures and are
excluded from this generated-artifact inventory. The first inventory had 335 rows.

The avatar's four frozen blocks, its three derived descriptions and the daemon's
archived inputs left this inventory on 2026-09-08 with the avatar and the daemon,
archived on `archive/ocaml5-avatar` at `14e6835`.

The owner also deferred the stamp on `generated/schema-structural-assurance.tsv`
on 2026-09-08: its manual producer refuses the frozen fingerprint for
`src/Effect4/Schema/Document.lean`. The Schema assurance lane owns that debt.
The report, frozen fingerprint and manual check remain unchanged.

`bash scripts/check-generated.sh --stale` checks all active provenance without
running Lean. `bash scripts/check-generated.sh` freshly produces the derived, Eff,
wire, CAS and TypeScript families. It requires a bijection between the generated-map
selection and every freshly produced non-sidecar file before comparing full non-stamp
bytes. The count comes from that inventory, including program and metadata fixtures.
LCNF retains its separately declared provenance policy. A provenance match alone is
not a claim that contents match a fresh generator run.

The LCNF declaration covers only the four unstamped files with their original
Phase 0 base bytes. A missing or changed stamp on any other active artifact
refuses before known-red policy is considered. A changed unstamped engine also
refuses. The accepted policy verdict is cached against scripts, manifest,
toolchain, Lake traces, source inputs and generated bytes. Removing the last
LCNF failure while its declaration remains is an unexpected pass and refuses.
`python3 scripts/test-generated-gate.py` tests those refusals in temporary fixtures.

## Engine boundary

Step 0.1 repairs compilation. `E4_program.pin` still refuses every load because the
wire's `native_op` alphabet includes the timer operations that the engine lacks.
The converter refuses those operations with `Ordinal_mismatch`; it does not silently
map them. Phase 1 must regenerate the engines before this refusal can be cleared.
`bash scripts/check-ocaml.sh engine-tests` now runs the engine tests in the OCaml
sweep and reports that failure as declared. The `dune-tests` row must still pass.

Keep `ocaml/gen/api_gen.ml` while `ocaml/engine/tools/api_engine_prelude.ml` contains
hand-written bodies. Gen-versus-Ref is the check on those carrier and extern choices;
it is not a check of correspondence to current Lean. Deleting an engine and abstracting
the Lean carriers are the same separate design change and are outside Phase 0.

The map retains all four LCNF outputs, including the older fibers and machine probes.
The approved regeneration scope names the API oracle and engine; this inventory does
not authorize silently replacing the older files.

## File inventory

One row per artifact. A family reference supplies the corresponding producer, inputs,
consumer and gate from the table above. For vendored input, the provenance record
replaces a claim of local generation. Ordinary compiler objects and binaries are not
source projections. Frozen historical test receipts outside the scout inventory retain
their own recorded provenance; they are not regenerated by this Phase 0 lane.

| File or build target | Tier | Producer command | Inputs | Consumers | Gate | cut-from stamp | Committed |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `src/Effect4/Laws/Program/Typing/Specs.lean` | committed projection | Typing specs | configured checker equations and full telescopes | typing inversions | generated | yes | yes |
| `src/Effect4/Store/Derived/Json.lean` | committed projection | Derived Json | Derived Json | Derived Json | Derived Json | yes | yes |
| `src/Effect4/Store/Derived/Schema.lean` | committed projection | Derived Schema | Derived Schema | Derived Schema | Derived Schema | yes | yes |
| `src/Effect4/Program/Derived.lean` | committed projection | Derived Program | Derived Program | Derived Program | Derived Program | yes | yes |
| `src/Effect4/Store/PinDerived.lean` | committed projection | Derived Pin | Derived Pin | Derived Pin | Derived Pin | yes | yes |
| `ocaml/eff/eff_types.ml` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/eff/eff_wire.ml` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/eff/eff_json.ml` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/eff/eff_native.ml` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/eff/eff_manifest.txt` | committed projection | Eff | Eff | Eff | Eff | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/corpus.txt` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/coverage.txt` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/p42.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/p42.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/p42.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAcquire.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAcquire.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAcquire.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pActions.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pActions.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pActions.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAwait.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAwait.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pAwait.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBind.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBind.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBind.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBranch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBranch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pBranch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCallback.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCallback.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCallback.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pDiamond.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pDiamond.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pDiamond.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExit.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExit.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExit.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFailCause.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFailCause.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFailCause.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFork.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFork.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFork.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pGen.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pGen.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pGen.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIll.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIll.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIll.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBranch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBranch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBranch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBreak.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBreak.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllBreak.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCallback.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllExternalDomain.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCallback.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllExternalDomain.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCallback.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllExternalDomain.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllInterruptor.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllInterruptor.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllInterruptor.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllJoin.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllJoin.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllJoin.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllReq.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllReq.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllReq.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllRet.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllRet.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllRet.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllStep.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllStep.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllStep.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllVar.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllVar.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllVar.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pJoin.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pJoin.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pJoin.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMasks.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMasks.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMasks.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMatch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMatch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMatch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMergeAll.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMergeAll.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pMergeAll.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOnExit.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOnExit.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOnExit.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOps.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOps.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pOps.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pPair.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pPair.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pPair.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pProvide.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pProvide.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pProvide.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pScoped.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pScoped.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pScoped.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSleep.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSleep.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSleep.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStmts.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStmts.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStmts.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStr.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStr.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pStr.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSuspend.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSuspend.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSuspend.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSync.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSync.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pSync.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pTwo.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pTwo.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pTwo.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pWhile.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pWhile.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pWhile.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pYieldError.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pYieldError.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pYieldError.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/manifest.txt` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/p42.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pAwait.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pBind.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pCatch.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pFork.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pGen.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pLoop.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/goldens/eff/pScope.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/cases.txt` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-01.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-02.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-03.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-04.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-05.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-06.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-07.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-08.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-09.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-10.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-11.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-12.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-13.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-14.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-15.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-16.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-17.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-18.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-19.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/digest-20.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-anyref-frame.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-canonical-digest-frame.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-censusEntry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-censusSchema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-genesisNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-annotation.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-chunk.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-component.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-entry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-export.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-fiber.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-manifest.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-program.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-query.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-result.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-schema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-source.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-tree.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-type.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-kind-vector.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-probeEntry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-probeSchema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-sampleEntry-payload.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g1-sampleNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-badVersion.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-conflict.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-dangling-spec.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-dangling-zero.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-entry-duplicate.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-entry-fresh.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-genesis-exempt.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-handle-in-content.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-length.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-occupant.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-ref-fresh.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-schema-duplicate.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g2-wrongKind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-advance-v2.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-dangling.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v1.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v2.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-stale.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-v1.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g3-wrongKind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-after-delete-get.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-after-delete.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-after-insert-get.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-after-insert.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-after-update.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entries-base.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entries-deleted.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entries-inserted.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entries-updated.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-nested-key.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-parent-miss.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-root.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-miss.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g4-get-parent.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-bytes-inside-list.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-bytes-is-a-leaf.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-ctor-seed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-handle-is-a-leaf.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-malformed-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-malformed-length.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-malformed-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-no-refs.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g5-order.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-closure-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-closure-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-closure-empty.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-nodes-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-nodes-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-replayed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-reversed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-probeWord.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-replay-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-replay-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g6-treeNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-dangling-edge.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-flipped-payload.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-good.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-replayed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-root-ok.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-root-wrong-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/g7-wrong-key.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/manifest.txt` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/val_handle.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/cas/goldens/val_ref.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | adjacent `.cut-from` | yes |
| `ocaml/gen/api_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | deferred: Phase 1 | yes |
| `ocaml/gen/fibers_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | deferred: Phase 1 | yes |
| `ocaml/gen/machine_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | deferred: Phase 1 | yes |
| `ocaml/engine/api_engine.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | deferred: Phase 1 | yes |
| `ts/eff/eff.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/forms.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/json.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/packages.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/profile.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/taxonomy.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `ts/eff/wire.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | yes | yes |
| `harness/truth/generated/p42.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pAcquire.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pAcquireClosed.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pAwait.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pBind.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pCatch.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pDiamond.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pFork.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pGen.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pLoop.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pMergeAll.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pAcquireHandle.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pFailTagged.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pSqlite.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pSqlFail.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pSqlCatch.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pSqlExit.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pSqlOrDie.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pKv.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlite.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/tapes/pSqlFail.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/tapes/pSqlCatch.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/tapes/pSqlExit.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/tapes/pSqlOrDie.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/tapes/pKv.jsonl` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/generated/pProvide.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pProvideMerge.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pProvideTwice.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pScope.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pTwo.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/corpus.json` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/result.json` | committed projection | Truth | Truth | Truth | Truth | adjacent `.cut-from` | yes |
| `harness/truth/result.md` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/schema-generation/AllRepresentations.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | yes | yes |
| `harness/schema-generation/Person.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | yes | yes |
| `harness/schema-generation/TwoRoots.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | yes | yes |
| `generated/effect-runtime-census.tsv` | committed projection | Runtime census | Runtime census | Runtime census | Runtime census | adjacent `.cut-from` | yes |
| `generated/schema-structural-assurance.tsv` | committed projection | Schema assurance | Schema assurance | Schema assurance | Schema assurance | deferred: Schema assurance | yes |
| `c_flags.sexp` | build artifact | Link flags | Link flags | Link flags | Link flags | no | no |
| `lean_flags.sexp` | build artifact | Link flags | Link flags | Link flags | Link flags | no | no |
| `ocaml/eff/eff_manifest.txt.cut-from` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/eff/goldens/corpus.txt.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/coverage.txt.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/p42.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/p42.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/p42.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAcquire.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAcquire.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAcquire.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pActions.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pActions.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pActions.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAwait.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAwait.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pAwait.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBind.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBind.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBind.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBranch.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBranch.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pBranch.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCallback.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCallback.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCallback.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCatch.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCatch.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pCatch.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pDiamond.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pDiamond.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pDiamond.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExit.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExit.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExit.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExternal.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExternal.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExternal.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pExternal.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExternal.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pExternal.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFailCause.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFailCause.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFailCause.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFork.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFork.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pFork.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pGen.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pGen.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pGen.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIll.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIll.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIll.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBranch.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBranch.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBranch.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBreak.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBreak.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllBreak.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllCallback.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllExternalDomain.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllCallback.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllExternalDomain.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllCallback.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllExternalDomain.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllInterruptor.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllInterruptor.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllInterruptor.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllJoin.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllJoin.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllJoin.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllReq.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllReq.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllReq.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllRet.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllRet.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllRet.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllStep.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllStep.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllStep.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllVar.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllVar.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pIllVar.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pJoin.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pJoin.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pJoin.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMasks.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMasks.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMasks.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMatch.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMatch.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMatch.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMergeAll.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMergeAll.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pMergeAll.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOnExit.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOnExit.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOnExit.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOps.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOps.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pOps.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pPair.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pPair.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pPair.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pProvide.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pProvide.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pProvide.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pScoped.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pScoped.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pScoped.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSleep.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSleep.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSleep.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStmts.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStmts.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStmts.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStr.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStr.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pStr.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSuspend.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSuspend.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSuspend.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSync.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSync.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pSync.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pTwo.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pTwo.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pTwo.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pWhile.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pWhile.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pWhile.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pYieldError.bin.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pYieldError.json.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/eff/goldens/pYieldError.ty.cut-from` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | yes | yes |
| `ocaml/goldens/eff/manifest.txt.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/p42.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pAwait.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pBind.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pCatch.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pFork.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pGen.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pLoop.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/goldens/eff/pScope.hex.cut-from` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | yes | yes |
| `ocaml/engine/cas/goldens/cases.txt.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-01.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-02.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-03.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-04.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-05.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-06.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-07.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-08.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-09.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-10.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-11.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-12.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-13.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-14.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-15.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-16.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-17.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-18.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-19.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/digest-20.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-anyref-frame.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-canonical-digest-frame.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-censusEntry.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-censusSchema.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-genesisNode.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-annotation.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-chunk.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-component.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-entry.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-export.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-fiber.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-manifest.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-program.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-query.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-result.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-schema.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-source.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-tree.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-type.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-kind-vector.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-probeEntry.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-probeSchema.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-sampleEntry-payload.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g1-sampleNode.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-badVersion.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-conflict.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-dangling-spec.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-dangling-zero.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-entry-duplicate.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-entry-fresh.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-genesis-exempt.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-handle-in-content.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-kind.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-length.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-occupant.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-ref-fresh.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-schema-duplicate.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g2-wrongKind.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-advance-v2.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-dangling.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v1.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v2.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-stale.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-v1.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g3-wrongKind.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-after-delete-get.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-after-delete.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-after-insert-get.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-after-insert.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-after-update.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entries-base.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entries-deleted.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entries-inserted.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entries-updated.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-nested-key.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-own.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-parent-miss.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-root.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle-own.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent-nested.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-miss.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-own.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g4-get-parent.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-bytes-inside-list.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-bytes-is-a-leaf.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-ctor-seed.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-handle-is-a-leaf.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-malformed-kind.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-malformed-length.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-malformed-nested.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-nested.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-no-refs.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g5-order.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-closure-a.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-closure-b.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-closure-empty.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-a.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-b.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-nodes-a.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-nodes-b.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-replayed.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-reversed.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-probeWord.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-replay-a.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-replay-b.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g6-treeNode.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-dangling-edge.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-flipped-payload.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-good.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-replayed.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-root-ok.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-root-wrong-kind.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/g7-wrong-key.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/manifest.txt.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/val_handle.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `ocaml/engine/cas/goldens/val_ref.hex.cut-from` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | yes | yes |
| `harness/truth/corpus.json.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/result.json.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlite.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlFail.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlCatch.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlExit.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pSqlOrDie.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/tapes/pKv.jsonl.cut-from` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `generated/effect-runtime-census.tsv.cut-from` | committed projection | Runtime census | Runtime census | Runtime census | Runtime census | yes | yes |

## Ingest documentation

The recognizer's tables are a committed projection. Its producer uses the same
sorted source-file SHA-256 stamp protocol; it has no Lean import closure. The
foreign fixture corpus is temporary output of `Tools.Corpus --foreign`, checked
against its construction oracles by the host gate.

Evidence for this family (DI-32): **reproduced** — a fresh byte comparison of the rendered
tables, everything but the informational revision — and **tested**, for the recognizers the
tables describe, whose verdicts are finite runs over the fixture corpus.

| Family | Producer command | Inputs | Consumers | Designated gate and present limit |
| --- | --- | --- | --- | --- |
| Ingest tables | `bun ts/eff/ingest/render-readme.ts`, also `bash scripts/generate.sh --only readme` and last in `--all` (DI-33) | producer and profile/forms/taxonomy `.gen.ts` | recognizer users | `bash scripts/check-ingest.sh`; fresh byte comparison except informational revision |

| Path | Tier | Family | Producer | Inputs | Consumer | Gate | Committed |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ts/eff/ingest/README.md` | committed projection | Ingest tables | family command | family inputs | recognizer users | ingest | yes |

| `ocaml/eff/goldens/metadata.tsv` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/coverage-metadata.txt` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `harness/truth/generated/pFailText.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pFailBoomText.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pTextOrDie.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `ocaml/eff/goldens/pFailText.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFailText.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pFailText.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllFailBool.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllFailBool.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllFailBool.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCauseBool.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCauseBool.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCauseBool.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/program-structure.json` | committed projection | Eff | Eff | Eff | Eff | adjacent `.cut-from` | yes |
| `ocaml/eff/eff_layout.ml` | committed projection | Eff | Eff | Eff | Eff | yes | yes |
| `ocaml/goldens/eff/same-programs.txt` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | adjacent `.cut-from` | yes |
| `ocaml/engine/e4_program_layout.ml` | committed projection | Engine structure | Engine structure | Engine structure | Engine structure | yes | yes |
| `ocaml/engine/e4_program_layout.json` | committed projection | Engine structure | Engine structure | Engine structure | Engine structure | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchError.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchError.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchError.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchIf.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchIf.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pCatchIf.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCatchIf.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCatchIf.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `ocaml/eff/goldens/pIllCatchIf.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | adjacent `.cut-from` | yes |
| `harness/truth/generated/pCatchError.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pCatchIfHit.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pCatchIfMiss.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |
| `harness/truth/generated/pCatchIfRetained.ts` | committed projection | Truth | Truth | Truth | Truth | yes | yes |

| `harness/truth/session/protocol.gen.ts` | committed projection | Host protocol | Host protocol | Host protocol | Host protocol | cut-from header; fresh-byte gate | yes |
| `harness/truth/session/tape.schema.json` | committed projection | Host protocol | Host protocol | Host protocol | Host protocol | adjacent cut-from; fresh-byte gate | yes |
