# Generated files

This map names the generated artifacts, their producers and the checks that currently
cover them. It owns this inventory and the generation rule; `docs/ARCHITECTURE.md`
owns the surrounding module boundaries. It is the Phase 0 step 0.2 inventory,
expanded from the five-scout plan (untracked working notes under `docs/research/`).
Later Phase 0 steps add stamps and drift checks; the table records their absence now.

## The rule

An artifact with no row in this map may not be committed. Every generated artifact
has one producer command and one designated gate. Its header must name both and
what it was cut from. A row with no gate records an owner and a date below; these
are explicit migration debts, not passing checks.

The three tiers are:

- **build artifact**: produced by the build system or build setup and never committed;
- **committed projection**: generated output kept in Git, to be stamped and checked
  byte for byte; the gaps in that requirement are recorded below;
- **vendored input**: copied from an identified source, with provenance recorded.

The required stamp is one line in the output's comment syntax:

```
cut-from: rev=<git describe --always --dirty> toolchain=<lean version> inputs=<sha256>
```

Step 0.4 must add one Lean implementation that computes `inputs` from the sorted
Lake traces of the producer's import closure. The revision is informational and is never compared.
The stale check compares the input digest without regeneration. The drift check
regenerates into temporary files and compares the output bytes. Neither a compiler
check nor a host test establishes that a committed output matches today's Lean source.

## Commands and current coverage

The family names in the file table refer to all four columns in this table: producer
command, inputs, consumers and designated gate. Commands run from the repository root
unless a working directory is stated. Hold `.lake/LANE.lock` for any Lean process,
use `LEAN_NUM_THREADS=3`, and use `-M4096` for Lean drivers. Run one Lean process at a time.
A command listed here is a reproduction instruction, not a claim that it was run for
this inventory. `cut-from` is the header stamp; a cached gate verdict is separate.

| Family | Producer command | Inputs | Consumers | Designated gate and present limit |
| --- | --- | --- | --- | --- |
| Derived Json | `lake env lean -M4096 --run tools/Effect4Gen/Driver.lean --group Json` | `tools/Effect4Gen/manifest.json`, `tools/Effect4Gen/guards/json.lean`, `Effect4.Store.Canonical` | `Effect4.Store.Derived.Schema`, Effect4 library | `lake build Test` runs `Test/Store/DerivedCheck.lean`; shape only, drift owed by Phase 0 |
| Derived Schema | same driver, `--group Schema` | manifest, `tools/Effect4Gen/guards/schema.lean`, `Effect4.Store.Derived.Json` | Effect4 library | `lake build Test`; shape only, drift owed by Phase 0 |
| Derived Program | same driver, `--group Program` | manifest, `tools/Effect4Gen/guards/program.lean`, `Effect4.Program.Native`, `Effect4.Store.Canonical` | `Effect4.Api`, program wire | `lake build Test`; shape only, drift owed by Phase 0 |
| Derived Pin | same driver, `--group Pin` | manifest, `tools/Effect4Gen/guards/pin.lean`, `Effect4.Store.Pin`, `Effect4.Store.Node` | store | `lake build Test`; shape only, drift owed by Phase 0 |
| Eff | `lake env lean -M4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff` | `src/OCaml5/Eff/World.lean`, `src/OCaml5/Eff/Emit.lean`, imported Lean declarations | `effect4_eff`, `effect4_engine` | `bash scripts/check-ocaml.sh dune-tests`; behavior tests, drift owed by Phase 0 |
| Eff goldens | same EffGen command | `src/OCaml5/Eff/Goldens.lean` | `ocaml/eff/test/dune` | `bash scripts/check-ocaml.sh dune-tests`; committed test data, no regeneration comparison |
| Wire goldens | `lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff` | `Effect4.Program.Wire.Corpus`, `src/OCaml5/Tools/EffWire.lean` | `ocaml/eff/test/test_lean_wire.ml` | `bash scripts/check-ocaml.sh dune-tests`; test skips if golden directory is absent |
| CAS goldens | `lake env lean -M4096 --run src/OCaml5/Tools/CasGoldens.lean ocaml/engine/cas/goldens` | Store Word and Genesis, Machine Stores, `Test.Store.NodeContract` | `ocaml/engine/cas/test/dune` | none in sweep; owner: engine lane, 2026-09-08. Manual `cd ocaml && dune test engine`; Phase 0 step 0.7 adds the row |
| LCNF | exact command in each output's first comment, run with `lake env` before `lean` | `src/OCaml5/Tools/LcnfGen.lean`, `src/OCaml5/Lcnf/`, named import and roots; engine also reads `ocaml/engine/externs.txt` and `ocaml/engine/tools/api_engine_prelude.ml` | `effect4_gen`, `effect4_engine` | gen files: `bash scripts/check-ocaml.sh dune-tests`; engine file: `bash ocaml/engine/tools/gen-check.sh` (manual, machine path repair owed by step 0.3). Neither regenerates |
| TypeScript | `bash scripts/generate-ts-eff.sh` | `OCaml5.Eff.World`, native rows, ingestion taxonomy, forms, profile, `lakefile.toml`, `src/Effect4/Codegen/Print.lean` | TypeScript readers, checkers and tests | `bash scripts/check-ts-eff.sh`; byte comparison, in sweep |
| Avatar descriptions | exact `Describe.lean` command in each file's `Regenerate:` header, stdout redirected to that file | `src/OCaml5/Tools/Describe.lean`, Machine Stores, Fibers and Context | `OCaml5.Avatar.Check`, hand overlays | none; owner: avatar retirement lane, 2026-09-08. No new gate is commissioned for retiring artifacts |
| Avatar blocks | `bash ocaml/avatar/render-deep.sh <mode> --write`, mode is the file's `deep_` suffix | `src/OCaml5/Tools/RenderDeep.lean`, `OCaml5.Avatar.parts` | avatar library | same command without `--write`, manual; owner: avatar retirement lane, 2026-09-08. Only the marked block is generated |
| Archived daemon inputs | `bash ocaml/server/tools/vendor-archived-inputs.sh 606918e` | archived Git revision `606918e` | daemon's dune rules | `bash scripts/check-ocaml.sh daemon-protocol`; provenance blobs in `ocaml/server/generated/archived-from.tsv`, no independent blob-check gate; owner: daemon lane, 2026-09-08 |
| Daemon | `cd ocaml && dune build server` | explicit rules in `ocaml/server/dune`, archived inputs, avatar sources and Lean machine | daemon library | `bash scripts/check-ocaml.sh daemon-protocol`; build dependencies owned by dune |
| Truth | corpus: `lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json`; other outputs: `bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300` | Eff corpus, `harness/truth/prelude.ts`, pinned rc.112 | truth differential, TypeScript corpus check | `bash scripts/check-truth.sh`; fresh generation and comparison plus bounded host observations |
| Schema TypeScript | `lake env lean -M4096 harness/schema-generation/EmitFixture.lean` for Person, `EmitCoverageFixture.lean` for AllRepresentations, `EmitMultiFixture.lean` for TwoRoots; redirect stdout to named output | `Effect4.Codegen.Schema`, fixture declarations | three runtime checks in `harness/schema-generation/` | `bash scripts/check-schema-typescript-generation.sh`, currently manual; joining sweep is the approved Phase 0 decision |
| Runtime census | `bash scripts/generate-effect-runtime-census.sh > generated/effect-runtime-census.tsv` | pinned rc.112 sources listed by output | `docs/RUNTIME-COVERAGE.md`, `Test/Audit/RuntimeCoverage.lean` | `bash scripts/check-effect-runtime-census.sh`, in sweep |
| Schema assurance | `bash scripts/generate-schema-structural-assurance.sh > generated/schema-structural-assurance.tsv` | schema sources, frozen batteries, pinned host sources listed by generator | schema assurance report | `bash scripts/check-schema-structural-assurance.sh`, manual by owner decision; owner: Schema assurance lane, 2026-09-08 |
| Link flags | `bash ocaml/link/tools/lean-flags.sh` | local Lean installation and Bridge object | `ocaml/link` build | none; owner: bridge lane, 2026-09-08. Local output names below are targets under `ocaml/link`, absent until that build runs |

## Engine boundary

Step 0.1 repairs compilation. `E4_program.pin` still refuses every load because the
wire's `native_op` alphabet includes the timer operations that the engine lacks.
The converter refuses those operations with `Ordinal_mismatch`; it does not silently
map them. Phase 1 must regenerate the engines before this refusal can be cleared.

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
| `src/Effect4/Store/Derived/Json.lean` | committed projection | Derived Json | Derived Json | Derived Json | Derived Json | no | yes |
| `src/Effect4/Store/Derived/Schema.lean` | committed projection | Derived Schema | Derived Schema | Derived Schema | Derived Schema | no | yes |
| `src/Effect4/Program/Derived.lean` | committed projection | Derived Program | Derived Program | Derived Program | Derived Program | no | yes |
| `src/Effect4/Store/PinDerived.lean` | committed projection | Derived Pin | Derived Pin | Derived Pin | Derived Pin | no | yes |
| `ocaml/eff/eff_types.ml` | committed projection | Eff | Eff | Eff | Eff | no | yes |
| `ocaml/eff/eff_wire.ml` | committed projection | Eff | Eff | Eff | Eff | no | yes |
| `ocaml/eff/eff_json.ml` | committed projection | Eff | Eff | Eff | Eff | no | yes |
| `ocaml/eff/eff_native.ml` | committed projection | Eff | Eff | Eff | Eff | no | yes |
| `ocaml/eff/eff_manifest.txt` | committed projection | Eff | Eff | Eff | Eff | no | yes |
| `ocaml/eff/goldens/corpus.txt` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/coverage.txt` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/p42.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/p42.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/p42.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAcquire.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAcquire.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAcquire.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pActions.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pActions.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pActions.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAwait.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAwait.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pAwait.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBind.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBind.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBind.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBranch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBranch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pBranch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCallback.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCallback.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCallback.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCatch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCatch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pCatch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pChoose.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pChoose.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pChoose.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pExit.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pExit.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pExit.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFailCause.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFailCause.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFailCause.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFork.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFork.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pFork.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pGen.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pGen.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pGen.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIll.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIll.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIll.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBranch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBranch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBranch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBreak.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBreak.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllBreak.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllCallback.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllCallback.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllCallback.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllInterruptor.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllInterruptor.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllInterruptor.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllJoin.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllJoin.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllJoin.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllReq.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllReq.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllReq.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllRet.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllRet.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllRet.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllStep.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllStep.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllStep.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllVar.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllVar.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pIllVar.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pJoin.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pJoin.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pJoin.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMasks.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMasks.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMasks.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMatch.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMatch.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pMatch.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOnExit.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOnExit.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOnExit.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOps.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOps.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pOps.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pPair.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pPair.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pPair.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pProvide.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pProvide.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pProvide.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pScoped.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pScoped.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pScoped.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSleep.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSleep.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSleep.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStmts.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStmts.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStmts.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStr.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStr.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pStr.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSuspend.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSuspend.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSuspend.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSync.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSync.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pSync.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pTwo.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pTwo.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pTwo.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pWhile.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pWhile.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pWhile.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pYieldError.bin` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pYieldError.json` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/pYieldError.ty` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/val_handle.hex` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/eff/goldens/val_ref.hex` | committed projection | Eff goldens | Eff goldens | Eff goldens | Eff goldens | no | yes |
| `ocaml/goldens/eff/manifest.txt` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/p42.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pAwait.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pBind.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pCatch.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pFork.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pGen.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pLoop.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/goldens/eff/pScope.hex` | committed projection | Wire goldens | Wire goldens | Wire goldens | Wire goldens | no | yes |
| `ocaml/engine/cas/goldens/cases.txt` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-01.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-02.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-03.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-04.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-05.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-06.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-07.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-08.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-09.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-10.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-11.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-12.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-13.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-14.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-15.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-16.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-17.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-18.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-19.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/digest-20.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-anyref-frame.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-canonical-digest-frame.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-censusEntry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-censusSchema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-genesisNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-annotation.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-chunk.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-component.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-entry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-export.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-fiber.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-manifest.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-program.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-query.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-result.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-schema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-source.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-tree.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-type.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-kind-vector.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-probeEntry.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-probeSchema.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-sampleEntry-payload.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g1-sampleNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-badVersion.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-conflict.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-dangling-spec.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-dangling-zero.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-entry-duplicate.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-entry-fresh.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-genesis-exempt.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-handle-in-content.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-malformedRef-length.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-occupant.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-ref-fresh.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-schema-duplicate.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g2-wrongKind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-advance-v2.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-dangling.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v1.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-roots-after-v2.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-stale.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-v1.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g3-wrongKind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-after-delete-get.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-after-delete.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-after-insert-get.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-after-insert.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-after-update.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entries-base.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entries-deleted.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entries-inserted.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entries-updated.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-nested-key.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-parent-miss.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-entryAt-root.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-cycle.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-grandparent.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-miss.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-own.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g4-get-parent.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-bytes-inside-list.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-bytes-is-a-leaf.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-ctor-seed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-handle-is-a-leaf.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-malformed-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-malformed-length.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-malformed-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-nested.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-no-refs.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g5-order.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-closure-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-closure-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-closure-empty.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-closure-tree-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-nodes-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-nodes-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-replayed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-probeWord-reversed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-probeWord.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-replay-a.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-replay-b.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g6-treeNode.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-dangling-edge.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-flipped-payload.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-good.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-replayed.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-root-ok.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-root-wrong-kind.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/g7-wrong-key.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/manifest.txt` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/val_handle.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/engine/cas/goldens/val_ref.hex` | committed projection | CAS goldens | CAS goldens | CAS goldens | CAS goldens | no | yes |
| `ocaml/gen/api_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | no | yes |
| `ocaml/gen/fibers_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | no | yes |
| `ocaml/gen/machine_gen.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | no | yes |
| `ocaml/engine/api_engine.ml` | committed projection | LCNF | LCNF | LCNF | LCNF | no | yes |
| `ts/eff/eff.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `ts/eff/forms.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `ts/eff/json.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `ts/eff/profile.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `ts/eff/taxonomy.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `ts/eff/wire.gen.ts` | committed projection | TypeScript | TypeScript | TypeScript | TypeScript | no | yes |
| `src/OCaml5/Avatar/Derived/Context.lean` | committed projection | Avatar descriptions | Avatar descriptions | Avatar descriptions | Avatar descriptions | no | yes |
| `src/OCaml5/Avatar/Derived/Fibers.lean` | committed projection | Avatar descriptions | Avatar descriptions | Avatar descriptions | Avatar descriptions | no | yes |
| `src/OCaml5/Avatar/Derived/Stores.lean` | committed projection | Avatar descriptions | Avatar descriptions | Avatar descriptions | Avatar descriptions | no | yes |
| `ocaml/avatar/deep_stores.ml` | committed projection | Avatar blocks | Avatar blocks | Avatar blocks | Avatar blocks | no | yes |
| `ocaml/avatar/deep_layer.ml` | committed projection | Avatar blocks | Avatar blocks | Avatar blocks | Avatar blocks | no | yes |
| `ocaml/avatar/deep_context.ml` | committed projection | Avatar blocks | Avatar blocks | Avatar blocks | Avatar blocks | no | yes |
| `ocaml/avatar/deep_forkflow.ml` | committed projection | Avatar blocks | Avatar blocks | Avatar blocks | Avatar blocks | no | yes |
| `ocaml/server/generated/archived-from.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/harness-trace/deferred-fixture.ts` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/harness-trace/fibers-fixture.stub.ts` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/harness-trace/layer-fixture.ts` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/harness-trace/ref-fixture.ts` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/harness-trace/scope-fixture.ts` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredDoubleComplete.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredFailAwait.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredPendingAwait.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredPollPending.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredSucceedAwait.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/deferred/deferredTwoHandles.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/buildMemo.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/buildOnce.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/freshRebuild.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/freshRegion.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/freshRelease.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/rebuildAfterClose.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/releaseOrder.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/layer/scopedRelease.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/masks.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/getAndSetOld.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/makeGet.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/modifyOld.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/setGet.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/takeUnderflow.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/twoRefs.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/ref/updateTwice.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/scope/addAfterClosed.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/scope/closeTwice.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/scope/lifo.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/server/generated/traces/scope/remove.tsv` | vendored input | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | Archived daemon inputs | no | yes |
| `ocaml/_build/default/server/e4d_masks_data.ml` | build artifact | Daemon | Daemon | Daemon | Daemon | no | no |
| `ocaml/_build/default/server/e4d_families_data.ml` | build artifact | Daemon | Daemon | Daemon | Daemon | no | no |
| `ocaml/_build/default/server/e4d_armmap.ml` | build artifact | Daemon | Daemon | Daemon | Daemon | no | no |
| `ocaml/_build/default/server/e4d_pins.ml` | build artifact | Daemon | Daemon | Daemon | Daemon | no | no |
| `harness/truth/generated/p42.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pAcquire.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pAcquireClosed.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pAwait.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pBind.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pCatch.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pFork.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pGen.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pLoop.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pProvide.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pProvideMerge.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pProvideTwice.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pScope.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/generated/pTwo.ts` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/corpus.json` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/result.json` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/truth/result.md` | committed projection | Truth | Truth | Truth | Truth | no | yes |
| `harness/schema-generation/AllRepresentations.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | no | yes |
| `harness/schema-generation/Person.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | no | yes |
| `harness/schema-generation/TwoRoots.generated.ts` | committed projection | Schema TypeScript | Schema TypeScript | Schema TypeScript | Schema TypeScript | no | yes |
| `generated/effect-runtime-census.tsv` | committed projection | Runtime census | Runtime census | Runtime census | Runtime census | no | yes |
| `generated/schema-structural-assurance.tsv` | committed projection | Schema assurance | Schema assurance | Schema assurance | Schema assurance | no | yes |
| `c_flags.sexp` | build artifact | Link flags | Link flags | Link flags | Link flags | no | no |
| `lean_flags.sexp` | build artifact | Link flags | Link flags | Link flags | Link flags | no | no |
