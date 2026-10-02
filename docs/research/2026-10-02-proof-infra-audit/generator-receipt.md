# Nested structure map audit and isolated repair

Before merging: this repair restores the supported polymorphic structure route in
`--extras`; the older monomorphic emitter limitation below remains. No program type,
proof obligation or generated production output is changed. The full `derived` group
was not regenerated in this unprepared independent worktree; run its normal regeneration
check once on the coordinator's prepared integration head. The narrow generator
regression and unchanged record output comparison below have passed.

Landing base: `c60c2f7c41634ae5166ec30335a80873d70ff0a8` on
`codex/proof-infra-freshness`, after the separate cache repair `f424ba4e`.
All five applied source files were byte-compared with the tested `landing-manifest.json`.
Probe-relative filenames below live under
`/private/tmp/codex-second-eyes-2026-10-01/proof-infra-audit/nested-structure/`.

The original generator refuses its own generated structure map. The smallest repaired path is prepared and checked in this directory; no active checkout was edited. Compiler lane released after the controls.

## Revision and reproduction

Base: `909dda2006b73ad6c0421d4afd5f3a09922b856a`, clean seat `/Users/pooks/Dev/lean4-effect4-seat-extras` at inspection. Exact Git blobs are under `snapshot/`; `source-manifest.json` records SHA-256 and equality with that seat. The fixture's `ElemOf` is the shape already used in `docs/research/2026-09-17-nested-fold-probe.lean`: `Bool`, child, `String`, now used by a one-member family with a nullary leaf and `List (ElemOf Tree)`.

The ordinary fold successfully generates and compiles `Probe.Structure.ElemOf.map`. Importing that fold and asking the same original tool for extras exits 1, before output:

> node.a0 : Probe.Structure.ElemOf Probe.Structure.Tree — `Probe.Structure.ElemOf` already carries a `Probe.Structure.ElemOf.map`

Source chain at the original revision: `Fold.lean:295–301` refuses existing maps; `:840–847` emits the map in the prerequisite fold; `:2487` rereads the family for extras. The newly passing record fixture uses `List (String × Ty)`, which exercises products rather than a custom structure, so it misses this path.

## Repair

`repair.patch` is the complete five-path landing patch. `source.patch` contains the tool-only part; `regression.patch` contains the existing-harness case and three fixtures. `landing-manifest.json` gives the exact checked source hashes. `patched/` holds their complete contents. Extras alone opt into checking an existing structure map. The reader derives a map expression recursively from every declared field and compares the imported map with it by definitional equality at source and target carrier types derived from the structure parameter binder, with independent rigid universe parameters when that binder is polymorphic. Names, identity laws and composition laws alone are not accepted as evidence of the actual field action. The ordinary fold's existing-map refusal remains enabled. Payloads are copied; recursive fields are mapped through the already-read positive positions.

This is a metaprogram admission check, not a new axiom or program representation. Generated laws still undergo ordinary Lean checking. The repair does not accept semantically equivalent but non-definitionally-equal custom implementations; that intentional restriction keeps the change small. Wrongly typed existing maps may fail with Lean's application diagnostic rather than the new field-map diagnostic; they do not produce a successful output.

## Checks actually run

All commands are recorded in `commands.jsonl`, with results in `logs/`. Every compiler command used the exact pinned Lean 4.33.1 binary, `-j1 -M2048 -DwarningAsError=true`, `LEAN_NUM_THREADS=1`, a 120-second subprocess bound and one process at a time. No Lake build, whole generator group or active repository output was used. The only non-SDK tool import, `Tools.GeneratedStamp`, was rebuilt from the exact pinned source into fresh `olean/`; fixture imports were also rebuilt locally. No existing repository `.olean` was consumed. The direct Lean binary directory was prepended to `PATH` because the generator itself asks Lean for the SDK location.

- Original structure fold: generation and compilation exit 0; 12 printed declarations at or below `[propext, Quot.sound]`.
- Original structure extras: expected exit 1 and no output, exact existing-map refusal (`structure-extras-before.log`).
- Repaired structure extras: generation and compilation exit 0; all 20 emitted law receipts at or below the ceiling (`structure-extras-after-compile.log`).
- Structure controls: exit 0. Distinct labels and Boolean payloads survive in order, including a nested child. The universal `allGood_true` invariant uses the child-property hypothesis, rather than proving an always-positive local result; its printed axioms are below the ceiling.
- A same-typed map which silently replaces each String payload is rejected by the new field-map check, exit 1, no output (`bad-map-refusal.log`). The bad-map fixture itself compiles and guards the observed corruption.
- Ordinary fold generation with an imported map still refuses, exit 1, no output (`ordinary-refusal-preserved.log`).
- Existing `GenFix.Record` was rebuilt from exact source: core, generated equality, functions, fold, extras, and `RecordExtras` controls. Before and after extras compile with all 20 law receipts below the ceiling; both existing controls pass (two more axiom reports). Generated extras bytes are identical (`TyExtras-before.lean`, `TyExtras-after.lean`).

`evidence.json` records source/artifact/log hashes, compiler hash, receipt counts, ceiling results and byte comparison. `reproduce.py`, `test_patch.py`, `baseline.py`, `controls.py`, and `runner.py` retain the actual isolated procedure. Earlier draft failures (missing fixture universe, missing output directory, toolchain PATH, helper insertion and `mkArrow` elaboration) are retained separately; they are not reported as successful evidence. The final tool, with binder-derived universes, was rerun through the permanent regression: the original generator fails the new case at the expected refusal; the repaired generator passes all eight steps, including 20 extras law receipts and the payload-corruption refusal. `run_regression.py` calls only `extras_structure` through the existing Context API; its bounded adapter replaces `lake env lean` with the pinned direct compiler and caps, leaving the test case and its assertions unchanged. No earlier harness cases or broad roots run. The final source hashes in `landing-manifest.json` match these final checks.

## Integration scope

The landing patch has exactly five paths: the fold tool, the existing generator harness, and `GenFix/Structure/{Core,Controls,BadMap}.lean`. The permanent `extras-structure` case generates and checks a fold and its extras, observes payload/order and the child-dependent invariant, then refuses the payload-corrupting map before writing output. Earlier standalone probes remain under `src/Probe/` as evidence. No production generated outputs need hand editing. This receipt does not claim every composition of `Pos` has been tested: the new successful structure uses a direct child under a record under a list. Further Option/product combinations remain separate coverage work.

## Monomorphic boundary requested in review

The extra `(α : Type)` fixture is accepted by the original position reader and ordinary fold producer, but the original generated fold fails to compile: it quantifies map carriers at arbitrary `Type u/v` while the structure accepts only `Type 0` (`monomorphic-original-fold-compile.log`). That occurs before extras and is a pre-existing emitter limitation. The repair does not widen emission or claim that route works. Its validator nevertheless now derives carrier sorts from the actual structure parameter binder, so it adds no separate arbitrary-universe assumption. Recursive expected-map construction passes that target carrier to every mapped nested structure field; constructor elaboration enforces the target structure's universe constraints. Supported polymorphic structure success and payload-corruption refusal were rerun against this final source.
