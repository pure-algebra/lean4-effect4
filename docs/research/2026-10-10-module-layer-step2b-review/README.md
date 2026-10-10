# Module-layer step 2b review

The current draft includes the verified proof repair.
Its proof sources match the isolated candidate exactly.
The separate TypeScript printing fixture also has its source correction.
Do not reapply `proof-only.patch`.
The [follow-up](followup-1913/README.md) records the new target checks and source comparison.

## Reviewed state

- Primary HEAD: `e9d6863eed613a40fe90444925daf5e3bec818c5`.
- Implementation base: `1c98dd94831c060e591cd7e5bef19d6528c5d22a`.
- Implementation worktree: `/Users/pooks/Dev/lean4-effect4-wt/module-layers`.
- Review parent: `4589867aae47532d847c13a4a4231c049e03884a`.
- Draft evidence: `draft.patch`, `draft-status.txt`, and the recorded input hashes.

The reviewed changes remain uncommitted during the checks.
Claude's implementation session owns them.
The review changes only this packet in the isolated review worktree.

## ML2B-TRUST-01: the round-trip proof exceeds the axiom boundary

Evidence kind: cycle-aware dependency audit of compiled draft laws.
Status: confirmed in the initial draft; the current working tree contains the verified repair.
Scope: the four selected code generation and hoisting law modules.

`moduleLayersOf_split` in `src/Effect4/Laws/Codegen/Module.lean` uses `List.filter_eq_nil_iff` twice.
That toolchain lemma reaches `Classical.choice`.
The project admits only `propext` and `Quot.sound`.

The helper carries the dependency into four consumers:

- `readModule_printModule_defs` in `src/Effect4/Laws/Codegen/Module.lean`;
- `readModule_printModule_defs_readable` in `src/Effect4/Laws/Api/ModuleReadable.lean`;
- `ModuleEmission.readModule` in the same file;
- `Api.printModule_roundTrip` in the same file.

This finding does not show a false round-trip statement.
It shows that these claims fail the project's axiom gate even though their modules compile.

The candidate replaces the two filter proofs with constructive membership arguments.
It follows `Slice.omitted_full` in `src/Effect4/Laws/Slice/Lattice.lean`.
It changes no premise, result, semantics registry pointer, or runtime operation.
The placement and dependency outline are in [PLAN.md](PLAN.md).

## ML2B-TEST-01: the declaration fixture selects a missing field

Evidence kind: compilation of an exact copy of the draft fixture.
Status: confirmed in the first draft; the owner repairs its source during this review.
Scope: `moduleLayered`'s declaration-order control in `Test/Codegen/DefinitionsPrint.lean`.

The control selects `.name` from `TypeScript.Decl`.
That type has several constructors and no such field.
The name belongs to the constant declaration held by `.const`.

The candidate matches `.const` and returns its name.
Other declarations return `none`, so the assertion still checks that every declaration is a constant.
No new helper enters the public API.

Claude subsequently moves the program to `moduleLayerProg` in `Test/Program/DefinitionsControls.lean`.
The current printing fixture matches constants through `filterMap`.
It no longer selects the missing field.
The owner also registers the program in the runtime comparison corpus and starts regeneration.
That run remains pending at this checkpoint.
This review verifies the source correction; it does not rerun the owner's revised fixture.
The earlier candidate fixture's successful compilation remains separate evidence.

## Finite controls

`Probe.lean` checks a module layer that depends on an earlier module layer.
A definition and the main program both name it.
A second block combines module layers with an ordinary hoisted layer.
The controls check types, declaration order, reconstruction, and fixed runs.

Malformed declaration paths remain refused at `moduleLayersOf` in `src/Effect4/Codegen/Read.lean`.
The cases include duplicates, gaps, reverse order, and a nested path.
The public checker refuses a reference into a nested part of a module layer.
A definition's own layer remains outside the current printing slice.

The composed run reaches a live frontier at budget 250.
The same run finishes with value 7 at budget 2000 under `Api.run`'s existing decisions.
No extra host answer or clock decision is needed.
This is a budget control, not a liveness theorem or a runtime defect.

The initial review fixture gives its second service key the boolean value code while storing a natural number.
That fixture is corrected to the natural-number value code.
The initial failed checks remain under `initial/`.
They are not reported as an implementation defect.

## Consumer boundary

Evidence kind: source inspection of the checked reading boundary.
The slice supports reconstruction through `Api.readModule`.
That is distinct from accepting edited TypeScript through `Api.admitModule`.
`SourceBindings` in `src/Effect4/Codegen/SourceBindings.lean` conservatively refuses forward references inside deferred closures.
Definitions printed before their module layers can meet that refusal.

This boundary predates the slice.
It is not a failure of `module-defs-round-trip`, whose statement promises reconstruction.
A live editor should distinguish successful reconstruction from successful source admission.
Any change to this lexical check needs its own design and refusal controls.

## Verification

The final run starts at `2026-10-10T19:04:11.599786+00:00`.
The candidate recompiles `Laws/Codegen/Module.lean` and its direct consumer, `Laws/Api/ModuleReadable.lean`.
The cycle-aware audit accepts 346 declarations within `[propext, Quot.sound]`.
It reports no planned goals and no declarations depending on planned goals.
All six named consumers in `Audit.lean` report `proved`.

All 24 finite controls pass.
The exact draft fixture fails on its missing field.
The corrected fixture compiles with warnings treated as errors.
All 975 recorded inputs remain unchanged during the final run.

Commands run from the isolated review worktree:

```sh
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-module-layer-step2b-review/run_checks.py
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-module-layer-step2b-review/run_candidate.py
```

The first command exposes the draft's axiom failure and exits with status 1.
The second command recompiles the candidate and checks the original fixture's expected failure.
It exits with status 0.
Exact Lean commands, durations, outputs, and hashes are in `candidate-result.json`.
The draft axiom failure is in `audit.out`.
The repaired dependency graph is in `candidate-audit.out`.
The combined candidate patch passes `git apply --check` before the owner's test correction.
After that correction, `proof-only.patch` passes the same check against the current draft.
The whitespace check excludes only the three retained draft patch files.
Their blank diff-context lines retain the exact captured bytes.
All other staged files pass the whitespace check.

The overlay copies imported artifacts and their `.ir` and `.ir.sig` files without changing the implementation artifacts.
The two law modules are rebuilt locally; their other imported dependencies are reused.
The record checks stability, not a fresh rebuild of every dependency.
The initial review performs no full sweep, TypeScript check, host comparison, merge, or push.
The follow-up records a separate narrow target check and three runtime observations.

## Handoff

Keep the applied proof repair; its source matches the independently verified candidate.
Run the narrow builds and cycle-aware audit before committing the landing.
Run the affected target and runtime comparison gates under the repository's build rules.
Keep the readable-domain premises on the public round-trip claim.

The owner corrects the semantics registry prose during the follow-up.
It now distinguishes a definition body's own layer from its reference to a module layer.
The anchors remain `module-defs-round-trip` in `tools/ProofGraph/Registry.lean` and its property in `docs/core/semantics.md`.

## Checkpoint

The primary HEAD remains `e9d6863eed613a40fe90444925daf5e3bec818c5` at the start of this review.
ML2B-TRUST-01 is repaired in uncommitted step 2b, with an exact match to the verified candidate.
ML2B-TEST-01 has its source correction in the owner's working tree.
ML2-C2-01 has a verified working-tree repair, recorded in the follow-up.
LV-OW-01 remains unchanged from its saved receipt.
The candidate does not apply either earlier repair.
