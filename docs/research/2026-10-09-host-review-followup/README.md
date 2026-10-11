# Host review follow-up

Correct the shared import reader before extending its supported header profile.
Keep C3b's reply-tape premise and loop case explicit before replacing the older compile proofs.

## Scope and pins

- Review base: `0e69fde97c81407d31cc2bc9aa61b2c71f27ca4e`.
- Reviewed landing: `df9d1c408186e5967e96d658e2306a1da437d6d4`.
- Prior semantic review: `321cda73d2d9ae8567d5b4bcd4da283df89d9618`.
- Three GPT-6.1 Sol reviewers independently read the collector, import reader and revised host-call design.
- The parent runs the finite controls in an isolated worktree.
- `input-pins.json` records the reviewed input hashes.
- The selected inputs match the landing.
- No production file, owner ruling or implementation session changes in this review.

The reviewed note is `docs/research/2026-10-09-host-calls-and-cleanup.md`.
Its changes land during the review.
The initial agent reports describe uncommitted edits; their hashes match the landing.

## Meaningful resolutions

### Proof placement and the cleanup receipt

HCC-01 is resolved.
`Tools.Semantics.registry` in `tools/ProofGraph/Registry.lean` now includes `Effect4.Laws.Program.Agreement.Segment`.
The same report-selection control reads 36 available declarations and selects all 36.
The previous control selected none.

This checks the exact module filter.
It does not rerun the whole semantics report.
Auxiliary-name exclusions still apply after this filter.

HCC-03 is resolved.
The note now distinguishes the narrowed `flushAll_Myield` helper from the unchanged public completion guarantees.
The empty-preloaded-answer premise is explicit.

HCC-02 receives an explicit disposition.
The note documents the move to `Effect4.Program.Denote.LoopedRows` and declines the compatibility alias.
The old qualified name remains unavailable.
No current caller requires it; this remains a documented internal rename.

### An axiom's type

`ProofGraph.usedConstantsOf` in `tools/ProofGraph/Axioms.lean` now reads an axiom's type.
The same finite control runs before and after the repair.
It creates `A : Type` and `a : A` in a temporary environment.

| Control | Before | After |
| --- | --- | --- |
| Direct axiom | found | found |
| Axiom in the dependent axiom's type | omitted | found |
| Agreement with Lean's collector on these fresh acyclic constants | no | yes |
| Shared memo agrees with fresh traversal | yes | yes |
| Explicit stop remains a leaf | yes | yes |
| Temporary axioms remain outside the imported environment | yes | yes |

The cycle algorithm remains unchanged.
These controls test executable trust tooling; they do not prove its algorithm.
The environment, memo, stop-predicate and finite-budget limits remain explicit in the source.

### The host-call design

The revised plan addresses HC-R1, HC-R2 and HC-R3 at the design level.
It places request correspondence before H9.
It retains row, request, stores, continuation and transcript position in the proposed residual relation.
The handler adapter must use reply admission at the checked call instance.

The live call view reads existing machine and ledger data.
It keeps optional binding information and separates history from current waits.
Uniqueness applies to an advancing session lineage.
It does not claim durable uniqueness after restoring an earlier snapshot.

These are design improvements.
H9, the residual relation and the checked native binding remain open.
No host compatibility grade changes in this review.

## New findings

### HCF-01: a quoted import loses its dependency edge

Evidence status: reproduced finite defect.
Scope: valid quoted Lean module identifiers.
Priority: P2.

`header_imports` in `scripts/lib/lean_imports.py` returns the spelling `«Effect4».Program.Ty`.
Lean 4.33.1 reads that identifier as `Effect4.Program.Ty`.
`QuotedImport.lean` compiles, so this is an accepted Lean import.

`imports_of` in `scripts/lib/build_profile.py` filters names against filesystem-derived module names.
It therefore drops this dependency.
The unquoted control retains the edge; restoring that control passes again.

The same reader feeds fixture inventory and generation.
Keep canonical dependency identity distinct from any source spelling required for emission.
Normalize names once in the shared reader, with a Lean-parser control.
Do not add independent normalizers to each caller.

No searched production import uses this spelling.
This is a latent reader defect, not a measured current build-time error.

### HCF-02: documentation comments do not end the header

Evidence status: reproduced finite parser mismatch.
Scope: documentation commands followed by another import.
Priority: P3.

`_tokens` in `scripts/lib/lean_imports.py` skips `/-!` and `/--` as ordinary comments.
Lean's header parser stops there.
The shared reader instead includes the later import.

Both documentation forms reproduce the mismatch.
Ordinary nested block comments remain valid positive controls.
The existing `test_header_ends` uses a later `set_option`, which masks this difference.

Stop at documentation-command tokens.
Add the two direct controls without an intervening command.
The later import is outside Lean's header; no false acceptance by a compiled gate is established.

### HCF-03: C3b needs both the loop case and the tape premise

Evidence status: source-checked plan gap, with finite controls.
Scope: the proposed compile-proof replacement, not the landed execution semantics.
Priority: P2.

`localRunC_compile` in `src/Effect4/Laws/Program/Agreement/Calls.lean` requires `StraightRows`.
It rejects an iteration that `Looped` accepts.
`localRun_compileB` in `src/Effect4/Laws/Program/Agreement/Loop.lean` handles that iteration.

Counting and depth information alone cannot supply the missing loop case.
Retain or port the loop induction, or add its budgeted counterpart before deleting the old family.

The proposed projection also needs an explicit reply-tape premise.
The finite control starts at one external call.
With one supplied reply, `localRunC` exits within two steps.
At the same budget, `localRun` returns `none`.
With an empty reply tape, `localRunC` waits instead.

Restrict the old-run projection to the empty tape, or state a proved no-call premise.
Do not project arbitrary answered calls into the old run.

This obligation serves the existing `run-eq-meaning` and `loop-agreement` claims under `translation-simulation`.
Its consumers retain the exit, stores, fragment, depth and quantitative premises of their existing statements.
The compiler connector also serves `rows-denotation-session` under R6.
It establishes no physical-host behavior or progress.
No new theorem statement or planned goal is introduced here.

## Commands and results

`results.json` records command arguments, exit codes and elapsed times.
`build.log` records the focused build:

```sh
LEAN_NUM_THREADS=3 lake build Test.Audit.ProofGraph Tools.Semantics
```

The build passes.
The collector, placement, projection and quoted-import probes pass.
The import reader's eight existing tests pass.
The independent seven-case comparison finds the three expected case mismatches across HCF-01 and HCF-02.
`Ty.lean`'s four public imports now appear.

The first projection probe uses an invalid empty-record shorthand for `Stores`.
Its Lean elaboration fails before evaluation.
The repaired probe uses `Stores.empty` and passes.
That setup error is retained; it is not evidence against the implementation.

The retained Lean diagnostics in `projection.log` and `attempt1-projection.log` contain trailing spaces.
The whitespace check excludes only those two logs.
Their bytes remain unchanged.

No TypeScript compiler, OCaml host, whole-library gate or full sweep runs here.

## Checkpoint

| Finding | Status at the reviewed landing |
| --- | --- |
| HCC-01 | resolved; module selection reproduced |
| HCC-02 | deliberate rename documented; old qualified name remains absent |
| HCC-03 | resolved; narrowed helper documented |
| Axiom-type omission | resolved; before/after controls reproduced |
| HC-R8's original public-import and ordinary-comment omissions | resolved; controls reproduced |
| HCF-01 | open; shared name normalization |
| HCF-02 | open; documentation-command header boundary |
| HCF-03 | open design requirement for C3b |
| H9 and request-retaining residual relation | proposed; no new composition theorem claimed |
