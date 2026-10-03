# Landed authoring, host-session and proof-reuse tranche

Merge fact: all implementation slices are integrated into the primary checkout on
`refactor/phase1-phase3`, and the combined affected graph passes. General progress and the remaining full T obligations are not being reported as closed.
The reserved host-failure mismatch remains an explicit contract dependency, with a checked
counterexample. The pre-existing dirty authorities/generated files are byte-for-byte unchanged.

Base: `8913519b146d95c07a3eaa195df1a1fcda2c642a`.
Verified implementation head, fast-forwarded into `refactor/phase1-phase3`: `c05eb111d792a953660e05b6c9d2049b05300abf`.
This receipt is a following documentation-only commit. No push.

## What landed

| Integrated commit | Result | Placement and evidence |
| --- | --- | --- |
| `8db6dcf8` | Straight-program composition, suspension removal and an actual exit/full-store execution comparison with computed sufficient budgets. | [Composition receipt](meaning-eq-receipt.md); concept 10, R8, bounded T5 contribution. |
| `dd26f097`, `63aaf059` | General same-sort path replacement with lookup/overwrite/restore/disjoint laws; existing layer editing uses the shared operation. | [Editing receipt](../2026-10-03-program-path-editing/receipt.md); concept 7, R8. |
| `5c5fca03`, `283ebbf6` | Successful synchronous store operations leave the complete external store unchanged; two existing proof consumers stop repeating that argument. | [Store-frame receipt](../2026-10-03-store-frame-laws/receipt.md); seven repeated clauses become one, eight redundant caller arguments removed. |
| `0b14244f`, `6bf4d3a2` | Recorded work inspection and an opt-in one-control planner through the checked journal. | [Session-work receipt](../2026-10-03-session-work/receipt.md); concept 4, R12/R13, T3 prerequisites only. |
| `057bb642`, `656ad0f6` | `Built.rebuild` rechecks the whole edited program against the original table and names, retaining located refusals. | [Rebuild receipt](../2026-10-03-program-path-editing/rebuild-receipt.md); concept 2, R8, checked authoring consumer. |
| `69974993`, `5befe488` | Actual accepted successful replies connect to their prepared values for shape-decided answer types on a non-stuck machine. | [Host-reply receipt](../2026-10-03-session-work/t4-receipt.md); concept 9, bounded T4 contribution. |
| `c05eb111` | Public usage documentation, a compiled editing example and the downstream runnable-observation proof repair. | [API surface](../../core/api-surface.md), [usage audit](Usage.lean), [integration commands](evidence/integration-commands.txt). |

Changed source/test paths are the exact output of `git diff --name-only 8913519b c05eb111d792a953660e05b6c9d2049b05300abf`;
each slice's prior brief and receipt records its narrower allowlist. The coordinator's only
additional proof edit is `ReasonsR.hasRunnable_eq_ref`: explicitly unfold the extracted
`isRunnable` predicate, with the original theorem and observation unchanged. The new law
module and test are imported at the documented existing root anchors.

## Verification and integration

- Individual slice builds, positive/negative fixtures and axiom inspections passed before
  integration. Independent source reviews found no remaining substantive issue.
- The first combined build found one downstream proof that still expected the runnable
  predicate inline. The repaired module passed its narrow build (343 jobs).
- Final command: `lake build Effect4 Effect4.Laws Test.Codegen.ReadContract Test.Machine.Runtime.StoresLawsContract Test.Program.SimulationContract Test.Program.MeaningEqContract Test.Run.RunContract Test.Program.AuthorContract Test.Program.AuthoringScope Effect4.Api.RefusalsDerived Test.Api.HostSessionContract Test.Api.FrontierContract`.
  Exit 0, **611 jobs**, including the complete public and law roots and all affected fixtures.
  (The raw build log was not retained; `evidence/integration-commands.txt` records the commands
  and exit codes. Reproduced independently by Claude on 2026-10-03, 611 jobs, 0 errors.)
- `lake env lean docs/research/2026-10-03-api-completion/Usage.lean`: exit 0. The published
  example compiles, the exported signatures are checked, and both inspected observation
  connector proofs use `[propext, Quot.sound]`. All new slice declarations stay within that
  same axiom ceiling in their retained audits.
- `git diff --check`: exit 0. The existing M6 ledger remains 20/20, M7 4/4, M7Results 1/1;
  these pre-existing closures are not counted as new results from this tranche.
- The primary checkout (`refactor/phase1-phase3`) fast-forwarded from the base to the verified implementation head. Hashes before and
  after confirm that `docs/STATE.md`, `docs/core/architecture-map.html`,
  `docs/core/semantics.md`, `generated/semantics.json` and `generated/semantics.md` are
  unchanged. Those are still the only pre-existing dirty paths. No build in the primary checkout,
  generated-output rewrite, push or external tracker update occurred.

No whole Test/AxiomGate/make-check sweep or TypeScript/OCaml host run is claimed. These are
Lean affected-graph checks and checked Lean theorems, accompanied by explicitly finite API
fixtures. The proposed central registry additions remain in the seat receipts because their
owning semantics authorities and generated projections were already dirty.

## Remaining obligations

[T-status and next dependencies](t-status.md) records every T item at its exact reach.
T1/T2 were already landed by Claude. This tranche closes the new local store-frame,
work-selection, straight-composition and successful-preparation obligations, plus authoring
laws; it does not close another full T item. In particular, accepted reserved `badName`
failures contradict a blanket admission-to-typed-exit assertion. The retained
[t4 audit](../2026-10-03-session-work/t4-audit.lean) establishes that mismatch without changing
runtime admission or weakening the typed-exit judgment.
