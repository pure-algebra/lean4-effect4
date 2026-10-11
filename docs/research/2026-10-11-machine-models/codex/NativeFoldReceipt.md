# Native code weights use one generated fold

The response-dependent stack credit stays a context fold.
A fixed sum over saved frames cannot express its checked zero and one cases.
This slice replaces two recursive current-code traversals with instances of one generated fold.
It does not close `Atomic.Cleanup.log_debits`.

## Placement

- Concept: scope-lifetime-finalization, requirement R11.
- Proof role: preservation helper for the existing source-opportunity and cleanup accounting claims.
- Consumers: `Workers.Assertions.registrations_step` through `SourceOpportunityHistory`, and the open `Atomic.Cleanup.log_debits` through `Atomic.WriterMachine`.
- Reach: every native `Prim` value, with arbitrary selected source address or cleanup identifier.
- Evidence: universal agreement proofs, narrow consumer builds and axiom audits.
- Limit: these fold agreements establish no command preservation, progress or cleanup history bound.
- Dependency: the instances preserve the existing accounting projections on the M6 invariant path.

## Base and integration

Base: `4bc3efc44`, branch `codex/symbolic-native-fold`.
The commit containing this receipt is the slice head.
The preserved Atomic work remains in the separate `codex/symbolic-programs` worktree at `c55d70ba9`.

The coordinator adds these root imports:

- `Effect4.Machine.Fold` in `src/Effect4.lean`, beside the machine syntax imports.
- `Effect4.Laws.Machine.PrimWeights` in `src/Effect4/Laws.lean`, beside `FrameWeights`.

The coordinator may add the `PrimFold` group to `docs/GENERATED.md`.
The manifest and Makefile already name its exact output path.
No lakefile, root import or decisions register changes belong to this slice.

## Changes

`tools/Effect4Gen/Fold.lean` emits the declared parameter telescope for a plain, unindexed family.
It rejects mutual blocks and nested recursive positions on this route.
The route emits an algebra, fold, constructor equations, uniqueness and identity.
It emits no unused monadic or path fold.
`tools/Effect4Gen/manifest.json` adds `PrimFold`.
`Makefile` lists `src/Effect4/Machine/Fold.lean` among the derived outputs.

`Effect4.Machine.PrimWeights` supplies one consumed table of native leaf weights.
`SourceOpportunities.current` and `Atomic.WriterPhase.current` instantiate that table.
Their existing proof consumers unfold the generated fold instead of the removed traversal.
The saved-frame head tables retain their meanings.
The existing source and writer machine sums remain outside this slice.

Changed source modules:

- `Effect4.Laws.Machine.PrimWeights` and `Effect4.Machine.Fold`.
- `Effect4.Laws.Program.SourceOpportunities`.
- `SourceOpportunityActions`, `SourceOpportunityCallbacks`, `SourceOpportunityEvaluation` and `SourceOpportunityExecution` in that program laws directory.
- `SourceOpportunityFrames`, `SourceOpportunityMachine`, `SourceOpportunityNative` and `SourceOpportunityPrimitive` in that program laws directory.
- `Atomic.WriterPhase`, `WriterSource`, `WriterCallbacks` and `WriterSuspensions` under `Test/Dogfood/Scenario/Atomic`.
- `WriterLoops`, `WriterFrames` and `WriterEvaluation` in the same directory.

The retained readers are `StackCreditContext.lean`, `NativeFoldAgreement.lean` and `NativeFoldAudit.lean` beside this receipt.
The agreement reader retains the old traversals only to compare them with the new instances.

## Checks

All commands run in the slice worktree with `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Program.ReleaseCustody.Control effect4gen` | passed, 377 jobs |
| `python3 scripts/generate.py --only derived` | passed all requested producers in dependency order |
| `lake build Effect4.Laws.Program.SourceOpportunityHistory Test.Dogfood.Scenario.Atomic.WriterMachine` | passed, 1118 jobs |
| `lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/StackCreditContext.lean` | passed; audit 338 declarations, zero goals and zero modulo goals |
| `lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/NativeFoldAgreement.lean` | passed; audit 668 declarations, zero goals and zero modulo goals |
| `lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/NativeFoldAudit.lean` | passed; audit 1992 declarations, zero goals and zero modulo goals |
| `git diff --check` | passed |

Every audit stays within `[propext, Quot.sound]`.
The changed-module audit covers all 18 changed library and scenario modules.
A byte comparison against the base checks all 33 pre-existing manifest outputs; none changes.
The new generated file has 258 lines, and the consumed table has 42 lines.
No executable machine definition changes, so this slice owes no behaviour sweep.

## Consolidation count and open work

The two removed recursive declarations contain 21 lines.
The changed proof files remove 115 lines and add 133 lines.
Including the new table, the proof files change from 3745 to 3805 lines.
This foundational slice adds 60 net proof lines; it does not claim a net line reduction.
The shared generated fold is additional generator infrastructure.
No private command or evaluator census is added.

`Control.stackCredits` still reads the active response and changes that context under a saved constant continuation.
`StackCreditContext` checks matching registration zero, unmatched active response one, and the constant continuation case.
These are synthetic structural controls, not admitted-history proofs.

`Atomic.Cleanup.log_debits`, the full writer command composition and shared current-code ledger remain open.
The existing StackLedger cannot express active-code weights without the approved extension or R2 work.
No new scenario premise, planned goal or program representation enters this slice.
No push occurs.
