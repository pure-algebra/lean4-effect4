# R2 release-accounting adapters

The five accounting modules pass their narrow build and axiom audit.
The machine change still requires the full law build before a commit.

Base: `b4dcef4f12c7ae6eeda97c6c9937596bdc42b61f`.
Status: checked source in the integration worktree; uncommitted.

## Placement

Concept: scope-lifetime-finalization, R11, serving `ReleaseCustody.Execution.history` and the original Workers release claim.
The existing accounting predicates measure scope, race, fiber, dispatcher, and queued-command credits.
The canonical countdown and scope-link plans use shared edit paths.
Their eager adapters apply `FiberSum.fiberEdits_le` after those plans.
Interruption spends fiber credit; observer metadata contributes no credit.
The scope-link command proof removes its private helper case analysis.
The original public theorem statements retain their hypotheses and conclusions.
These bounds establish no progress, host agreement, or application history by themselves.

## Checked modules

- `src/Effect4/Laws/Program/ReleaseCustody/CommandDebit.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/CommandRaceDebit.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/CommandStoreDebit.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/NativeActionDebit.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/NativeParkDebit.lean`

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.CommandSequencing Effect4.Laws.Program.ReleaseCustody.LoopCommand` passes, with 592 jobs.
The shared eliminator module resolves the generated auxiliary declaration collision.
The log is `/private/tmp/r2-command-sequencing-4.log`.

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.AdministrativeKept Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue` passes, with 602 jobs.
Both observer wrappers consume the shared producer path.
The log is `/private/tmp/r2-administrative-2.log`.
The full law build remains the integration acceptance check.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/R2ReleaseAccountingAudit.lean` passes.
The retained audit reports 376 declarations within `[propext, Quot.sound]`, zero modulo declarations, and zero planned goals.
The retained source and output are `R2ReleaseAccountingAudit.lean` and `R2ReleaseAccountingAudit.out` beside this receipt.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/R2QueueRawControls.lean` passes.
Its controls retain the raw missing-owner tail failure and the idle-target current-code change.
These controls are checked Lean examples, not outside-runtime comparisons.

## Remaining work

The combined queue proof and observer instances pass their builds.
The full law build and the integration audit remain open.
The executable machine change owes the reached behavior gates at the sweep.
The original application goals remain open until their history producers compose.

## Joint integration

The later full law build and landing audit pass.
`r2-integration-receipt.md` records their commands, counts, and remaining Timeout adapter obligation.
