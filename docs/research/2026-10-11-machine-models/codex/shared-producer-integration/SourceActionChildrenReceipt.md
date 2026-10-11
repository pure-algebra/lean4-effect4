# Exact source children of native actions

The source producer retains exact child points without a second action or evaluator analysis.
It does not establish the Timeout numeric history.

Proof role: source provenance.
Evidence status: the actual consumer build, trust audit, and old-contract reader pass.
Scope: actual action answers at scoped source points.

## Placement

Concept: store-typing, R4, serving `HeapSites.heap_sites_keep`.
The source-instance consumer serves `Timeout.cleanup_keeps` and `Timeout.retries_declared`, under R11 and R10.
The old source-fragment premise stays on the old scope projection.
The stronger producer retains the actual child node, scope, represented program, and captured point.
It supplies no active-generation permission, progress, or outside runtime agreement.
`At` retains lexical scope and length.
The numeric instance separately owns the actual captured values and active-generation permission.

## Change

The changed source is `src/Effect4/Laws/Program/NativeActionScope.lean`.
The old action predicate becomes the scope instance of `ActionProgramsAt`.
`SourceProgramAt` names fork, mask, and entrant child roles.
Fork children use `[0,0]`; mask children use `[0]`.
Entrant children use `[0,0] ++ List.replicate index 1 ++ [0]`.
`childPoint_spec` retains the captured point fields and the actual fuel debit.
The sole entrant and source-action analyses move into `entrants_children` and `source_action_children`.
Their old declarations are projections of the stronger results.
`scoped_fork_children` supplies the same source witness for the actual scoped-fork answer.
`interp_source_children` supplies the stronger actual interpreter result.
The existing interpreter consumer uses that result before the old scope projection.
All seven old theorem headers remain byte-identical.
A constructor reader checks the old `ActionAt` meaning at every actual action constructor.

## Measurements

The source has 159 lines before and 291 lines after.
The measured producer build takes 176 seconds in this run.
This is a run measurement, without a controlled comparison to other coordinator builds.
There is one existing action analysis, moved rather than copied.
No executable code changes.

## Open work

`Timeout.stale_never_applies` is proved.
`Timeout.cleanup_keeps` and `Timeout.retries_declared` remain planned goals.
The full history must couple the retry cursor, active generation, captured references, and completed timeout outcome.
Retired generations retain cleanup-entry provenance, rather than an obsolete exact heap image.
That provenance must consume the actual source store operation.
Reference equality alone cannot issue it, because an executed operation can keep references equal.
The actual cancellation join produces the completed cleanup phase before the root publishes its form result.
The original fixed budgets remain explicit.

## Base and delivery

The worktree head is `125865d206dfedd3434d460010366f4fd136d84b`.
The reviewed root head is `fb3b0394c76310e6f62db23f5579d6139b0c04c2`.
The source baseline SHA256 is `e090af39ff5167175de260eb69d5c2d21be6c2587c8054fbd3ec843e48805529`.
The checked source SHA256 is `7f8e6c0ae374860848f97ab56648379c597092295a155ac17e1ebfd9d241d8a2`.
The one-file patch is `/private/tmp/source-action-children.patch`.
Its SHA256 is `54ab10a48cc60bbc2993616175622f37ec204615a8c1306832553ca03d5233e8`.
The source snapshot is `/private/tmp/NativeActionChildrenChecked.lean`.
Copied coordinator dependencies are excluded from that patch.
Their hashes are in `/private/tmp/source-action-children-dependency-hashes.tsv`.

## Verification

The private complete producer probe passes:

```sh
LEAN_NUM_THREADS=3 lake env lean /private/tmp/NativeActionChildrenProbe5.lean
```

The actual consumer build passes 1200 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHeapHistory Effect4.Laws.Program.ReleaseCustody.NativeActionDebit Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout
```

Its log is `/private/tmp/source-action-children-consumer-build-2.log`.
The first run compiles every numeric consumer, but fails three stale release dependency modules.
The corrected run uses exact checked coordinator bytes and passes.
No release proof repair enters this patch.

The audit and old-contract reader pass:

```sh
LEAN_NUM_THREADS=3 lake env lean /private/tmp/source-action-children-audit.lean
```

The exact audit output is:

```text
#axiom_audit: 446 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The audit log is `/private/tmp/source-action-children-audit.log`.
`git diff --check` passes for the changed source.
No runtime, program constructor, gate, root import, or scenario statement changes.
The slice reaches no new outside behaviour gate.
