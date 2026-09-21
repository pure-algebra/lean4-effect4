# Foundations slice 1 receipt

Merge note: the only seven changed Effect4 obligation propositions are the seven authorized
premise amendments below. Every other obligation keeps its proposition. The four pre-existing
Pending argument reorderings are handled by checked evidence, not by statement edits.

Base: `3a1b456d`. Head: the commit carrying this receipt on `codex/foundations-slices`.
Worktree: `/private/tmp/effect4-foundations-slices`. Nothing pushed. The original checkout is
unchanged. The attached objective authorizes slices 1 and 2 of the 2026-09-20 foundations plan;
this commit is slice 1 only. No owner decision register or retained baseline changed.

## Migration and statement audit

The source inventory found 329 declarations in 40 files, rather than the plan's older 245.
Twenty are test fixtures; 309 belong to Effect4. `migration-inventory.tsv` names every source
and `migrate-obligations.py` records the mechanical def-to-theorem pass. Existing neighbouring
law omissions were copied where theorem elaboration otherwise adds unused instances. Two
additional DecidableEq omissions on `Api.M1Origin.spawn_origins` and `start_origins` keep the
old propositions; their laws are outside that instance section. No law proof was weakened.

The pre-edit audit (`StatementAudit.lean`, `statements-before-final.log`) paired 268 of the
309 obligations against namesakes or explicit backing names. It found the seven missing-premise
statements and four reordered Pending statements. All four had equal binder counts but a
different binder order: `beginRace_pendingOk`, `fork_pendingOk`, `forkIn_pendingOk`,
`forkScoped_pendingOk`. The former already has searched evidence; the latter three now have
explicit lambda adapters. Full quantifiers inside `Obligation` are included in these counts.

`AllStatements.lean` prints every extracted Effect4 proposition, with explicit arguments and
universes. The before dump uses the untouched base checkout; the after dump uses this worktree.
`compare-statements.py` requires the same 309 names and exactly the seven approved differences.
`FinalAudit.lean` runs `#obligation_audit Effect4`, validates the unique declaration-backed
ledger without rerunning search, and prints the axioms of all 32 explicit references.

## Authorized amendments

All names below are under `Effect4.Program.Sched.M1Origin`. Counts cover the entire proposition.

| Obligation | Old / new binders | Restored premise and evidence |
| --- | --- | --- |
| `actionAt_fork` | 6 / 8 | action and source-location `h`; the stronger old statement also had the plan's proof probe |
| `actionAt_forkIn` | 7 / 9 | action and source-location `h`; same |
| `actionAt_not_forkScoped` | 6 / 8 | action and source-location `h`; same |
| `actionAt_raceAll` | 6 / 7 | source-location `h`; old statement refuted by E4-SCHED-CE-004 |
| `fork_rel` | 15 / 18 | `MachineOk`, `BMeans`, `FMeans`; old statement refuted by E4-SCHED-CE-005 |
| `forkIn_rel` | 16 / 19 | `MachineOk`, `BMeans`, `FMeans`; same |
| `raceAll_rel` | 11 / 14 | `MachineOk`, `BMeans`, `FMeans`; same |

The permanent counterexample battery is
`Test/Counterexamples/Machine/Semantics/ActionAtRaceAllPremise.lean`, imported by `Test.All`.
The race counterexample uses a source race and an unrelated action. The three Actions
counterexamples use unrelated machines with different allocation counters, and retain valid
program and answer relations. Each contradiction is kernel-checked, not a finite search
reported as a universal preservation theorem. The race proof uses `[propext]`; the other three
use `[propext, Quot.sound]`. Their register rows preserve the old false claims explicitly.

## Checked references

These 32 entries had live markers before this change; each marker is removed in the same
source edit as its reference. Ordinary applications and the three Pending adapters elaborate
against the exact extracted proposition. The axiom ceiling is unchanged.

| Obligation | Checked term |
| --- | --- |
| `Effect4.Program.Sched.M1Origin.actionAt_fork` | `@Effect4.Program.Sched.actionAt_fork` |
| `Effect4.Program.Sched.M1Origin.actionAt_forkIn` | `@Effect4.Program.Sched.actionAt_forkIn` |
| `Effect4.Program.Sched.M1Origin.actionAt_not_forkScoped` | `@Effect4.Program.Sched.actionAt_not_forkScoped` |
| `Effect4.Program.Sched.M1Origin.actionAt_raceAll` | `@Effect4.Program.Sched.actionAt_raceAll` |
| `Effect4.Program.Sched.M1Actions.scopeLinkFiber_ok` | `@Effect4.Program.Sched.scopeLinkFiber_ok` |
| `Effect4.Program.Sched.M1Origin.fork_rel` | `@Effect4.Program.Sched.fork_rel` |
| `Effect4.Program.Sched.M1Origin.forkIn_rel` | `@Effect4.Program.Sched.forkIn_rel` |
| `Effect4.Program.Sched.M1Origin.raceAll_rel` | `@Effect4.Program.Sched.raceAll_rel` |
| `Effect4.Machine.M1Clock.book_advanceState` | `@Effect4.Machine.book_advanceState` |
| `Effect4.Program.Sched.M1Drive.dropFinalizer_ok` | `@Effect4.Program.Sched.dropFinalizer_ok` |
| `Effect4.Program.Sched.M1Deliver.storesOk_closeScopeUnsafe` | `@Effect4.Program.Sched.storesOk_closeScopeUnsafe` |
| `Effect4.Program.Typed.WorldWanted.memoBuild_extension` | `@Effect4.Program.Typed.memoBuild_extension` |
| `Effect4.Program.Typed.M2ForkSourceWanted.source_fork_extension` | `@Effect4.Program.Typed.M2ForkSourceWanted.fork_source_extension` |
| `Effect4.Api.M1Trace.fork_forked` | `@Effect4.Api.fork_forked` |
| `Effect4.Api.M1Trace.forkScoped_forked` | `@Effect4.Api.forkScoped_forked` |
| `Effect4.Api.M1Trace.forkFinalizers_forked` | `@Effect4.Api.forkFinalizers_forked` |
| `Effect4.Api.M1Trace.supervision_static` | `@Effect4.Api.TraceFacts.supervision_static_flags` |
| `Effect4.Api.M1Origin.supervision_static` | `@Effect4.Api.supervision_static_origins` |
| `Effect4.Api.M1Origin.source_fork` | `@Effect4.Api.source_fork_holds` |
| `Effect4.Api.M1Origin.race_launch_origins` | `@Effect4.Api.race_launch_origins_holds` |
| `Effect4.Machine.M1Origin.spawnChild_keys_subset` | `@Effect4.Machine.spawnChild_keys_subset` |
| `Effect4.Machine.M1Origin.spawn_minted` | `@Effect4.Machine.spawn_minted` |
| `Effect4.Machine.M1Origin.fork_arm_minted` | `@Effect4.Machine.fork_arm_minted` |
| `Effect4.Machine.M1Origin.withFiber_fork_minted` | `@Effect4.Machine.withFiber_fork_minted` |
| `Effect4.Machine.M1.Handles.register_keys` | `@Effect4.Machine.DeferredStore.register_keys` |
| `Effect4.Machine.M1.Handles.complete_keys` | `@Effect4.Machine.DeferredStore.complete_keys` |
| `Effect4.Machine.M1.Handles.drainDue_keys` | `@Effect4.Machine.DeferredStore.drainDue_keys` |
| `Effect4.Machine.M1.Handles.setCell_keys_of_subset` | `@Effect4.Machine.DeferredStore.setCell_keys_of_subset` |
| `Effect4.Machine.M1.Handles.setCell_appendDue_keys` | `@Effect4.Machine.DeferredStore.setCell_appendDue_keys` |
| `Effect4.Program.Sched.M1PendingOrigin.fork_pendingOk` | `fun i m f y hf program options site a ha => @Effect4.Program.Sched.fork_pendingOk i m f y hf program options a ha site` |
| `Effect4.Program.Sched.M1PendingOrigin.forkIn_pendingOk` | `fun i m f y hf program options scope site a ha => @Effect4.Program.Sched.forkIn_pendingOk i m f y hf program options scope a ha site` |
| `Effect4.Program.Sched.M1PendingOrigin.forkScoped_pendingOk` | `fun i m f y hf program options site a ha => @Effect4.Program.Sched.forkScoped_pendingOk i m f y hf program options a ha site` |

## Tool controls and validation

The ledger refuses old-style obligation definitions, wrong propositions, wrong existing
checked declarations, disallowed axioms, missing evidence, and stale markers. Direct
references work when the supplied search fails; repeated checking validates the existing
proof. The include-hypothesis fixture checks the full binder count. A theorem-form obligation
can itself be referenced at its own marker proposition, without pretending that its empty
marker proves the proposition it records. Namesake discovery is only an audit and never
publishes evidence by matching a name.

Commands (all with exit 0 in the final retained evidence):

- `lake build ProofGraph Effect4.Laws.Auto.Obligations Test.Audit.ProofGraph Test.Audit.ProofGraphSearch Test.Audit.Obligations` (`tooling-final.log`).
- Each touched law module was built during the migration. The last corrections to unused
  instances in `Api.Supervision` were rebuilt by `make check`.
- `make build` (`make-build.log`); `make check` (`make-check.log`) repeats the final build,
  fresh root elaboration, and hermetic generated-file drift checks.
- `lake env lean -DwarningAsError=true .../AllStatements.lean` before and after;
  `python3 .../compare-statements.py` (`statement-diff.log`).
- `lake env lean -DwarningAsError=true .../FinalAudit.lean` (`final-audit.log`).
- `git diff --check`.

The failed intermediate migration builds were diagnosis, not verification; only final
passing logs are retained in this commit. `make check-full` and the host oracles are outside
this slice's requested checks. No runtime or generated bytes changed.

## Result and remaining work

The declaration-backed counts, open names and final audit summary are recorded below.
Slice 2 remains the owner-row and typed-stack interface change. The existing open obligations
are not silently declared proved, and no claim of runtime coverage or whole-machine typed
preservation is made by this tooling migration.

```text
Effect4: 237 paired, 72 without a namesake, 0 mismatches
OPEN Effect4.Api.M1Origin.source_fork_site
OPEN Effect4.Api.TraceFacts.M1Trace.step_agrees
OPEN Effect4.Program.Guard.M4Handshake.parkHandshake_reachable
OPEN Effect4.Api.TraceFacts.M1Trace.reachable_agrees
OPEN Effect4.Api.M1Origin.source_two_race_sites
OPEN Effect4.Api.M1Origin.source_forkScoped_site
OPEN Effect4.Api.M1Origin.source_race_site
OPEN Effect4.Api.M1Origin.source_forkIn_site
OPEN Effect4.Run.M1Trace.observe_replace_trace
UNIQUE LEDGER: 309 total; 300 proved; 9 open
```

The final build audited 470 modules and 66,414 declarations. Semantic/test axioms remain
`[propext, Quot.sound]`; the existing exact implementation boundary permits
`Classical.choice` in 14 named modules and 29 named declarations. This boundary was not edited.

Retained build logs remove line-ending whitespace only; the local `.raw.log` files retain
the command output verbatim. This normalization changes no diagnostics or results.
