# Fiber sum instance receipt

The newer foundation needs three interruption-helper unfold repairs after this slice merges.
The coordinator applies them in `SourceOpportunityNative`; this slice retains its checked base.

## Placement

Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Question: source-use and cleanup accounting install the acting fiber once and retain the other fibers' weights.
Consumers: source-opportunity history, release-custody history, Workers releases and Atomic cleanup writer accounting.

`FiberSum.install_le` supplies the absent-owner installation bound from the existing keyed-list law.
It retains distinct identities and the returned fiber's actual identity.
It neither requires an old lookup nor creates a new case analysis.
The source installation and shared writer settlement consume it.

Twelve existing proofs now consume `FiberSum` laws:

- Source opportunities: `outside_split`, `outside_update`, `update_debit`, `step_frame_install_debit`, `outside_update_le`, `install_le`.
- Shared writer weights: `settle_bound`.
- Atomic writer: `settle_debit`.
- Release custody: `outside_split`, `outside_update`, `outside_update_le`, `outside_install`.

The member-based source update derives its existing lookup with `fiber_lookup_of_mem_nodup`.
It adds no second membership or lookup carrier.
The existing `FiberSumConnect` equations continue to compile at the unchanged family definitions.

Reach: each theorem retains its exact old source, model, lookup, membership, distinct-id and local-weight premises.
Every old theorem name and statement remains unchanged.
The seven modules contain 77 old theorem headers; a text comparison confirms each header remains identical.
No executable definition changes.

Limit: the slice does not establish any local writer debit or source relation that its callers assume.
It removes repeated row-sum proof bodies, with no new evaluator or command pass.
The existing evaluator and settlement case analyses remain unchanged.
The host boundary remains unchanged.

## Commits and files

Coordinator merge base: `b81664fd8`, merging `0a41c816e` into the clean checked branch.
Proof head: `c2fb064b5`.

| File | Before | After |
| --- | --- | --- |
| `Laws/Machine/FiberSum.lean` | 144 | 152 |
| `Laws/Machine/WriterWeights.lean` | 184 | 184 |
| `Laws/Program/SourceOpportunityMachine.lean` | 348 | 342 |
| `Laws/Program/SourceOpportunityNative.lean` | 463 | 464 |
| `Laws/Program/SourceOpportunityExecution.lean` | 150 | 149 |
| `Laws/Program/ReleaseCustody/Outside.lean` | 69 | 64 |
| `Test/Dogfood/Scenario/Atomic/WriterMachine.lean` | 204 | 203 |
| Total | 1,562 | 1,558 |

Library paths start under `src/Effect4/`.
The diff adds 42 lines and removes 46 lines.
Twelve direct shared sum-law applications replace the repeated family proof bodies.
The new shared helper adds eight lines.

## Verification

Commands run with one Lake process per worktree:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.FiberSumConnect Effect4.Laws.Program.SourceOpportunityExecution Test.Dogfood.Scenario.Atomic.WriterMachine
Build completed successfully (1130 jobs).

LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.SourceOpportunityHistory Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers.Assertions Test.Dogfood.Scenario.Atomic.Cleanup Test.Dogfood.Scenario.Timeout
Build completed successfully (1239 jobs).

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/fiber-sum-instance-audit.lean
#axiom_audit: 382 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

git diff --check
No findings.
```

The first narrow build exposes two unchanged-field normalization obligations in release custody.
The repaired build above compiles every changed module and the existing sum connectors.
The second build checks the actual history and application consumers, including the original Timeout module.
The retained `FiberSumInstancesAudit.lean` imports and audits all seven changed modules.
Its exact output is retained in `FiberSumInstancesAudit.log`.
The final audit runs after the builds finish.

This proof-only slice reaches no changed executable or outside comparison input.
It owes no additional behavior gate.
The newer core foundation and its full Laws build remain the coordinator's separate slice.

## Remaining numeric history

`Timeout.stale_never_applies` remains proved.
`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain open.
Source opportunities still require their stated loop and race restrictions.
This consolidation does not apply those restrictions to the Timeout producer.
The numeric producer still needs actual source, store, cursor and loser-cleanup coupling.
The settled declared-failure retry ruling remains unchanged.
