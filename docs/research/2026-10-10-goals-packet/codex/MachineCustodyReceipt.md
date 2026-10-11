# Release custody command receipt

The local custody transfers and actual release command compile without planned goals.
The whole-configuration available-credit premise remains open.
The coordinator must keep that premise visible when integrating the command consumer.

Base: `b74ebab6f`.
Dependencies: `c5c7cf921`, `cde1c0e0`, `788266a7`.
The head is the commit containing this receipt.

## Placement

Concept: scope-lifetime-finalization.
Property: R11, at most once per registration counted by identity.
Question: helpers of `Workers.Assertions.releases_step` and the queue release debit claim.
Reach: actual native scope-add and release-start commands, source-indexed foreign captures and arbitrary selected fibers.
Fresh open registration requires a fresh key.
The loop rule requires the selected fiber, no pending interrupt, no override and available operation budget.
Limits: no whole-machine custody preservation, source-use uniqueness, progress or host execution is established.
Unlock: the release debit goal can consume checked scope transfers and the exact counted command rule.

## Changes

`ReleaseCustody` tracks credits in scope entries, close orders and registration responses.
Open registration moves its credit into the scope entry.
Closed registration keeps its credit in the closing-exit response.
Closing empties the entry and transfers its credits into the close order.
The sequential head takes one credit and retains the tail credits.
Actual native continuation delivery follows the unit and closing-exit alternatives.
Actual release-start evaluation pushes the source-identified frame and increments its trace count exactly once.
Its registration count stays unchanged.
`release_loop_debit` consumes an available credit at the actual machine command boundary.
`Workers.Assertions.release_command` applies that rule to both real acquisition paths.
It supplies no proof of the available-credit premise.

The rule uses each capture's actual source identity.
It assumes no uniform environment length for generator points.
The state-transfer clause concerns the selected entry.
It claims no global store total when duplicate scope keys exist.

## Verification

All commands use `LEAN_NUM_THREADS=3` in the managed worktree.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Program.ReleaseCustody Test.Dogfood.Scenario.Workers.Assertions` | exit 0, 1037 jobs |
| `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCustody.lean` | exit 0 |
| `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` | exit 0 |

```text
#axiom_audit: 45 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

`MachineCustody.out` retains the exact audit output.
`MachineAssertions.out` retains the universal observation consumer and its open goals.
The latter remains modulo the three existing preservation goals.

## Remaining work

The custody assertion must include every fiber, pending command and residual close chain.
It must distinguish the scope-add response before counting the continuation's credit.
Counting every stored foreign name duplicates credits.
`Machine.Lift` supplies the existing command and admitted-history assembly.
The remaining assertion must use that assembly and account for raw controls and fuel cuts.
No original scenario goal changes in this slice.
No machine behavior changes.
Behavior gates remain deferred by the coordinator until the major structures land.
No push.
