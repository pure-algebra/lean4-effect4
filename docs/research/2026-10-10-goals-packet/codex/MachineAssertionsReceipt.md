# Workers assertions receipt

The workers assertion assembly compiles with three planned preservation goals.
It does not prove the original cleanup claim without those goals.
The coordinator must replace the original goal body with the checked assembly consumer.

Base: `b74ebab6f`.
Dependencies: command rules `c5c7cf921`, run frame `a70ea309`.
The frame appears here as cherry-pick `592a12bf6`.
Neutral source extraction: `c92d43b1`.
The head is the commit containing this receipt.

## Placement

Concept: scope-lifetime-finalization.
Required property: R11, at most once per registration, counted by identity.
Question: `Test.Dogfood.Scenario.Workers.releases_once`, consumed by the workers claim.
Reach: the actual built crew, every total, compile budget and admitted session history.
Bounds: decisions row 254, including raw controls, cuts, forced yields and session-preflight host answers.
Limits: no progress, release order, another program or host execution is established.
Unlock: the original scenario observation follows by reading the concrete assertions.
Each helper's module docstring states its role and consumer.

## Files

`Workers.Program` holds the unchanged source declarations, without the scenario's planned goals.
`Workers.Assertions` holds concrete acquisition-path trace counts and second-cell write counts.
`Holds` retains the existing `Run.HistoryOf` and the three concrete assertions.
It defines no separate run representation.
`load`, `history_step` and `read` are proved without a planned goal.
`middleware_step` proves the flag edit leaf and is consumed by `step`.
`step` and `history` use the three planned goals for the remaining decisions.
`MachineAssertions.lean` checks the actual universal scenario observation consumer.
The coordinator inserts that body at the original theorem, avoiding a second library claim.

## Commands

All commands use `LEAN_NUM_THREADS=3` in the managed worktree.

| Command | Result |
| --- | --- |
| `lake build Test.Dogfood.Scenario.Workers` | exit 0, 1026 jobs after neutral extraction |
| `lake env lean /private/tmp/MachineProgramAudit.lean` | exit 0, three source declarations within the ceiling |
| `lake build Test.Dogfood.Scenario.Workers.Assertions` | exit 0, 1024 jobs |
| `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAssertions.lean` | exit 0, reader and audit |

```text
#axiom_audit: 30 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 3 planned goals
```

`MachineAssertions.out` retains the measured plan and its exact goal statements.

## Remaining proof work

`registrations_step` needs source placement plus dynamic source-use accounting.
`releases_step` needs scope-entry ownership and control-use accounting.
`logs_step` needs the second cell's writer census and each acquisition's captured value.
`HistoryOf` records actual execution; it does not itself supply these safety facts.
`Typed.CaptureTyped` already carries exact acquisition-source identity and typed captures.
The residual-source proof should reuse this judgment and the existing machine lift.
`Book.MachineOk` carries pending interruption and store assertions, without source-use accounting.
`Handles` supplies handle membership, without the writer census or captured-value identity.

The source modules change no machine behavior.
The new `Test` modules need the coordinator's `Test/All.lean` integration.
Behavior gates remain deferred until the major structure lands.
No push.

## Certified source follow-up

`Holds.sites` now consumes the universal acquisition-node facts from `Programs.workers_acquisition_sites`.
`Holds.placement` consumes `Programs.crew_acquire_once_placed`.
The paths alias `Programs.crewAcquire`, so the assertions introduce no parallel path table.
`yield_step` proves the yield-override edit and the step assembly consumes it.
The shared classifiers live in `Effect4.Laws.Program.ReleaseTrace`, consumed by both crews.
The classifier-only audit reports eleven declarations within the ceiling, without goals.

Dependencies: `b67e9b9c`, `3a7b059c`, `7719b68b` from the symbolic-programs seat.
`lake build Test.Dogfood.Scenario.Workers.Assertions` succeeds, 1034 jobs.
The updated universal reader succeeds with this measured audit:

```text
#axiom_audit: 46 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 3 planned goals
```

The generic release debit remains open, even without the per-source once bound.
`Scope.closeState_finalizers` empties the store's registration list before finalizer code runs.
`scopeCloseSnapshot` transfers its close order into residual store-generated programs.
A successful `scopeAdd` also leaves the release name in `afterScopeAdd` until delivery.
Counting both occurrences as live credits would double count one registration.
The custody proof must distinguish the returned unit from an already-closed scope's closing exit.
It must track residual finalizer code, stacks and commands as well as scope entries.
The existing scope-store laws alone prove no trace-event debit inequality.
The typed capstones apply to the reference machine and ghost admission.
Their observation transfer supplies no native residual-source theorem at the crew's actual host table.
