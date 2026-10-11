# Shared accounting over the existing places

The new ledger replaces installation and settlement arithmetic in two existing consumers.
It does not prove their local evaluator debit or the original history goals.

Proof role: accounting composition and exact connectors.
Evidence status: narrow build, direct consumer build, statement comparison, and trust audit pass.
Scope: existing fibers, races, store, pending commands, detached tasks, and trace events.

## Placement

Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Questions: the original Workers and QueueWorkers log bounds and `Atomic.Cleanup.log_debits`.
`ReleaseCustody.install_funded`, `ReleaseCustody.settle_funded`, and `WriterMachine.settle_debit` consume the shared laws.
Each instance still supplies source permissions and its actual local debit.
The laws establish no progress, acquired-value identity, cleanup order, or outside-host agreement.

## Model and replacement

`PlaceLedger` holds observation functions on existing machine data.
It introduces no executable state or stored program representation.
Its balance composes consumed events, outstanding weight, produced events, and an initial allowance.
The pending suffix and detached task snapshot remain explicit.

The local debit excludes the acting stored row and counts its returned row once.
Installation uses `FiberSum.split` and `FiberSum.install_le`.
Settlement uses the existing fiber, field, and command bounds.
No command, evaluator, or settlement case analysis is added.

Exact connectors read the saved-stack, release-custody, source-opportunity, and Atomic writer bounds.
The two old release theorem statements and twelve old Atomic theorem statements remain unchanged.
The replaced proof bodies are removed in this slice.
The remaining ledger-specific evaluation, edit, and history producers stay open.

## Acceptance

Base: `9643905ab44ce058318c937fa16b4ac9d33ede67`.
Code head: `6eeb6b5c01f0bad8ca42d7d9f9745130c20c20ea`.
The source hashes and line counts are retained beside this receipt.
The acceptance build passes 1169 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeAccounting Test.Dogfood.Scenario.Atomic.WriterMachine
```

The module audit passes:

```sh
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/PlaceLedgerAudit.lean
```

The retained `Audit.lean` contains that audit's exact source.
Its output is:

```text
#axiom_audit: 107 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

`git diff --check` passes before the code commit.
The retained header comparison finds fourteen unchanged old theorem statements.
The initial private probe checks the four readings; the production build checks the final installation certificate.

## Changed paths and measured size

| Path | Lines before | Lines after |
| --- | ---: | ---: |
| `src/Effect4/Laws/Machine/PlaceLedger.lean` | 0 | 157 |
| `src/Effect4/Laws/Program/PlaceLedgerConnect.lean` | 0 | 72 |
| `src/Effect4/Laws/Program/ReleaseCustody/IterationDebit.lean` | 73 | 67 |
| `Test/Dogfood/Scenario/Atomic/WriterMachine.lean` | 203 | 232 |
| `src/Effect4/Laws.lean` | 347 | 348 |

The code adds shared definitions and connectors; its total line count increases.
Release custody removes six lines; Atomic adds twenty-nine lines, including its ledger instance and exact connector.
The two new shared modules contain 229 lines.
The initial probe and plan are retained beside this receipt.
All nine remaining underlying application and call-tree goals remain open.

No executable code changes, so this slice reaches no behavior comparison.
The earlier R2 and future context changes still owe their planned behavior sweep.
