# Seams implementation receipts

K0 lands from `c752e565b4e1afac95d1258b0a4a570b81bcdf81` on `codex/seams`.
The remaining slices are open. This receipt claims no completed goal.
The coordinator merges; this branch is never pushed.

| Slice | Implementation commit | Receipt | State |
| --- | --- | --- | --- |
| K0 | `66f292a095e57e7c94586434aab9c5c597f82d6e` | [K0](K0.md) | Required checks pass. |
| S0 | Pending | Pending | Open |
| V1 | Pending | Pending | Open |
| S1 | Pending | Pending | Open |
| S2 | Pending | Pending | Open |
| S4 | Pending | Pending | Open |
| S3a | Pending | Pending | Open |
| S3b | Pending | Pending | Open |
| ST1a | Pending | Pending | Open |
| ST1b | Pending | Pending | Open |
| ST2 | Pending | Pending | Open |
| ST3 | Pending | Pending | Open |
| ST4 | Pending | Pending | Open |
| S6 | Pending | Pending | Open |

## Departures from the plan

| Slice | Correction and control |
| --- | --- |
| K0 | The shared launcher admits two slots and resets the thread count. An outer lock serializes this goal; the command overrides the count. |
| K0 | Split generated constructor headers need a reader repair. Current generated-file controls retain the failing baseline. |
| K0 | Deleting Cascade exposes an implicit Store import in the evaluator proof. The explicit import restores its unchanged proof. |
| K0 | `generate.py` has no semantics family. `make gen-semantics` owns that report. |
| K0 | The reader tool's String and JSON operations exceed the library proof ceiling at baseline. Library and fixture audits keep the required ceiling. |
| K0 | The native compile script names the deleted numeric interface. Removing that input repairs its retained failing command. |
| K0 | Pending nursery allocations distort immediate counters. Flushed readings pass a known-list calibration; earlier measurements are superseded. |

## Proposed decisions rows

| Slice | Proposed text |
| --- | --- |
| K0 | Update `E4-CAS-CE-006` to resident node identity. Keep both own-address lookup premises and equal addresses; retain the arbitrary-content collision alternative. |

The individual receipts retain commands, exit statuses, audit output, red controls, and evidence limits.
