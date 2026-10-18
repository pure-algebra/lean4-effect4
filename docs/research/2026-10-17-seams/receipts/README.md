# Seams implementation receipts

K0 lands from `c752e565b4e1afac95d1258b0a4a570b81bcdf81` on `codex/seams`.
The remaining slices are open. This receipt claims no completed goal.
The coordinator merges; this branch is never pushed.

| Slice | Implementation commit | Receipt | State |
| --- | --- | --- | --- |
| K0 | `66f292a095e57e7c94586434aab9c5c597f82d6e`; receipt `faa7d0122bd550186e4c622517509ac001763a35` | [K0](K0.md) | Required checks pass. |
| S0 | `d46b1e6d6f184764a7ee1a00b01a800a45f35d33` | [S0](S0.md) | Required checks pass. |
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
| S0 | The certified checker packages land in S0 to test the actual sealed boundary; V1 retains decomposition and caller migration. |
| S0 | A generated annotation leaf reader removes a dependent-child lowering refusal; its connector proves the exact ordered annotation sequence. |
| S0 | Source nominal ascriptions recover erased package types. A concrete verdict accessor replaces the refused generic mono root. |
| S0 | The stable step recomputes its source interpreter and ignores the adapter's former argument; mismatched-interpreter controls bound this change. |
| S0 | Fresh typed trees determine interfaces; final duplicate bindings win. Stale-interface and hostile-alias clients retain their refusals. |
| S0 | Explicit roots include observed inherited instance operations and Todo callers. The kit renderer now matches real kinds. |
| S0 | Generated warnings 30 and 32 are suppressed; warning 55 remains an error. The hidden-helper refusal is retained. |
| S0 | Todo placeholders remain outside the tested Live/start/restore closure, which contains no unknown type or placeholder. |
| S0 | Output alias checks cover all generated extensions and cross-artifact aliases before publication or comparison. |
| S0 | The report explicitly imports Check for its new claim. Its retained first attempt refuses the unloaded pointer. |

## Proposed decisions rows

| Slice | Proposed text |
| --- | --- |
| K0 | Update `E4-CAS-CE-006` to resident node identity. Keep both own-address lookup premises and equal addresses; retain the arbitrary-content collision alternative. |
| S0 | Adopt typed-tree interface inference, explicit roots, source nominal ascriptions, and whole-package sealing for this generated family. |
| S0 | Record the exact annotation connector and the stable closed step; retain interpreter recomputation as an unmeasured cost. |

The individual receipts retain commands, exit statuses, audit output, red controls, and evidence limits.
