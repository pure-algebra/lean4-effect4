# Review findings and landing order

## Reviewed baseline

The design note and probes are at `9fb3b66cd0c80fe26468e9bef143e993fd3bf3f8`.
The production-code commit at that baseline is `cd61d93378275c276a2c0206a8391b881b1f9864`.
The reviewed note is `docs/research/2026-10-10-schedule-independence/README.md`.

## Corrections before a production claim

### DET-OW-01: keep all premises of the abstract theorem

`RD.extends_all`, `RD.complete_unique`, and `RD.bounded` compile and pass the cycle-aware audit.
They require `Equivalence R`, `Bisim step R`, and `Diamond step R`.
The note's short premise list omits the first premise.
Keep all three in the production statement and handoff.

The one-step diamond is stronger than arbitrary convergence.
`PromiseControls.unequalLengths` reaches the same endpoint in two and three steps.
Thus equal results alone do not imply equal callback counts.

### DET-OW-02: raw fires are not the enabled relation

A raw fire on an absent owner can leave the finished machine unchanged.
`Controls.padded` appends nine such fires without changing `Machine.obs`.
Raw tape lengths therefore cannot satisfy the proposed bound.

Define the enabled-fire relation separately from raw input replay.
Keep its budget receipts.
`Controls.zeroStart` also demonstrates a live fuel frontier with no armed owner.
Do not turn that frontier into an RD normal form.

### DET-OW-03: no armed owner does not mean finished

The original `TapeProbe.explore` calls an unarmed, non-halted endpoint “complete”.
`Controls.promiseWait` reaches such an endpoint without finishing.
The cycle control does too.

Use `finished`, sufficiency receipts, and frontier classification separately.
`frontier_empty_iff_deadlocked` in `src/Effect4/Laws/Api/Frontier.lean` states the broader frontier test.
No-armed alone is not that test.

### DET-OW-04: observations include answers

The original probe renders the root exit and reference heap as diagnostic text.
It also combines all failures into one text label.
Those observations do not establish equality of `Machine.obs`.

The new probe compares every fiber exit and the entire store.
The returned-update control has equal final cells but different returned values.
The fragment therefore refuses shared updates that expose their intermediate answer.

### DET-OW-05: postpone a general name quotient

The earlier component comparison found different allocation counters under different schedules.
A different number of allocated tokens is not a permutation of the whole allocation history.
A wider relation may need correspondence of live names and unused-supply information.

`FiberAction.getId` also exposes a fiber ID as an ordinary natural value through `interpOf`.
Code can observe more than abstract handle identity if program admission accepts that operation.
A universal alpha-renaming argument must account for that observation.

The first fragment avoids these obligations by allocating cells and workers in fixed program order.
It excludes worker allocation, nested forks, and numeric identity observations.
Its proposed endpoint statement uses exact `Machine.obs` equality.
This does not assert equality of internal machine states.

### DET-OW-06: concrete evaluator laws stay concrete

The generic fiber evaluator receives machine state.
It can inspect fields that the concrete program evaluator ignores.
Existing trace-append laws do not prove trace independence for every evaluator.

State any trace erasure or scheduling bisimulation for `Program.evaluatorFor` and `Program.interpOf`.
Alternatively require an explicit evaluator law.
Do not infer it from a current inspection consumer being the only observed reader.

### DET-OW-07: single-writer promises still need a dependency proof

`PromiseControls.cycle` is typed and has a unique producer for each promise.
Its producers wait cyclically and do not finish.
`PromiseControls.handshake` finishes after one producer publishes before waiting.

Keep promises outside the first fragment.
The next slice needs an event dependency graph and guaranteed production, not just writer counts.

### DET-OW-08: type-preserving edits can change resource identity

`LiveView.edited` replaces one alias-producing expression with another expression of the same type.
The typing table splices successfully.
The unchanged continuation acquires a shared-write conflict.

Invalidate the phase's behavioral summary after this edit.
A typing repaint delta is insufficient evidence for reusing that summary.

## Landing order

These are planning estimates in focused working days, not measured completion times.
They assume the current machine and checker interfaces remain stable.

| Slice | Work and likely files | Estimate | Unlock |
| --- | --- | --- | --- |
| D0 | Correct note claims; land generic RD in `Laws/Machine/Descent.lean` with its audit and controls | 0.5–1 | A reusable conditional theorem, with no machine-wide claim |
| D1 | Data-only summary and typed-entry checker in proposed `Program/Schedule.lean`; located explanations and author controls | 1–2 | Useful optional editor feedback over ordinary programs |
| D2 | Primitive answer/store laws, summary interpretation, and final-observation proof in proposed `Laws/Program/Schedule.lean` | 3–5 | A certified result for the finite phase under the declared decision profile |
| D3 | Finite work measure and canonical driver connector | 2–3 | Completion under sufficient scheduling work and budgets; a justified canonical result |
| D4 | Current-input publication and graph annotations through existing session tools | 1–2 after D1 | Clear live feedback, stale-result protection, and linked explanations |
| D5 | Proven incremental invalidation and indexed first-conflict comparison | 2–4 after D1 | Reusable analysis with an explicit agreement law and measured cost |
| Later | Promise event extraction, modular summaries, and preemption extension | Separate estimates after their statements settle | Wider programs without weakening the first claim |

D4 can show an unproved analysis before D2.
It must not show a certified badge until D2's top node rests on no planned goal.
D2 does not require a universal name quotient or a general reachable-state explorer.
D3 does not claim infinite liveness under arbitrary decision tapes.

The existing typed root and state machinery stay authoritative.
Place checker data below Laws; place semantic statements and proof dependencies in Laws.
Keep the core import graph free of proof-graph tools and graph-rendering modules.
Coordinate root imports at the existing named anchors when a production brief assigns them.

## Open choices and recommendations

| Choice | Recommendation |
| --- | --- |
| A third route to a determinism claim | Propose schedule independence for a named observation and fragment; retain relational full meaning |
| Universal equality up to fresh-name renaming | Defer; exact endpoint equality suffices for the first fragment |
| User-written commutativity annotations | Refuse as evidence; recognize a closed family and prove its law once |
| Shared read-only cells | Include; they are useful and already fit the access matrix |
| Worker return values | Include ordinary data; keep handles and shared intermediate update answers excluded |
| A new parallel language | Avoid; analyze existing `Eff` and expose one operation on `Api.Typed` |
| Finite exploration as a certificate | Keep it diagnostic until coverage, transition enumeration, and witnesses are checked |
| A failed exploration bound | Report an unfinished search, never independence or unreachability |
| Resource and failure cases | Add later with finalizer accesses and state-before-failure retained |

No authority file is amended by this packet.
The coordinator can use these recommendations when recording a ruling.
