# Executed reference words

Actual native iterations now supply the checked reference word.
The original reference-transfer theorems retain their names and statements.
The original application accounting goals remain open.

## Placement

Concept: store-typing R4 and reactive-scheduling R11.
Question: `cell-invariant-from-write-sites`, serving the original application accounting goals.
Consumers: `primitive_refTransfer`, `native_refTransfer`, `iteration_refTransfer`, and the existing native heap history.
The observation is exact reference lookup, including absent keys.
The statements quantify over the actual returned iteration and its synchronous operation and answer.
They establish no generation permission, progress, or outside runtime agreement.

## Change

`RefWords` annotates existing move labels and uses the shared `Contracts.Path` over reference heaps.
Its fold recovers the final reference heap.
Its conservative footprint includes reads and allocation's actual returned key.
An absent footprint member retains its exact lookup.
List membership represents finite union; duplicate entries change no membership judgment.

`primitive_refEffects` reads the same indexed `PrimitiveProducer` as the existing frame and source proofs.
It returns both the old reference transfer and the reference word.
The synchronous branch retains its actual operation and answer even when references stay equal.
The native wrappers compose these paired results through the existing alternatives.
The old transfer theorems become projections, replacing their previous bodies.
No evaluator or command classification is added.

A reference certificate alone describes reference changes, not every operation that executed.
The indexed producer supplies execution evidence; each source instance still owes generation and phase permission.
Reference equality grants neither permission.
Other store components remain outside this observation.

## Evidence

Base: `1591530e9978b1d1d07c5646f093f55d923294b1`.
Changed source files: the new `RefWords`, `NativeHeapExecution`, and the existing `PrimitiveProducerReader` battery.
`LandingEvidence.json` records their source hashes and before-and-after line counts.
The source measurement finds 302 added lines and 19 unchanged old theorem headers.
It compares header bytes before the first declaration `:=` and measures textual stability only.

The reader uses an actual allocated-read producer.
Concrete readers compose a write and allocation and retain an untouched cell and an absent cell.
A successful read and a write of the current value both retain actual operation evidence.
These finite readers establish no application history claim.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHeapHistory Test.Dogfood.Proofs.PrimitiveProducerReader Test.Machine.ReferenceFootprint Test.Dogfood.Proofs.HostTimeoutNumberState
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/RefWordsLandingAudit.lean
git diff --check
```

The build passes with 1115 jobs.
The audit checks 99 declarations within `[propext, Quot.sound]`, with zero planned goals and zero declarations depending on them.
`LandingBuild.log`, `LandingAudit.lean`, and `LandingAudit.log` retain the commands' results.
The first build finds dependent branch indices that need their actual result equation retained.
The repaired proof records that equation before splitting; the next repair makes both scoped exits explicit.
The final source passes the same targets.

## Remaining work

Timeout still needs actual captured generation permissions, persistent cleanup provenance, and completed loser-join evidence.
Workers, QueueWorkers, and Atomic still need their application balances and source permissions.
The reference word removes a shared execution obligation; it does not close those history proofs.
No runtime definition changes, so this slice adds no behavior gate obligation.
