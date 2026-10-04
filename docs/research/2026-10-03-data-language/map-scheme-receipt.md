# Map scheme checkpoint

The coordinator can now regenerate PreludeAtoms from all six atom schemes.
The source repair changes one raw helper equation; the handle-proof seat owns its corresponding proof repair.
This checkpoint does not yet claim the full typing graph builds.

Base: `71d9f9ae`, after the shared map reader proofs.
Branch: `codex/data-admission`.
The commit containing this receipt is the checkpoint head.
The earlier machine source is `bc781486`; generated AtomInventory is `8f7077fd`.

The six schemes use the types in the tracked map contract.
Update binds the old and replacement value types separately and returns their union.
The existing polymorphic scheme handles all five nonempty-signature operations.
No new inference rule is needed.

Proof preparation found a counterexample to the first raw construction helper.
An empty fiber snapshot passes the existing list membership check at every element type.
A helper restricted to the carrier's plain list would therefore fail on a typed argument.
Construction now reads the outer list through `Val.asList?`, as the existing list atoms do.
The fixture retains empty-snapshot success and nonempty-snapshot refusal.
The old typing and progress premises remain unchanged.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Program.NativeAtom
PASS: 25 jobs

LEAN_NUM_THREADS=3 lake env lean Test/Program/MapValues.lean
PASS: 30 finite guards
```

Both checks passed on their first attempt.
`Machine.Map.fromEntries`, `Machine.Map.set` and `NativeAtom.eval` report `[propext]`.
`NativeAtom.ofName?_name` reports no axioms.
Logs: `/tmp/map-schemes-build.log` and `/tmp/map-snapshot-fixture.log`.

Result membership, world-indexed membership and typed evaluation existence remain in progress.
The raw-handle helper's arbitrary-input success statement remains unchanged during its repair.
The brief now names its precise consumer path through `MeaningSound.evalTerm_validIn` and `Denote.meaning_typed`.
Target execution and JSON codec boundaries remain separate.
No full battery, root axiom gate or generator ran in this seat's checkpoint.
The Lean lane is released to the coordinator for the next producers.
