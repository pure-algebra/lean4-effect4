# Worker release entry restriction

The live source annotation now excludes the two actual release destinations.
A five-value prefix does not establish the connection value of a release.
The existing capture producer supplies that value instead.
The original `Workers.Assertions.logs_step` remains open.

## Placement

- Concept: store-typing, R4, and scope-lifetime-finalization, R11.
- Question: the capture and binding producers serve the unchanged `Workers.Assertions.logs_step`.
- Reach: both actual Worker acquisitions, every total, and supplied actual source binders.
- Limit: the annotation supplies no history, writer budget, progress, or log bound.
- Consumer: the shared accounting instance combines capture ownership with finalizer-start and writer costs.

`MachineWorkersSlots.OrdinaryPoint` excludes the two source release addresses.
`bind_destination_ordinary` derives the restriction from an actual bind head.
The actual gate callback and acquisition note keep the ordinary annotation.
`CapturedSlots` moves beside the binding data; its definition and scope consumer stay unchanged.
The extraction removes the duplicate predicate body from `MachineWorkersCapturedSlots`.

## Evidence

Base: `2e4a5e36a`.
The coordinator's shared cause and action modules supply the current frame contract during checking.
This slice changes no executable module or original scenario statement.

Each command passes with `LEAN_NUM_THREADS=3`:

```text
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersConnections.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersConnections.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersNativeSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersNativeSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersCapturedSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersCapturedSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersReleaseEntryControl.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersNativeSlotsAudit.lean
```

The finite control has the correct prefix and lexical length, but connection value 9.
The ordinary entry predicate rejects its actual first-release address.
This control establishes no failure of an admitted history.

The audit checks `ScopeFields`, `NativeScopeStore`, and both actual native/capture consumers.
It reports 215 declarations within `[propext, Quot.sound]`, zero modulo goals, and zero planned goals.
Its output is `MachineWorkersReleaseEntryAudit.out` beside the finite control.
`MachineWorkersCapturedSlots` changes from 204 lines to 199 lines after the predicate extraction.
`MachineWorkersSlots` changes from 652 lines to 698 lines with the data predicate and entry restriction.
The consolidation packet stops further scenario constructor expansion.
The next slice replaces native stack transport with the shared interference classification.

