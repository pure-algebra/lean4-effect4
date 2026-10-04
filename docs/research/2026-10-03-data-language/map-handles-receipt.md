# String-map reader and raw-handle proofs

The low-level helpers pass their checks. Native atom integration remains pending.
The coordinator retains the OCaml manual edits separately.

Base: `994c8a6c`, with source `bc781486` and generated inventory `8f7077fd`.
The commit containing this receipt supplies the low-level head.

## Placement

The five-part placement is `map-handles-brief.md` beside this receipt.
`readPairs_map`, `readTuples_map`, `readPairs_exact`, `readTuples_exact`, and `read_write` serve `denote-typed` through the typing seat's `Typed.MapValues`.
`read_exact`, `write_handles`, `tupleEntries_handles`, and `read_handles` connect the raw carrier to its handle list.
The five operation subset helpers serve `m7-exit-handles-valid` through the native term consumers.
`keys_handles` gives an empty handle list, which supplies its subset immediately.
No helper adds a typing, registered-input, canonicality, or external host premise.

## Files and checks

- `src/Effect4/Laws/Machine/Map.lean`: reader reconstruction and raw handle proofs.
- `Test/Program/MapHandles.lean`: finite controls and axiom queries.
- `map-handles-brief.md`: placement and file ownership.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.Map
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/MapHandles.lean
```

The module build reports `Build completed successfully (7 jobs)`.
The fixture passes eight controls and 14 axiom queries.
Every queried theorem stays within `[propext, Quot.sound]`.
The controls retain unknown kind bytes 254 and 255 through map operations.
They distinguish ordinary entry tuples from map-entry pairs.
They check last-occurrence construction and missing-key lookup.
These controls remain finite evidence.

No machine execution, scheduler progress, liveness, or OCaml simulation follows from this slice.
Native atom consumers and their unchanged theorem statements remain pending for the next checkpoint.
