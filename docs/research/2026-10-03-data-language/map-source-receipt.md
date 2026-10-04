# Map source checkpoint

The coordinator can regenerate AtomInventory from this checked source stage.
PreludeAtoms waits for the next typing-scheme stage.
The generated inventory is intentionally stale between these stages.

Base: `2d6534e9`. Branch: `codex/data-admission`.
The implementation scope and five-part proof placement are in `map-operations-brief.md` and the coordinator's `maps-tuples-brief.md` at `d69a28da`.
Decision row 197 fixes constructor duplicates and update typing.

The six appended native atoms evaluate through `Machine.Map`.
Map values use pair entries; entry construction and extraction convert ordinary two-item lists.
Construction keeps the last supplied value for a repeated key.
Update replaces the named entry and restores distinct keys in UTF-8 order.
Lookup keeps absence separate from present unit, option-none and nested handles.
The raw readers refuse malformed entries and nonstring keys.
Their success alone is not a membership certificate.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Machine.Term
PASS: 19 jobs

LEAN_NUM_THREADS=3 lake env lean Test/Program/MapValues.lean
PASS: 28 finite guards
```

The source and fixture passed on their first attempt.
`Machine.Map.fromEntries`, `Machine.Map.set` and `NativeAtom.eval` report `[propext]`.
`NativeAtom.ofName?_name` reports no axioms.
Logs: `/tmp/map-source-build.log` and `/tmp/map-source-fixture.log`.
The brief passes the strict language check. `git diff --check` passes.

Typing schemes, coarse and world-indexed result membership, evaluation existence and handle-subset proofs remain for the next stage.
The prelude bodies are source data; no TypeScript compiler or target execution ran in this checkpoint.
No generator, case census, whole battery or root axiom gate ran here.
The coordinator owns the generated outputs, target checks and policy measurements.
No new term or type constructor was added.
The Lean lane is released to the coordinator.
