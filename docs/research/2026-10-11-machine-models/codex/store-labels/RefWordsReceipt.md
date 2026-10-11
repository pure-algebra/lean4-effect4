# Reference-word probe receipt

The shared word laws check, but the native producer connector remains open.
This probe closes no original application goal.

Base: `6d2c7b5e7` on `codex/last-planned-goals`.
The source is `RefWordsProbe.lean`; its placement and consumers appear in `PLAN.md`.
No library or executable source changes in this slice.

## Checked scope

The annotation reuses `MoveLabel` and `Contracts.Path` over reference heaps.
Each executed edge retains its actual operation, answer, and store-step equation.
The fold reconstructs the final reference heap from that certified path.
The frame rule retains lookups outside the conservative footprint, including absent cells.
The word erases to the existing traced frame relation.
Composition retains the ordered event suffix.

The concrete readers cover an existing-cell write followed by allocation, two untouched lookups, and a successful read.
The footprint includes read-only selected cells; it is not an exact write census.
The result establishes no source permission, history funding, progress, full-store equality, or host agreement.

## Verification

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/RefWordsProbe.lean` passes.
`LEAN_NUM_THREADS=3 lake env lean -R /private/tmp -o /private/tmp/RefWordsProbe.olean -DwarningAsError=true /private/tmp/RefWordsProbe.lean` passes.

The audit imports that compiled probe and `ProofGraph.AxiomAudit`.
Its command uses the checkout's Lake environment with `/private/tmp` prepended to `LEAN_PATH`.
`lake env lean -DwarningAsError=true /private/tmp/RefWordsAudit.lean` then passes under that environment.
`RefWordsAudit.log` reports 35 declarations within `[propext, Quot.sound]`, no modulo declarations, and no planned goals.

The retained probe has 175 lines.
`RefWordsEvidence.json` records the checked source and audit hashes.
No old theorem statement changes and no behaviour gate is reached.
