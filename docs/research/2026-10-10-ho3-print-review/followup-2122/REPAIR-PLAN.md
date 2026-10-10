# Repair the invocation proof trust failure

The cycle-aware audit refuses the reviewed HO-3b proof graph.
`rowPrint_inv` and `rowDom_inv` in `src/Effect4/Laws/Codegen/ReadPrint.lean` reach `Classical.choice`.
The reported path passes through `Pi.instNonempty` and `Classical.ofNonempty`.
The build alone does not test that boundary.

## Placement

Concept: `exact-codecs`, required reconstruction property in `docs/core/semantics.md`.
Questions: existing `typed-print-erasure`, `typed-print-read`, and `module-defs-round-trip` compatibility claims.
Helpers: `rowPrint_inv` and `rowDom_inv`, consumed by `read_print` and the typed erasure inductions.
Reach: their existing row-selection premises and their structural inversion conclusions, under decisions rows 325 and 340.
Limits: this repair establishes neither successful printing nor typing, target acceptance, or host behavior.
Unlock: restore the prescribed axiom boundary for the existing R8 reconstruction claims.

## Probe

Keep both helper statements unchanged.
Test explicit row and output splitting as a negative control.
Provide constructive local function instances before proof search in the positive control.
Keep the invocation witnesses and all existing hypotheses unchanged.
Audit the alternative helper proofs in isolation.
Keep the failed original audit as the negative control.

Do not weaken a premise, change source admission, or add a printing option.
A passing helper audit does not replace a downstream rebuild and audit after the owner applies the repair.

## Checked result

The split-only control compiles but retains both choice dependencies.
The constructive-instance alternative compiles and passes the cycle-aware audit.
`repair-controls.json` records both outcomes and unchanged input hashes.
`repair-statements.json` records exact statement comparison after renaming the probe declarations.

The repair changes proof search's instance selection.
It does not install a default callback in program data or machine execution.
Keep the instances local to these proofs until another measured consumer requires shared proof infrastructure.
