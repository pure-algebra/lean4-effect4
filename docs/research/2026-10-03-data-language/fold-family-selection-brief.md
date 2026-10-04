# Stable fold family selection

`fold_of` must retain one selected family across mutual siblings and fixed binders.
The coordinator assigns this repair after a concrete import-dependent failure in `Typed.Fits`.

## Placement

Concept: Free Algebra & Catamorphisms (`docs/core/semantics.md`).
Role: tooling for the existing agreement-of-folds proof graph.
Consumer: `Fits.eq_cata` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
Requirement: R3, supporting the M5 membership proofs.

The repair selects a family recognized in the target's arguments and supported by every mutual sibling.
It refuses no common family and ambiguous common families.
An explicit family selection must itself satisfy the shared-family check.
Reopening fixed binders retains the chosen family identity.

This repair changes inference, not a semantic judgment or a generated theorem statement.
The generator still checks its proof terms in Lean.
No host behavior follows from the tool's family selection.

## Files and checks

Edit only `src/Effect4/Program/FoldOf.lean` and its focused fixture.
The fixture is `Test/Program/FoldFamilySelection.lean`.
The coordinator imports `Test.Program.FoldFamilySelection` into `Test/All.lean`.

Check mutual inference with both `Store.Val` and `Ty` folds imported.
Check explicit selection and refusal of ambiguous inference.
Inspect each generated connector's axioms.
Inventory existing callers and check each affected consumer.
The fold connector statements retain their existing hypotheses and conclusions.
