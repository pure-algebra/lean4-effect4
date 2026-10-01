import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-! Seat J, step 1: the census rows of the `Representation` family in `Effect4.Codegen.Schema`,
where the two folds through the private `printAlgebra` print. Run from the worktree root (the
census reads `tools/Effect4Gen/manifest.json` relative to it):
`lake env lean docs/research/2026-10-01-landing/seat-J/probes/CensusSchemaRows.lean`. -/

#traversal_census Effect4.Representation under Effect4.Codegen.Schema
