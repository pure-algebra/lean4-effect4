# Prepared run views

The run view computes its static program lines and printed code once for each frame sequence.
The preparation reads the run's `Api.Built` and its exact row table.
Base: `9389e543`.

## Placement

1. Concept: `initial-algebras-folds`, in `docs/core/semantics.md`.
   The preparation retains the existing view's readings.
   It serves fold congruence by keeping the built input fixed.
2. Question: the tool compatibility law `prepared-run-view-agrees`.
   `Compare.lean` checks that question on the finite corpus.
   No generic view-agreement theorem is claimed.
   The helper's consumer is `framesBuilt` in `tools/Tools/View/Run.lean`.
   Decisions rows 334 and 336 permit a named tool law.
   The control helper proves that a planned control keeps the built program.
3. Reach: one built program, its exact row table, and each planned control's frame.
   The finite comparison covers existing empty-table output and one nonempty row table.
4. Limits: preparation establishes no cost bound, scheduler progress, or host correspondence.
   Source addresses remain source addresses.
   The change assumes no connection between expanded call addresses and source addresses.
5. Unlock: the run viewer reuses its static readings.
   Later MCP resources can retain the same preparation at the same built program.
   R13's journal replay and R14's checked address view remain their existing laws.

## Finishing criteria

- Bind preparation to the run's built program through its type.
- Compare representative frames with the former implementation.
- Check the displayed type and code at a nonempty row table.
- Measure repeated preparation separately from frame rendering.
- Build the changed module and its direct consumer.
- Audit the changed module with the cycle-aware walk.
- Record exact rendering exclusions, commands, results and remaining limits.
- Commit only the owned source and evidence paths.
