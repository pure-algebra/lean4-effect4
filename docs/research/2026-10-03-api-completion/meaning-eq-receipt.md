# Straight-fragment composition receipt

Merge fact: this is a checked contribution to T5 for the existing straight fragment and the exit/full-store observation. It does not close general T5 or T3.

Base: `8913519b146d95c07a3eaa195df1a1fcda2c642a`. Implementation head: the commit containing this receipt (`git log -1 --format=%H -- src/Effect4/Laws/Program/MeaningEq.lean`). Branch: `codex/run-replay-api`. No push.

## Placement and result

The prior `plan.md` places the obligation in concept 10 (Translation and Simulation), supported by concept 7 composition, proposed registry claim `straight-composition-agreement`, R8. The new local `StraightEqWanted.run_agrees` goal is 1/1 proved. The relation and all its helper laws have the concrete `run_agrees` / `run_agrees_at_bound` execution consumers. This is proof-side data over the existing program and denotation, not a second program representation.

`StraightEq` requires both programs to belong to `Straight` and gives equality of exit and complete stores for every environment and initial store. Its constructors support bind, selection, materialized exits, cause handling and finalization. Suspension removal supplies a concrete source-shape change. The runtime connector reuses `run_eq_meaning` at the existing empty initial environment/store and empty host table; source and destination may have different sufficient budgets. `fuelFor` computes those bounds from the existing measures.

No typing preservation, trace equality, equal insufficient-fuel frontier, scheduled or looped congruence, host execution, target execution, or whole-machine equality is asserted. E4-DEN-CE-003/004/005 and decision 138/DI-57 remain the limits of the underlying denotation connection. Existing M5-M7 statements are unchanged.

## Files

- `src/Effect4/Laws/Program/MeaningEq.lean`
- `Test/Program/MeaningEqContract.lean`
- `src/Effect4/Laws.lean`: import after `Effect4.Laws.Program.Agreement.Machine`.
- `Test/All.lean`: import after `Test.Program.AgreementContract`.
- This research directory: prior plan, axiom inspection script, focused output and receipt.

## Verification

- `lake build Effect4.Laws.Program.MeaningEq Test.Program.MeaningEqContract`: passed, 306 jobs (raw log not retained).
- `lake env lean docs/research/2026-10-03-api-completion/MeaningEqAxioms.lean`: passed; all 16 inspected declarations use a subset of `[propext, Quot.sound]`; `evidence/meaning-eq-axioms.txt`.
- `git diff --check`: passed before commit.
- Independent source review by the program-path-editing seat: no finding; no duplicate build in this worktree.

Fixtures prove and execute suspension removal under binding, failure and cleanup: both runs retain reference value 8 and fail with 5 at different budgets. Negative fixtures reject exit-only comparisons with different stores and the outside-fragment fallback; zero fuel remains unfinished. Congruence consumers cover selection, exit, catchCause and matchCause. These executable guards are finite evidence in addition to the general checked theorems.

## Proposed registry insertion

Add `straight-composition-agreement` under concept 10, role simulation, declaration `Effect4.Program.Denote.StraightEq.run_agrees`, with the exact fragment/observation and budget premises above. The dirty coordinator-owned semantics authorities and generated status files were left unchanged; this receipt records the proposal rather than claiming a generated status update.
