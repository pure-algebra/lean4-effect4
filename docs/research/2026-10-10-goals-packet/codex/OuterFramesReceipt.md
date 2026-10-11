# Saved frames outside the command runner

The custody history proof can now retain saved-frame sequencing through every outside edit it uses.
The history endpoint remains open.

Base: `ec101452d`. The commit containing this receipt is the landing head.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`.
Role: invariant preservation.
Evidence status: proved without planned-goal dependencies.
Scope: actual dispatcher drain, scheduler verdict, interruption, owed-resume posting, clock advancement and reply preparation.

`OuterFrames.interrupt` instantiates the existing `NativeMachineShape.edit` classification.
Keyed updates reuse `CommandSequencing.configuration_update`.
The remaining edits retain the fiber list or only change its metadata.
No command ownership, source count, release funding, progress or outside implementation claim follows.

Changed sources: `src/Effect4/Laws/Program/ReleaseCustody/OuterFrames.lean` and its import in `Execution.lean`.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers`: passes, 1149 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/OuterFramesAudit.lean`: passes.
- The audit checks 15 declarations within `[propext, Quot.sound]`, with no planned goals or modulo declarations.

Behavior gates remain scheduled after the major proof structures land. This slice changes only proof modules.
