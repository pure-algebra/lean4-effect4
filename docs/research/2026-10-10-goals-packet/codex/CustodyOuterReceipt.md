# Release custody outside the command loop

The scheduler obligation is proved. The universal command obligation remains open.

Base: `54f099c75`. The landing changes `ReleaseCustody.Execution` and retains its compiled probe and audit.

## Placement

- Concept: scope-lifetime-finalization. Required property: at most one release per registration, R11.
- Question: `ReleaseCustody.Execution.outer_custody` supplies the existing decision lift.
- Consumer: `Execution.decision`, then `Execution.history` and `Workers.Assertions.releases_step`.
- Reach: every native program, row table, source identity, machine and command budget, under the explicit command contract.
- Exclusions: no progress, source uniqueness, or host agreement follows from this scheduler proof.

The proof accounts for dispatcher snapshots, interruption, timer advancement, host-answer preparation and scheduler bookkeeping.
Completion code carries no release credit. Native answer preparation retains scope entries and their allocation supply.
The proof uses the existing machine and decision lift. It introduces no execution representation or planned goal.

## Checked evidence

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution`: passes, 498 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions`: passes, 1073 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CustodyOuter.lean`: passes.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CustodyOuterAudit.lean`: passes.

The audit reports 64 declarations within `[propext, Quot.sound]`, two modulo planned goals, and one planned goal.
The remaining goal is `Execution.command_custody`. The scheduler theorem has no dependency on that goal; its command contract is an explicit premise.

The landing changes proofs only. The affected behavior gates passed at `b3d481c8a`; this landing changes none of their runtime inputs.
The original worker and queue release clauses remain open through the command and source-placement obligations.
