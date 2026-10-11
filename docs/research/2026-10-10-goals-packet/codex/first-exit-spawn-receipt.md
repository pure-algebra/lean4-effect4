# First-exit launch receipt

The first-exit launch clause and its typed assembly compile with no planned goals.
The slice depends on the checked bookkeeping commit `a741a709`.

Concept: residual-program-typing, serving `fiberClauses` on the M6 route.
`clause_raceAllFirst` constructs the typed race with first-exit mode and no selected exit.
`fiberClauses` consumes that clause for the new source action.
The original `clause_raceAll` retains first-success mode and no selected exit.
These clauses serve the frozen timeout repair, translation-simulation R10.
They retain the existing source, world, point and command-typing assumptions.
They establish no host-table typing, outside observation agreement, cleanup progress or fairness.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Commands.Clauses.Spawn Effect4.Laws.Program.Typed.Commands.Clauses.All`: passes, 514 jobs.
- Lake reports the changed modules as 3.4 seconds and 1.5 seconds respectively.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitSpawnAudit.lean`: passes.
- The audit walks 126 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.
- `git diff --check`: passes.

The coordinator owns the first-exit behaviour gates and the original scenario goal assemblies.
The source proof bridge is complete across source typing, introduction, handles, denotation, adequacy and launch clauses.
