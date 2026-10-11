# First-exit typed source receipt

The first-exit source denotes a typed entrant action and saves a typed answer frame.
This slice depends on `aa976b2f`, the checked simulation and residual extension.

Concept: residual-program-typing, serving `denoteAt_typed` on the M5 route.
The private expansion helpers serve `raceAllFirst_arm`.
That arm consumes the existing checked joined entrant columns and serves `withFiber_arm`.
`raceAllFirst_frame` serves typed command evaluation at the first-exit answer frame.
The source action serves the frozen first-exit timeout repair, translation-simulation R10.
The helpers retain the existing source, world, point and judgment assumptions.
They establish no general host-table typing, outside observation agreement, cleanup progress or fairness.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Typed.Adequacy`: both targets pass in the focused bridge build.
- Lake reports the changed modules as 11 seconds and 8.9 seconds respectively.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitTypedSourceAudit.lean`: passes.
- The audit walks 986 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

The combined launch-clause build still needs the coordinator's mode-aware `Typed.Commands.Bookkeeping` extension.
The launch clause and its assembly remain the next source bridge slice.
