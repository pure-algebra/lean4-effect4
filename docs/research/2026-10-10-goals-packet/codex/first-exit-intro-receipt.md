# First-exit source introduction receipt

The source entrant introduction compiles and passes its axiom audit.
This slice depends on `0f5fd4e0`, `6aba81de` and `677cb391`.

Placement: translation-simulation, R10, serving the frozen first-exit timeout repair.
`actionAt_raceAllFirst` connects the actual compiled action to its source entrant points.
The new `intro_withFiber` case consumes that equation and the existing entrant introductions.
The consumer is the compilation-to-declarative-program introduction used by `Typed.Residual`.
This proof establishes no outside implementation agreement, fairness or cleanup progress.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Intro.Fibers`: passes, 372 Lake jobs.
- Lake reports the changed `Intro.Fibers` build as 2.4 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitIntroAudit.lean`: passes.
- The audit walks 147 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

The remaining typed launch and denotation consumers await the checked backend handle and residual dependencies.
This commit also corrects requirement names and the compiler command in the two earlier source receipts.
