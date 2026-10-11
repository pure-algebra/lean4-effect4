# Compiled store command receipt

The shared source-to-command connector compiles and has no planned-goal dependency.

Placement: translation-simulation, R10, the command step of proposed `queue-expansion-agrees`.
Consumers: Atomic heap-site transfers and QueueWorkers `Assertions.jobs_step`.
Reach: an arbitrary native fiber at a compiled `Ref.modify` row.
Premises retain its capture, request value, operation budget, interrupt flag and yield override.
The answer is the exact machine update and pending command suffix.
The caller's stack remains in the updated fiber.
The connector establishes no writer census, whole-run closure, progress or outside-host behavior.

Base: `69a002e23`, including shared ControlSteps from `c5c7cf921`.
Files: `src/Effect4/Laws/Program/StoreExecution.lean`, the packet's `StoreExecution.lean` probe and this receipt.
The landing commit contains this receipt.

`/usr/bin/time -p env LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.StoreExecution` succeeds with 340 jobs.
Times: real 2.66 seconds, user 1.52 seconds, sys 1.05 seconds.

`/usr/bin/time -p env LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/StoreExecution.lean` succeeds.
Times: real 1.64 seconds, user 0.65 seconds, sys 0.96 seconds.

```text
#axiom_audit: 76 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

`git diff --check` succeeds.
The coordinator imports `Effect4.Laws.Program.StoreExecution` through the Laws root.
This law changes no program or machine behavior.
No outside-runtime gate or push runs in this lane.
