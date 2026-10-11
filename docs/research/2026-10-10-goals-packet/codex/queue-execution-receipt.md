# Queue native command transfer receipt

Take and offer attempts now have checked transitions on the actual native command rule.
The whole-program conservation preservation goal remains open.

Placement: translation-simulation, R10, the command half of proposed `queue-expansion-agrees`.
Consumer: QueueWorkers `Assertions.jobs_step`.
Reach: an arbitrary fiber at a source row resolved from the actual root program.
The existing Queue attempt laws supply the encoded next cell, reply and notifications.
The machine command commits those values and retains its stack and pending command suffix.
The same transition satisfies the shared model job conservation laws.
Premises retain source position, capture, first profile, request, membership, budget and interrupt state.
These laws establish no writer census, wrapper delivery, whole-run closure, progress or outside-host behavior.

Base: `20615175`, including shared ControlSteps from `c5c7cf921`.
Files: `src/Effect4/Laws/Library/Queue/Execution.lean`, packet probes `QueueExecution.lean`, `QueueSites.lean` and this receipt.
The landing commit contains this receipt.

`/usr/bin/time -p env LEAN_NUM_THREADS=3 lake build Effect4.Laws.Library.Queue.Execution` succeeds with 582 jobs.
Times: real 2.56 seconds, user 1.04 seconds, sys 1.10 seconds.

`/usr/bin/time -p env LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/QueueExecution.lean` succeeds.
Times: real 2.11 seconds, user 1.01 seconds, sys 0.95 seconds.

```text
#axiom_audit: 2 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The finite `QueueSites.lean` probe uses the existing `Node.addresses` traversal at total zero.
It prints the actual Ref.modify source addresses and their request variable indices.
It succeeds; real 3.07 seconds, user 0.60 seconds, sys 1.09 seconds.
This source-location probe proves no dynamic source-capture invariant.

`git diff --check` succeeds.
The coordinator imports `Effect4.Laws.Library.Queue.Execution` through the Laws root.
The next proof needs actual reachable source capture, queue-cell writer provenance and command-suffix custody.
The program and machine behavior remain unchanged.
No outside-runtime gate or push runs in this lane.
