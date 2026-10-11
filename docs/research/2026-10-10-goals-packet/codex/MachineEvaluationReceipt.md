# Release custody evaluator checkpoint

The whole command obligation remains open.
This checkpoint supplies checked callback producers and the actual forced-yield command branch.

Base: 208a1a947, including the coordinator's ScopeIdentity result.
Consumer: Execution.command_custody and Execution.outer_custody, then Workers.Assertions.releases_step.

Placement:

1. Concept: scope-lifetime-finalization; required property: at most one release start per counted registration.
2. Question: the existing Workers release clause consumes the two placed Execution custody obligations.
3. Reach: arbitrary native source, table, selected fiber, stack, interruption cause and pending command suffix.
4. Limit: continuation popping and the remaining command branches stay open. No progress or host agreement follows.
5. Unlock: R11 through the existing Machine.Lift command and decision interfaces.

Evaluation bounds every native and stored value callback and suspension producer.
Cause callbacks produce zero credits.
The forced-yield theorem reads the actual charged yield verdict and actual operation count.
It preserves Funded through the actual driveStep update and emitted events.
The interruption bound reads the response-sensitive stack projection.
Execution.ready_update and ready_emit supply the coordinator's outside-loop proof.

Commands:

- LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution: passes, 497 jobs.
- LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineYieldCustody.lean: passes.
- Axiom audit: 1250 declarations within propext and Quot.sound; zero goals and zero modulo declarations.

The audit covers Names, Control and Evaluation.
Execution retains its two placed goals; this checkpoint proves neither whole-run goal.
The coordinator runs the deferred behaviour gates.
