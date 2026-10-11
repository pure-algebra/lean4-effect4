# Captured source producers

The source predicate now records the actual acquisition or onExit source constructor.
The existing source, heap and reply history proofs retain their statements.

Concept: scope-lifetime-finalization, R11.
Role: preservation.
Claim: source opportunity accounting serves FinalizerRun.once_placed_pushes_once and Workers.Assertions.registrations_step.
Consumer: SourceOpportunities.captured_zero and SourceOpportunities.finalizer_zero.

Base: 3ac2db31d.
Changed modules: Effect4.Laws.Program.NativeScope and Effect4.Laws.Program.NativeInterpScope.

FinAt records an acquisition source constructor for captured foreign finalizers.
NameAt records the producer constructor for acquisition callbacks and authored onExit callbacks.
ThunkAt records the producer constructor for masked acquisition thunks.
The compiler proves these facts from the actual resolved source node.

Command: LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity.
Result: 1071 jobs succeed.
Command: LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/RegistrationSourceAudit.lean.
Result: 3025 declarations remain within propext and Quot.sound; no modulo declarations or planned goals.

This checkpoint establishes source constructor ownership.
It does not establish dynamic registration uniqueness.
The application census and complete command accounting remain separate dependencies.
