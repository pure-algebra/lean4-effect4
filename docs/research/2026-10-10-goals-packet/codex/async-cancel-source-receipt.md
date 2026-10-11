# Native Async cancellation ownership

The actual native cancellation producers discharge the strengthened source ownership field.
The original application statements remain unchanged.

Concept: scope-lifetime-finalization.
Requirement: R11.
Role: preservation.
Consumers: source opportunity accounting and actual Workers registration counts.

Base: `a4b12837`, with the exact NativeScope change from root `a21844cb`.
The root change connects external registration names to their actual source operation.

`AsyncCancelAt` recognizes native deferred cancellation and stored deferred or timer cancellation.
The existing `CodeAt` Async arm requires that producer shape alongside its prior source ownership.
The compiler, stored-program fold and callback proofs discharge the field.
Actual frame evaluation retains the prior source ownership through the stronger projection.
The actual Workers history reader extracts the field for every natural job count.

The numeric current projection counts a latent Async cancel continuation before it is pushed.
Actual native producers have zero selected source opportunity in that continuation.
`AsyncCancelBoundary.lean` retains the synthetic boundary that motivated the restriction.
Its finite reader shows one synthetic callback counted in both stale current code and the newly pushed frame.
The source ownership field excludes that callback from actual native configurations.
This is a projection control, not an admitted program history or an outside runtime comparison.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity`: passed, 1081 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AsyncCancelBoundary.lean`: passed.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/AsyncSourceAudit.lean`: passed.
- Audit: 1269 declarations within the permitted axioms; zero planned goals; zero declarations modulo goals.

The first combined build also attempted the unfinished primitive accounting aggregate.
That aggregate fails separately and is absent from this commit.
The native source, heap, admitted-history and application reader targets compile with the stronger field.
No new planned goal, runtime change or application assumption is introduced.
Whole-history source-use uniqueness remains open.
