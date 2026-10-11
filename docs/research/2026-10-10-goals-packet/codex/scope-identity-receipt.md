# Scope identity preservation

This helper discharges scope-entry identity preservation for the pending release-custody command proof.
It closes no original scenario by itself.

Base: `1245a4f2`.
Head: the commit containing this receipt.

## Placement

Proof role: preservation helper of registration custody.
Evidence status: proved, within `[propext, Quot.sound]`.
Concept: scope-lifetime-finalization, R11.
Consumer: `Program.ReleaseCustody.Execution.command_custody` and its evaluator clauses.

`Machine.ScopeIdentity.Allocated` reads distinct scope-entry keys below the fresh-name supply.
`syncOpStep_allocated` carries that predicate through every actual native store step.
The helpers cover scope replacement, allocation, finalizer removal, closure and child-scope creation.
The statement retains its input invariant and successful-step premises.
`Stores.ScopeKeysFresh` remains a separate registration-key predicate.
The result establishes no progress, completed cleanup, host behavior or whole-run invariant.

## Files and checks

- `src/Effect4/Laws/Machine/ScopeIdentity.lean`
- `docs/research/2026-10-10-goals-packet/codex/ScopeIdentityAudit.lean`
- `docs/research/2026-10-10-goals-packet/codex/ScopeIdentityAudit.out`

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.ScopeIdentity` passes with 249 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/ScopeIdentityAudit.lean` passes.
The audit reports 19 declarations, no planned goals and no dependence on goals.
This proof-only helper changes no behavior.
Root reachability follows when the release-custody consumer imports it.
