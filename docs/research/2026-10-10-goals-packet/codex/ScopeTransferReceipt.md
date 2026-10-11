# Native scope-credit transfers

Every native synchronous store operation now has a checked credit bound. The whole-command obligation remains open.

Base: `81beed83`. The landing adds `ReleaseCustody.ScopeTransfer` and a reader with premise controls.
It moves the existing registration-freshness proof into `Machine.ScopeIdentity` and makes `Simulation.Hooks` reuse it.
The Laws and Test roots register the new modules.

## Placement

- Concept: scope-lifetime-finalization; required property: at most one release per registration, R11.
- Question: these helpers serve `ReleaseCustody.Execution.command_custody` and its evaluator, link, removal and close cases.
- Consumer: the original worker and queue release clauses through `Execution.history`.
- Reach: actual native stores and operation results, with distinct scope identities and fresh registration keys.
- Exclusions: no source-use bound, progress, completed-history claim or outside-host agreement follows from these local transfers.

`ScopeTransfer.add` proves an exact equation across the resulting store and the returned value.
Open registration transfers credit into the scope. Closed registration transfers credit into the immediate cleanup response.
Removal discards credit. Scope fork and fiber linkage add only administrative finalizers.
State-first close transfers every selected credit into its returned close program.

The freshness census has one body. The existing simulation proof calls the extracted theorem without an additional premise.

## Checked evidence

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.ScopeTransfer`: passes, 360 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Program.ReleaseCustodyScope Effect4.Laws.Program.ReleaseCustody.Execution Effect4.Laws.Program.Simulation.Walk`: passes, 948 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/ScopeTransferAudit.lean`: passes.

The audit reports 168 declarations within `[propext, Quot.sound]`, zero modulo declarations and zero planned goals.

The reader applies the transfer law to a real open-scope operation.
Finite controls show duplicated scope identities duplicate credit, and stale registration keys replace an existing entry.
An unknown scope returns no result. These controls justify the transfer law's premises without replacing its proof.

The landing changes proofs and fixtures only. The affected behavior gates passed at `b3d481c8a`; no runtime input changes here.
