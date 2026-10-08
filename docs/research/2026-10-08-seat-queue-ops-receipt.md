# Queue operation proof migration receipt

The complete owned Queue Ops source passes against the final checked Queue Steps dependency.
Its source axiom gate passes for 65 declarations.

Source: `src/Effect4/Laws/Modules/Queue/Ops.lean`.
The six step scope proofs consume `Step.scoped` and `Input.source_scoped`.
The existing `Queue.message_nodes` and `Queue.offer_nodes` names remain compatibility aliases to the shared upstream formation helpers.
Every existing theorem header remains identical, including binder names and premises.

## Placement

Concept: initial-algebras-folds, requirement R4.
Question: helpers of `operation-data-scoped`, consumed by Queue wrapper scope and client admission.
Reach: the existing source scope judgment for every scoped caller source.
The proofs establish no behavior agreement, allocation, progress, liveness, or host execution.
The unchanged formation aliases serve the existing R4 operation typing consumers.

## Checks

All six isolated scope proof bodies pass before and after generic tuples.

`LEAN_NUM_THREADS=3 lake env sh -c 'LEAN_PATH="/Users/pooks/.codex/worktrees/module-folds/lean4-effect4/.lake/build/lib/lean:$LEAN_PATH" lean -DwarningAsError=true src/Effect4/Laws/Modules/Queue/Ops.lean'` passes.
The dependency worktree HEAD is `6d014154c56848660aa941efb88a7b22b87004fd`.
This checks all owned source, including the operation consumers, without changing dependency files.

`LEAN_NUM_THREADS=3 lake env sh -c 'LEAN_PATH="/Users/pooks/.codex/worktrees/module-folds/lean4-effect4/.lake/build/lib/lean:$LEAN_PATH" lean -DwarningAsError=true /private/tmp/queue-ops-trust-source.lean'` passes.
The scratch file contains the owned source followed by the focused audit.
It selects every current-module declaration through `env.getModuleIdxFor?`, requires a nonempty selection, and checks `ProofGraph.Audit.factsOf` flags.
`ProofGraph.reachedAxiomsMany` audits 65 declarations; only `propext` and `Quot.sound` are permitted.
A preliminary imported-module-only audit selects no current-source declarations and is discarded as vacuous.
The corrected source audit covers every current declaration without a namespace filter.

The header comparison reports no changed existing header.
`git diff --check` passes.
The coordinator owns the final imported-module axiom gate, library-root gate, and integrated battery checks.
No full sweep or host check runs in this slice.
