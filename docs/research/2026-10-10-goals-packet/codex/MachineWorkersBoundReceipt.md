# Workers acquisition answer classes

The original `Workers.Assertions.logs_step` remains open.
This slice connects each actual acquisition body to its saved literal-return callback.

Base: `3d9a39ae5`, after the shared saved-mask checkpoint.
Changed files: `MachineWorkersSlots.lean` and `MachineWorkersConnections.lean`.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: these helpers serve the unchanged Workers log bound.
Reach: both actual acquisition sites, every job total, and supplied actual source and store premises.
`CodeAt.bound` annotates existing native success binders with their actual future callback contract.
The contract quantifies every completed-exit view and row table.
`CodeAt.frontier` retains zero source budgets as live frontiers.
Limit: no complete evaluator, command, or history closure follows.
The finalizer model still supplies no native finalizer interception contract.
Unlock: the acquired callback can require its own connection literal after the real note binder.

## Consumers

`bound_push` applies the shared saved-answer law to the actual primitive frame push.
`acquisition_body_head` supplies the common source census for annotation and push.
`literal_code` includes both positive source budgets and live zero-budget frontiers.
`acquisition_return_callback` accepts any permitted note answer and returns the source's own literal.
`acquisition_body_code` gives both source bodies their connection output classes.
`acquisition_body_push` checks the actual frame step against that annotation.
`code_sizes` and the existing exclusivity reader consume the strengthened annotation.

## Verification

With `LEAN_NUM_THREADS=3`, the following commands exit with status zero:

```sh
lake build Effect4.Laws.Machine.AnswerFlowHooks
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersConnections.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersConnections.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersExclusivity.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivity.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersConnectionsAudit.lean
```

The audit reports 246 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
These are conditional symbolic proofs, not runtime or host checks.
No runtime or host behavior changes.

## Open obligations

Actual native operations must preserve each current answer class and produce the matching post-state answer.
History must retain the binding prefix through worker creation, captured finalizers, and saved callback invocation.
The actual release start must issue one writer allowance, and the real cleanup write must consume it.
The existing pure source-history theorem supplies addresses and lexical lengths, but not these value premises.
