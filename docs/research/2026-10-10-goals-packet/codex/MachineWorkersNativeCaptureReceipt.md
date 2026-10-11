# Workers native notes and captured slots

The original `Workers.Assertions.logs_step` remains open.
This slice checks actual note replies, acquired callbacks, registration, and selected cleanup writers under explicit slot premises.

Base: `5630b7e27`, after the shared value-pop checkpoint.
The library changes are `ScopeFields.lean` and `NativeScopeStore.lean`.
The application proofs are `MachineWorkersNativeSlots.lean` and `MachineWorkersCapturedSlots.lean`.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: shared scope-field transport serves `HeapSites.heap_sites_keep` and the unchanged Workers log bound.
Reach: existing scope rows, actual native synchronous operations, both actual acquisition sites, and every job total.
The saved acquisition callback quantifies every actual completed-exit view and row table.
The captured writer resolves the effective release destination after the stored acquisition value and exit binder.
Limit: history must supply current slot annotations, captured identities, and writer permissions.
The existing Workers model still supplies no native finalizer interception contract.
Unlock: native source ownership and exact connection captures share one scope-table census.

## Shared scope transport

`ScopeFields.Model` supplies finalizer and strategy predicates on the existing scope data.
It requires the administrative fork finalizers and sequential allocation to satisfy those predicates.
`ScopeFields.OperationAt` identifies the fields introduced by registration and allocation operations.
The shared proofs cover table replacement, registration, removal, allocation, fork, close order, every sync operation, and state-first close.

`NativeScopeStore` instantiates the model with its existing source predicates.
Every existing theorem keeps its statement.
The source module replaces 128 proof lines with applications of the shared transport.
Its full source-history and release-custody consumers rebuild successfully.

## Actual Workers consumers

`sync_root_native` checks both actual sync replies and the missing-store fallback branch.
It uses the existing store-growth theorem and the actual post-operation answer class.
`acquisition_one_note_native` and `acquisition_two_note_native` resolve actual note sources and append their own literals to the opened reference.
`acquisition_note_delivery` invokes the real saved literal-return callback and retains its older ordered stack.

`acquired_resume` consumes the connection answer class at the real saved acquired callback.
`acquired_capture` retains the five bindings and the exact connection literal in the actual capture.
`acquired_registration` applies the shared scope census to that produced capture.
`captured_close_order` retains exact capture predicates in the actual state-first close order.
`close_selected_writer` resolves a selected foreign capture to the released reference and its matching connection literal.

## Verification

With `LEAN_NUM_THREADS=3`, the following commands exit with status zero:

```sh
lake build Effect4.Laws.Machine.ScopeFields Effect4.Laws.Program.NativeScopeStore
lake build Effect4.Laws.Program.NativeReplies Effect4.Laws.Program.ReleaseCustody.Execution
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersNativeSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersNativeSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersCapturedSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersCapturedSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersNativeSlotsAudit.lean
```

The narrow library build reports 384 jobs.
The existing history-consumer build reports 600 jobs.
The audit reports 217 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
The evidence consists of conditional symbolic proofs, not bounded runtime or host checks.
No runtime or host behavior changes.

## Open obligations

The full current-code annotation must decompose actual source heads into their typed native wrappers.
History must propagate the root binding prefix through every live current frame and worker creation.
Native scoped close and finalizer interception must retain typed captured programs beyond the current model's empty finalizer function.
The actual release start must issue a writer permission, and the selected cleanup operation must consume it.
These premises remain open; the original scenario statement does not change.
