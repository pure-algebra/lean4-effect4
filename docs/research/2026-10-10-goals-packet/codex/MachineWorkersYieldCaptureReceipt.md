# Workers yield and captured cleanup

The original `Workers.Assertions.logs_step` remains open.
The slice proves conditional current-frame and writer consumers, without supplying their whole-history premises.

Base: `abede52eb`, after the shared `AnswerFlowFrames` checkpoint.
The changed files are `MachineWorkersSlots.lean`, `MachineWorkersConnections.lean`, and their audit reader.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: these helpers serve the unchanged Workers log bound.
Reach: existing native primitive frames, both actual acquisition sites, every job total, and supplied actual store and source-slot premises.
The forced-yield class retains the owner phase and exact reference and deferred-store lengths.
Each captured writer uses the effective release destination after the acquired-value and exit binders.
Limit: no complete current-code, evaluator, command, or history closure follows.
The writer bound still needs captured-value ownership and a write allowance from the actual release start.
Unlock: shared constant-frame laws support transient initializer yields, and real cleanup commands consume the retained slots.

## Checked consumers

`code_sizes` transports current annotations only when the owner and allocation sizes agree exactly.
`yield_saved`, `yield_push`, and `yield_resume` use the actual constant-frame push and pop.
`yield_native` checks the actual parked unit-response producer in its unchanged store.
`phase_does_not_retain_yield` retains the finite weaker-phase control.
That control refutes no history or funding theorem.

`acquisition_one_env` and `acquisition_two_env` recover exact environments from the existing lexical predicate and five-value prefix.
The second environment retains its additional previous answer.
`acquisition_one_answer` and `acquisition_two_answer` check the actual literal-return source addresses.
`captured_one_writer` and `captured_two_writer` resolve actual captured release destinations to the second reference and correct connection literal.
`captured_one_command` consumes the first destination at a real native command boundary.
It retains other fibers and the unfinished command suffix.

## Verification

With `LEAN_NUM_THREADS=3`, the following commands exit with status zero:

```sh
lake build Effect4.Laws.Machine.AnswerFlowFrames
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersConnections.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersConnections.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersExclusivity.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivity.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersConnectionsAudit.lean
```

The audit reports 216 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
The source, native operation and command proofs are conditional symbolic proofs.
The weaker-phase control is a finite response-class control.
No runtime or host behavior changes.

## Open history obligations

History must preserve every live current annotation, including forced-yield response sizes.
Actual source callbacks must retain the five bound values and return the acquired literal to the registration callback.
The active cleanup writer must consume one allowance issued by its actual release start.
The existing pure source-history theorem supplies source addresses and lexical lengths, but does not supply these value premises.
