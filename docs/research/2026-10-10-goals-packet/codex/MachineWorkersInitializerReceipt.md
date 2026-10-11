# Actual Workers initialization

The original `Workers.Assertions.logs_step` remains open.
The checked source and allocation consumers do not supply whole-history slot ownership.

Base: `93f4523d5`.
The slice changes `MachineWorkersSlots.lean` and adapts `MachineWorkersExclusivity.lean` to this worktree's existing native fiber type.
The fiber type is definitionally the type used by the coordinator's later `Moves.NFiber` alias.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: these helpers serve the unchanged `Workers.Assertions.logs_step`.
Reach: the actual loaded Workers source, its first five allocation binders, and their real native callbacks.
The statements quantify every job total, table, owner, saved suffix, and permitted future store.
Positive source-budget premises expose the compiled allocation.
Smaller source budgets remain live frontiers.
Limit: the current-code contract has no complete evaluator, command, or history preservation theorem.
Initialization exclusivity follows only after a history supplies every live frame contract.
Unlock: exact allocation answers extend the concrete five-value prefix before any worker starts.

## Consumers

`load_frames` proves the actual loaded root contract.
`initializer_head` checks the first four allocation source heads for every total.
`initializer_source_push` consumes those heads at the actual frame push.
`initializer_native` supplies the actual post-allocation answer class.
`initializer_resume` consumes that answer at the actual saved binder pop.
`gate_native` and `gate_callback` establish the later store bounds and the concrete gate key.
`stable_bind_saved` retains the five values through a source binder under its effective destination premise.
`MachineWorkersExclusivity.other_exited` consumes `code_phase` and the actual distinct stored identities.

## Verification

The following commands run with `LEAN_NUM_THREADS=3` and exit with status zero:

```sh
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersExclusivity.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivity.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineAnswerFlowAudit.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivityAudit.lean
```

The slot audit reports 161 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
The combined live-owner audit reports 167 declarations within the same budget, zero modulo planned goals, and zero planned goals.
These are conditional symbolic proofs.
No runtime or host behavior changes.

## Remaining obligations

Execution must preserve current source phases, including copied forced-yield bodies before the gate allocation.
Every worker capture must retain the five bound values and its acquired connection literal.
Each cleanup write must consume an allowance issued by its actual release start.
The original log bound remains open until those obligations close through actual history.
