# State-indexed saved answers

The coordinator must retain the open history premise.
The checked initializer consumes a current source stage; it does not establish that stage from execution.

Base: `71b5b51ba`.
The slice changes `MachineAnswerFlow.lean`, `MachineWorkersSlots.lean`, and `MachineAnswerFlowAudit.lean` in this directory.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: the helpers serve the unchanged `Workers.Assertions.logs_step` in `Test/Dogfood/Scenario/Workers/Assertions.lean`.
The shared contract also serves Atomic cleanup writes and Timeout cleanup ordering.
Reach: the existing primitive frame, its actual ordered saved list, and an explicitly supplied future-state relation.
The Workers instance retains the actual fiber owner and Stores.
The native allocation consumer uses the actual `evaluateNative` equation.
Limit: no source-history closure, initialization exclusivity, cleanup write permission, progress, or host agreement follows.
Unlock: an actual saved initializer can consume the returned cell identity after the store changes.

## Checked structure

`AnswerFlow.Model` supplies state-indexed value, cause, and current-code predicates.
`SavedAt` checks callbacks in each permitted future state.
`StackAt` composes those checks through the actual saved list.
`FrameAt` joins the current input class to that list.
The native finalizer hook types the installed program separately from a pure frame arm.

`MachineWorkersSlots.RootStage` retains the source path, binding prefix, owner, and transient store lengths.
`Phase` requires the root owner or the stable allocation lengths.
`code_phase` reads this condition from each current-code constructor, including returned values and failures.
`initializer_callback` invokes the actual source `contA` callback at every total, view, and table.
`initializer_saved` applies the shared contract to that callback.
`initializer_native` consumes the actual native reference allocation and proves its returned frame contract.

## Verification

Run in the managed machine-structure worktree, with `LEAN_NUM_THREADS=3`:

```sh
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineAnswerFlow.olean docs/research/2026-10-10-goals-packet/codex/MachineAnswerFlow.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAnswerFlowAudit.lean
```

Each command exits with status zero.
The audit reports 127 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
These are symbolic conditional proofs, not bounded execution checks.
No runtime, target, compiler, or host behavior changes.

## Open obligations

The actual history must establish the initial source stage and exclude competing initializers.
The gate allocation must move the root into the stable phase before any fork.
Workers must retain its five binding values through callbacks, child initialization, and captured releases.
The acquired value must retain the actual worker identity.
The cleanup writer must consume one allowance issued by its actual release start.
The shared contract has no complete native evaluator or history transport theorem yet.
The original `logs_step` remains open.
