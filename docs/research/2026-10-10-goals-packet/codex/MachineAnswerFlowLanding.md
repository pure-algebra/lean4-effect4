# Shared saved-answer contract

The coordinator must add `Effect4.Laws.Machine.AnswerFlow` to the Laws root.
The original Workers log clause remains open.

Base: `ae99c2649`.
The shared contract moves from the checked research probe into `src/Effect4/Laws/Machine/AnswerFlow.lean`.
The research file becomes an import reader.
`MachineWorkersSlots.lean` adds the actual post-allocation binder consumer.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: these helpers serve the original `Workers.Assertions.logs_step`, Atomic cleanup writes, and Timeout cleanup ordering.
Reach: existing primitive frames and actual ordered saved stacks, under supplied state-indexed value and cause predicates.
The model types the actual installed finalizer program separately from pure frame callbacks.
The Workers consumer uses the actual source callback and native allocator.
Limit: no complete pop, evaluator, command, or history preservation follows from this slice.
Initialization ownership, captured binding values, acquired identities, and cleanup write permission remain open history obligations.
Unlock: the application instances share the same checked saved callback and resumption laws.

## Checked consumers

`AnswerFlow.resume_success` describes the actual `FrameFiber.resumeValue` pop.
It requires the incoming value class, provided exit class, saved callback contract, and absence of deferred interruption.
It preserves the actual older suffix and records the actual pop event.
`MachineWorkersSlots.initializer_resume` consumes this law at each of the first four source allocation binders.
It checks the callback in the post-operation store, with the exact returned cell key.

## Verification

With `LEAN_NUM_THREADS=3`, `lake build Effect4.Laws.Machine.AnswerFlow` passes all 174 jobs.
The research import reader and updated Workers slot consumer compile independently.
`lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAnswerFlowAudit.lean` passes.
The audit covers the shared library module and the actual Workers consumers.
It reports 129 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
No runtime, target, compiler, or host behavior changes.
