# Cancellation after state consumption

Both installed Effect versions can interrupt the caller after a protected body consumes a message and reaches its result.
Restoring interruptibility delivers the pending interruption before the caller's continuation runs.
The consumed message remains absent.

Evidence: finite deterministic host probe under bun 1.4.2, using installed source entries.
Versions: Effect 4.0.0-rc.112 and 4.0.1.
All five controls pass their assertions on both versions. Their observations are identical.
No TypeScript compiler, build, installation, timer, or arbitrary fiber-state mutation runs.

## Commands

```sh
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/atomic/cancel-return/probe.mjs /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/atomic/cancel-return/rc112.json
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/atomic/cancel-return/probe.mjs /Users/pooks/.bun/install/cache/effect@4.0.1@@@1 > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review/atomic/cancel-return/v401.json
```

Both commands exit 0.
`receipt.json` records probe/output hashes and checks the rc.112 imported files against the inspected vendor bytes.
Each output records runtime/package versions, repository metadata, installed directory, and source hashes.

## Observations

| Control | State consumption | Protected body reaches result | Operation exit | Caller continuation | Caller fiber exit |
| --- | --- | --- | --- | --- | --- |
| No cancellation | Yes | Yes | Success | Entered with message | Success |
| Cancel inside `uninterruptible`, incoming interruptible | Yes | Yes | Interrupt | Not entered | Interrupt |
| Cancel inside `uninterruptibleMask`, incoming interruptible | Yes | Yes | Interrupt | Not entered | Interrupt |
| Same inner mask, caller already masked | Yes | Yes | Success | Entered with message | Interrupt when the outer mask restores |
| Cancel while waiting before consumption | No | Not reached | Not separately wrapped | Not entered | Interrupt; a later offer remains available |

The observer of `operation-exit` is an `onExit` outside the inner protected operation.
The caller continuation is the code after `yield* op`.
The final fiber exit is read separately with `pollUnsafe`.
The committed event follows the actual public `Queue.take`; it does not mutate a queue or fiber manually.

A separate fiber waits for the commit notification and calls public `Fiber.interrupt(target)`.
`Deferred.succeed` resumes that waiting fiber synchronously.
The canceller requests interruption and waits for the target's exit.
The protected target continues to its result, then restores interruptibility.
The manual scheduler disables automatic yielding; every control executes zero queued tasks.
The pre-consumption control restores interruptibility around the empty queue's wait before cancellation.

## Source explanation

In `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`:

- `FiberImpl.interruptUnsafe`, lines 574–595, records the cause while a target is masked.
- `FiberImpl.getCont`, lines 680–698, executes `contAll` while searching for the next success or failure continuation.
- `uninterruptible`, lines 4299–4310, pushes restoration when entry was interruptible.
- `setInterruptible`, lines 4312–4322, replaces the pending continuation with failure when restoring an interrupted fiber.
- `uninterruptibleMask`, lines 4340–4352, uses the same restoration frame.
- `Deferred.doneUnsafe`, `vendor/effect-4.0.0-rc.112/src/Deferred.ts:1648–1662`, invokes captured resume callbacks inline.

The same masking condition exists in `/Users/pooks/.bun/install/cache/effect@4.0.1@@@1/src/internal/effect.ts`.
The declarations are `uninterruptible`, `setInterruptible`, `uninterruptibleMask`, `FiberImpl.interruptUnsafe`, and `FiberImpl.getCont`.
That version adds `succeedWith`; it still obtains the next continuation through `getCont`.
The output's hash pins the inspected installed source.

## Recommended first Queue contract

Use a target-compatible commit boundary, subject to owner ratification.
When cancellation wins before atomic consumption, withdraw its request without consuming a message.
At atomic consumption, the operation commits its state change.
After commitment, pending interruption may reach the caller before its continuation receives the value.
Committed state remains committed.

The observation must record commitment, operation exit, continuation entry, and whole-fiber exit separately.
Do not claim that an interrupted take implies no consumption.
Do not claim that every consumed value reaches the caller's continuation.
Those stronger claims need a separate profile, adapter, and proof; masking alone does not provide them.

This contract concerns destructive queue consumption.
Permit and allocation lifetimes still need protected acquisition, installed cleanup, and scoped release.
A committed acquisition does not excuse abandoning the owned resource when interruption unwinds its scope.

The probe proves neither all-schedule behavior nor a Lean theorem.
It refutes deriving cancellation-without-consumption from masking alone on these two installed runtimes.
