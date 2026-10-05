# Cancellation requested before consumption

The semantics registry needs decision 222's condition: “When cancellation wins before consumption.”
A cancellation request can already be pending while a masked take consumes an available message.
Request timing alone does not establish withdrawal.
This finding concerns wording, not an upstream runtime defect.

Evidence status: six finite host cases pass on Bun 1.4.2.
The installed versions are Effect 4.0.0-rc.112 and 4.0.1.
Their three case observations match exactly.
Proof role: counterexample to interpreting “cancellation before consumption” as any earlier interruption request.
Scope: one available message, one consumer, one observer, explicit synchronous scheduling, and no timer.

| Case | Consumption | Body result | Operation exit | Caller continuation | Fiber exit | Message remains |
| --- | --- | --- | --- | --- | --- | --- |
| Masked, interruption requested before take | Yes | Message | Interrupt | Absent | Interrupt | No |
| Same masked path, no cancellation | Yes | Message | Success | Receives message | Success | No |
| Unmasked, interruption requested before take | No | Absent | Interrupt | Absent | Interrupt | Yes |

```mermaid
sequenceDiagram
    participant C as Masked consumer
    participant I as Separate interrupter
    participant Q as Queue with one message
    C->>I: Complete before-take notification
    I->>C: Request interruption
    Note over C: Pending interruption; mask remains active
    C->>Q: Take
    Q-->>C: Message consumed and returned inside mask
    Note over C: Restoring interruptibility produces Interrupt
    Note over C: Caller continuation does not run
```

The probe uses public `Fiber.interrupt`, `Deferred.succeed`, and `Queue.take` operations.
The before-take event reads the pending interruption and mask fields without changing them.
This diagnostic confirms the interruption already exists before the actual take.
The final `Queue.poll` checks the remaining message independently.
All cases execute zero queued scheduler tasks; deferred completion resumes the observer synchronously.

`operation-exit` observes an `onExit` outside the protected operation.
`body-result-ready` observes the successful take inside that operation.
These observations distinguish the body result, the operation exit, the caller continuation, and the final fiber exit.

The available-message case enrolls no queue waiter.
It therefore does not establish a defect in a waiting wrapper or a race after queue registration.
If “cancellation” already means accepted withdrawal, the semantics registry could be read consistently, but that condition needs to remain explicit.

Smallest correction: restore “when cancellation wins before consumption” in `waiting-request-obligation-preserved` under R11.
Keep the existing rule that committed state remains committed after consumption.
No new design choice is required.

The reviewed declaration is in `/Users/pooks/Dev/lean4-effect4/tools/Tools/SemanticsRegistry.lean`.
Its cited authority is decision 222 in `/Users/pooks/Dev/lean4-effect4/docs/core/decisions.md`.
`wording.json` retains both exact statements and `receipt.json` pins their hashes and the main commit.

Source anchors:

- `FiberImpl.interruptUnsafe` records interruption while masked in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
- `fiberInterruptAs` calls that method before awaiting the target's exit in the same file.
- `uninterruptible` installs restoration; `setInterruptible` delivers the pending interruption when restoring interruptibility in the same file.
- `doneUnsafe` invokes captured resume callbacks synchronously in `vendor/effect-4.0.0-rc.112/src/Deferred.ts`.
- `take` calls `takeUnsafe`, which removes an available message, in `vendor/effect-4.0.0-rc.112/src/Queue.ts`.

`source-cites.json` retains excerpts, exact installed paths, and source hashes for both versions.
The imported rc.112 runtime, deferred, queue, and fiber source bytes match the corresponding vendor files.

`commands.txt` records both exact probe commands; each exits 0.
`rc112.json` and `v401.json` contain all events, versions, source hashes, exits, and remaining messages.
`probe.mjs` retains the deterministic scheduler and assertions.
No repository edit, build, installation, TypeScript compiler, or Lean invocation occurs.
The result proves neither all-schedule behavior nor a Lean theorem.
