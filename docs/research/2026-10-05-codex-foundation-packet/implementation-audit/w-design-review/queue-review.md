# Waiting wrapper review

The cancellation cleanup handles the tested gap between registration and entering the await.
The design needs a condition on its interruptible-wait claim: the caller must enter with interruption enabled.
This is a wording correction, not a new upstream defect or a reason to reject the wrapper.

Evidence status: eight finite host cases pass, four each on Effect 4.0.0-rc.112 and 4.0.1, using Bun 1.4.2.
The observations match across both versions.
The queue definitions are copied unchanged from `composite-queue.ts`; only the review harness is added.
The retained original outputs also match each other apart from the version field.
No repository edits, builds, installations, Lean invocations, or TypeScript compiler runs occur.

## Cancellation and registration

`takeBetween` masks registration and signal delivery, then installs `onInterrupt` around the restored await.
`cancelStep` removes the stable request identity and computes the next signal.

| Control | Before interruption | After completion |
| --- | --- | --- |
| Cancel between registration and await | One registration; masked; zero hint callbacks | Target interrupted; registration removed; later messages `[1,2]` remain |
| Same gap without cancellation | One registration; masked; zero hint callbacks | Target receives `1`; message `2` remains |
| Interrupt after posting, incoming interruptible | Registered receiver; helper queued | Receiver withdraws; message `1` remains after the old helper runs |
| Same posted window, incoming masked | Registered receiver; helper queued | Receiver stays registered, then consumes `1`; its inner continuation runs; outer restoration interrupts |

The scheduler hook observes registration without changing the cell or fiber.
It requests public `Fiber.interrupt` from a separate fiber before the hint has any await callback.
This checks the protected gap omitted from the original traces.
It does not prove cleanup for every schedule.

```mermaid
sequenceDiagram
    participant I as Interrupter
    participant W as Receiver with masked caller
    participant H as Posted helper
    I->>W: Request interruption while hint wait is active
    Note over W: Request stays registered; interruption stays pending
    H->>W: Resolve hint
    W->>W: Retry consumes message; inner caller receives it
    Note over W: Outer restoration produces Interrupt
```

F3 and F5's cancellation acceptance row currently say the wait stays interruptible without qualifying the incoming mask.
F4 explicitly makes `restore` the identity under a masked caller.
The fourth control witnesses that distinction in the actual wrapper.
Smallest correction: require incoming interruptibility for immediate withdrawal, and retain the masked control as its counterpart.

## Repeated hints and helper count

Two offers before dispatch post two helpers for the same request and the same hint.
The first helper permits consumption; the second completes an already resolved hint and causes no further consumption in this case.
This supports the stated absence of coalescing, with a more precise cost: one helper per signal occurrence.
It does not imply one helper per distinct request.

F3 and `post` use one helper for each hint.
The current `wake` returns at most one hint, so these runs cover no multiple-hint step.
No helper-coalescing defect is established.

## Limits of the source probe

The probe explicitly limits itself to the cases it needs.
Its `ready` does not cap the minimum by capacity; `QueueModel.threshold` does.
For capacity one and minimum two, the source probe keeps waiting while `QueueModel` admits the buffered message.
All retained bounded-capacity host cases use minimum one, so this difference does not invalidate their outputs.
The source also omits zero-bound handling, pending offers, closing, shutdown, and rendezvous.
Its cancellation checks concern takers only; no suspend offerer registers or waits.
The first suspend-offer slice needs cancellation of an enrolled offerer and forwarding after capacity release, each with a no-cancellation control.
The source declares these limits; its retained cases stay within them.

Duplicate helpers are tested after completion, not after a receiver rearms with a fresh hint.
The old-hint-after-rearming acceptance trace remains owed.
The pure model explicitly excludes the wrapper and deferred delivery, so its checks do not close that obligation.

Anchors: `takeBetween`, `takeStep`, `cancelStep`, `wake`, `post`, and `ready` in `docs/research/2026-10-05-claude-lead/queue-probes/composite-queue.ts`.
Model anchors: `threshold`, `ready`, `take`, and `wake` in `docs/research/2026-10-05-claude-lead/queue-probes/QueueModel.lean`.
Design anchors: F3, F4, F5, and F6 in `docs/research/2026-10-05-claude-lead/waiting-design.md`.

The note has active edits at main commit `27ea7cb246191ccdec20ca4819446b2546084118`.
These findings describe the retained snapshots, not a completed amendment.
`receipt.json` pins the source, runtime, and commands; both probe commands exit zero.
`wrapper-controls.ts` and its two JSON outputs retain the executable controls and exact observations.
