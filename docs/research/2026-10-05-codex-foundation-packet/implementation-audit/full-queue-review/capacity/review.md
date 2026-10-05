# Zero-capacity Queue and API-boundary review

Keep the selected refusal of `dropping(0)`. Replace its rationale: a hand-over is not necessarily a reservation.
The first Queue profile chooses a particular commitment and delivery protocol; it does not rule out every zero-storage nonblocking queue.

Proof role: contract review and target-behavior evidence.
Evidence status: source inspection and finite runtime controls; no Lean proof.
Scope: contract at `a3954d03f2787b856e4f13c6eb63573cac885e34`, installed rc.112 and 4.0.1, default runtime under Bun 1.4.2.
The coordinator reports owner acceptance of the three choices; this review does not reopen the capacity refusal.

## Findings

### 1. Correct the reason for refusing dropping at zero

In 4.0.1, `offer` calls `offerUnsafe` in the installed `src/Queue.ts`.
Its zero-capacity branch appends the message and invokes `releaseTakers` synchronously.
A ready taker can retry and consume before the offer returns.
The independent control records `before offer`, `receiver got 7`, then `offer returned true`, with final size zero.
That run exhibits completed consumption, rather than a reserved message awaiting a later taker step.

A different abstract contract could atomically match a waiting producer and consumer, commit both outcomes, and deliver their replies later.
It would need explicit arbitration against withdrawal and the oldest eligible request.
It must leave no buffered message, pending offer, or duplicate claim after commitment.
Before commitment, winning withdrawal must prevent that match; afterward, cancellation cannot undo it.
These conditions do not establish that native Effect implements that contract in every case.

The current project instead posts hints and commits consumption at the taker's own later step.
A nonblocking dropping offer cannot wait for that future step.
Supporting useful dropping-at-zero therefore needs a separately selected matching protocol or different timing.
An always-refused zero-capacity dropping queue is another consistent choice, but it is not the selected profile.

Suggested replacement for proposal 2's reason:

> Refuse dropping at zero in this profile. Its nonblocking hand-over needs a separate commitment protocol from the selected posted-hint rendezvous.

As an independent reference contract, Java SE 25 `SynchronousQueue` has no storage and lets nonblocking `offer` succeed for a waiting receiver.
Its optional FIFO policy further separates ordering from storage capacity.
This demonstrates a coherent alternative; it proves no Effect agreement.
[Oracle API, class description and offer](https://docs.oracle.com/en/java/javase/25/docs/api/java.base/java/util/concurrent/SynchronousQueue.html#offer(E)).

### 2. Zero-capacity behavior differs across operations, not only releases

| Control | rc.112 | 4.0.1 |
| --- | --- | --- |
| Dropping single offer, no receiver | false | false |
| Dropping single offer, waiting taker | false; taker waits | true; taker consumes before offer returns |
| Dropping single offer, waiting peeker | false | true; peek returns, message remains, size one |
| Dropping `offerAll([7])`, waiting taker cancelled before wake | accepts; size one remains; later poll returns 7 | same |
| Sliding single offer at zero, waiting taker | true; size one; taker remains parked after settling | same |
| Sliding `offerAll([7])` at zero | empty remainder; size zero; taker waits | same |
| Sliding single offer at capacity one | receiver gets 7; size zero | same |
| `flush` after the parked sliding-zero case | API absent | receiver gets 7 immediately; size zero |

The dropping batch control extends D3 to the dropping strategy.
It also prevents generalizing D4's direct hand-over to the entire dropping API.
The peeker control shows that the native taker set includes nonconsuming readers.
Therefore its size is not a count of committed consuming matches.

The inspected source explains these outcomes:

- `offerUnsafe` handles sliding overflow without scheduling or running `releaseTakers`.
- `offerAllUnsafe` trims sliding batches back to capacity, including zero, and schedules a wake.
- At zero, `offerAllUnsafe` counts entries in `state.takers` as available room and appends before its posted wake.
- `releaseTakers` calls each ready callback; it does not represent one atomic two-party transaction.

### 3. Keep upstream classification narrower than the project contract

D5 remains a reproducible candidate on 4.0.1: an accepted single message and a ready waiting taker coexist without notification.
The capacity-one and batch controls narrow it to the sliding-zero single-offer path.
The successful 4.0.1 flush confirms that the waiting consumer can receive that stored message.

The exposed buffer at zero is a separate contract question.
The project selected zero-storage rendezvous; that selection alone does not establish an upstream promise.
`make` accepts the supplied capacity without a positive-capacity check in the inspected sources.
Report the operation asymmetries and exact traces, rather than assuming undocumented zero-capacity semantics.
Call this a current upstream defect only after the coordinator's latest-release check confirms the relevant behavior remains.

### 4. Refusing flush and Unsafe is a profile boundary

The refusal of `flush` is coherent with a posted-only Queue profile.
In 4.0.1, `flushUnsafe` invokes `releaseTakers`, and `flush` wraps that call in an Effect.
It is a public effectful timing operation; it cannot be replaced by a no-op while claiming its behavior.
The absence of a corresponding synchronous wake pass in the proposed implementation explains the refusal.

The Unsafe family performs host operations directly, outside the selected effectful invocation surface.
That is a valid admission boundary, not a claim that every Unsafe operation is impossible to model.
For example, `sizeUnsafe` and `isFullUnsafe` are reads; other members mutate state or release consumers.
Keep the refused names explicit, and keep `flush` separate from that host-function explanation.

## Obligations if the zero-capacity profile grows later

No new theorem is needed merely to retain the selected refusal.
Any later matching extension belongs under R10's `queue-expansion-agrees`, concept `translation-simulation`, with the zero-capacity Queue as consumer.
Its premises must name formed states, strict request order, the selected commit actor, withdrawal arbitration, and delivery policy.
Observe both commitments, queue contents, replies, caller entry, and fiber exit.
Exclude native agreement, eventual service, and successful return of every committed value until separately established.
The immediate prerequisite is an owner-selected matching contract, before changing the current formation rule.

## Receipt

`probe.mjs` imports absolute installed source paths and writes `rc112.json` and `v401.json`.
Both runs exit zero: sixteen assertions on rc.112 and nineteen on 4.0.1.
`probe-dist.mjs` repeats the same cases through the installed compiled modules.
Both compiled-module runs also exit zero with the same assertions and identical result objects.
Their separate outputs are `rc112-dist.json` and `v401-dist.json`; all four runs retain their original results.
Every waiting receiver is interrupted during cleanup; no run waits for an unavailable message.
The scheduler is the ordinary runtime, with eight explicit yields for settling; these are finite schedules, not fairness proofs.

The rc.112 runtime `Queue.ts` is byte-identical to `vendor/effect-4.0.0-rc.112/src/Queue.ts`.
SHA-256: `dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35`.
The installed 4.0.1 `Queue.ts` hash is `6781fd0ac6fad03057ebeaa838d0f9723913027a4f6845d57dc3c17da70d1953`.
The manifest versions and imported Effect/Fiber/internal runtime hashes are retained with the results.
The compiled-module results also retain the hashes of their imported files.
The implementation may have changed after these releases; the latest-release audit belongs to the coordinator.
No evidence here establishes that 4.0.1 is the latest published release.

No install, build, generator, Lean execution, active-repository write, UI action, or external message ran.
