# Catalogue scout receipt

The catalogue must separate pure steps from operations and module laws.
PartitionedSemaphore cannot reuse Semaphore's take, visit or withdrawal steps.
The finite controls distinguish their reservation and delivery choices.

Evidence status: source inspected and finite controls checked.
Base and head: `01c83fbc0f319999faf9a9ab306137a95f6dd303`.
Branch: `codex/catalogue-scout-20261008`.
The scout changes no production file and runs no sweep.
Catalogue work waits for Claude's C2 rename to Library.

## Controls

Run from this checkout:

```sh
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-catalogue-scout-controls/ExistingSemaphore.lean
bun docs/research/2026-10-08-catalogue-scout-controls/host-values.ts
bun docs/research/2026-10-08-catalogue-scout-controls/host-waits.ts
```

Each command exits 0. Bun reports version 1.4.2.
The TypeScript probes execute latest (Effect 4.0.1) from its vendored source.
No TypeScript compiler or type check runs.
The Lean file contains finite guards, with no theorem or axiom claim.
The host probes observe one selected run, with no fairness or whole-module claim.
The first probe logs values. The second asserts its expected finite observations.
Its 20ms waits allow callback delivery; they establish no bound on every schedule.

| Control | Existing Semaphore | Latest PartitionedSemaphore |
| --- | --- | --- |
| Capacity 2, hold 1, request 2 | free count remains 1 | available becomes 0 |
| Interrupt that waiting request | no partial holding exists | available returns to 1 |
| Capacity 3, hold 3, enqueue A1=2, A2=1, B1=1, release 2 | first visit selects A1 | B1 completes first |
| Then release 1 twice | not compared as a run | A1 completes, then A2 |

Latest's completed plain take retains its permit after a later client failure.
The probe initially expected a refund there and failed with available 1 instead of 2.
The corrected control retains this observed value.
`onExitUnsafe` protects its current evaluation, not the whole later client.

PubSub's finite capacity-one control observes no retention without subscribers.
With two subscribers, one poll leaves size 1; the second poll leaves size 0.
SynchronizedRef's failed client leaves value 4 and allows the next modification to store 5.

## Ref: a small first slice

`Ref.modify` calls its pure callback once, stores the second result, and returns the first.
`Ref.modifySome` keeps the previous value when the optional result is absent.
The independent model must state these equations without reading Step.
Use the existing native Ref forms; do not add another cell operation family.

A Step callback is data. Its term feeds `Ref.modifyWith` or its native siblings.
`Step.getOrElse` handles optional new values with the old value as fallback.
No new option eliminator is required for these value equations.
The domain contains checked pure Step callbacks, not every JavaScript callback.
Throwing, reentrant mutation and external closures remain outside that domain.

Suggested first slice: generic checked value types A and B; make, get, setAndGet,
getAndSet, modify, getAndUpdate and optional-update value equations.
Give one caller example using named inputs and minted binders through the existing forms.
Add callback captures to that example, so scope alignment is exercised.
The callback body remains first-order Term within Eff.

`Ref.set` needs a named observation before inclusion.
Latest declares `Effect<void>` but returns its backing MutableRef at runtime.
The current native row answers a Ref handle.
The host probe distinguishes the backing object from the outer Ref object.
That result establishes neither a target type check nor an invalid handle correspondence.
A wrapper that discards the reply can match the declared void observation.
Any changed native-row contract requires its own reviewed amendment.

G1 remains open for an operation's atomic wrapper law.
G10 remains open for client traces across schedules.
Unsafe constructors and reads are outside the Eff-operation slice.
G2 and G3 describe missing authoring conveniences, not unavailable Ref transitions.

## PartitionedSemaphore: correct the brief

Latest uses one shared capacity, not one semaphore per key.
A waiting request consumes the currently free permits before it registers.
Release distributes one permit to the oldest waiter of each visited partition.
The iterator persists across releases, deletion and reinsertion.
Cancellation removes the request and refunds every permit it already reserves.
A wake completes that request; it does not ask the request to take everything again.

The model needs shared available, total waiting, ordered partitions, ordered requests,
remaining need, original request size, and a persistent iterator position.
Deletion and reinsertion need generation or insertion information sufficient to transcribe Map iteration.
The model transcribes the source independently of Step.
Client calls and interruption remain observable under decisions rows 330 and 333.

Start with natural-number keys and finite natural capacities.
Allow zero capacity; latest allows it, while Semaphore.make refuses it.
Mark fractional, negative, infinite and NaN counts outside this first profile.
Write tryTake, available, bounded enrolment and single-permit release as pure steps first.
Use waiter identities separately from partition keys and hints.
Do not call one selected service order fairness.

| Operation or property | Gap or missing condition |
| --- | --- |
| General key K lookup | New gap: Step has natural equality and deferred equality, not generic key equality |
| General releaseUnsafe count loop | New gap: Step folds input lists but has no numeric repetition builder |
| take and release delivery | G1; reservations require waitAnswer semantics, not waitRetry |
| interrupted partial take | G1; refund and wake records must be part of withdrawal |
| withPermits, withPermit, withPermitsIfAvailable client observation | G5 |
| their exit cleanup | G1 and G10; protectedBy typing alone proves no cleanup run |
| request-to-hint correspondence | G9 when represented through an identity table |
| order under registration, removal and resumed requests | G10 |
| progress or starvation exclusion | G10 plus explicit readiness and fair-schedule premises |

The numeric-loop finding concerns the direct source transcription.
It proves no impossibility for every alternative encoding.
A bounded literal count can unroll steps; its profile and bound must be explicit.
A wider count profile needs a new builder or an independently justified allocation algorithm.

## PubSub pressure test

Use a bounded, positive natural capacity with no replay first.
The model keeps message order, active subscriber cursors, pending poller order,
publisher groups, final-message state and shutdown state.
Each buffered message holds until every relevant subscriber consumes or unsubscribes.
No subscriber means publish succeeds without retaining that message.
A new subscriber starts at the current publisher position.

Pure steps can describe subscribe, poll, publish, removal, dropping and sliding.
A list of independent subscriber queues needs a proved shared-capacity connector.
It cannot silently replace the source's shared message retention rules.
Backpressure tracks a publisher group's final marker and shared deferred identity.
Cancellation removes the entire publisher group, not just its current item.

Blocked operations: subscribe and shutdown need G7 as well as G1.
Take, takeAll and takeBetween need G1 for pending pollers and interruption.
Publish and publishAll need G1 for surplus completion and publisher cleanup.
End needs G1 for waking pollers and pending publishers without occupying capacity.
Replay is an explicit omitted profile, not covered by those pure steps.
Subscription identities need G9; public behavior across schedules needs G10.

## SynchronizedRef pressure test

Pure modify still runs inside a Semaphore permit.
A pure value equation does not establish serialization or release at an exit.
The independent model allows the old value to remain visible during a pending client.
It writes the new value only after client success.
Failure and interruption keep the old value and release the permit.
An unsynchronized get does not acquire the lock.

Author an effectful callback as an existing stored definition with captures.
Pass the old value through its declared parameter and call it through `Def.invoke`.
Compose the call with Ref.get and the commit under `Semaphore.withPermits`.
No second program IR or host closure enters stored syntax.
This authoring composition is possible today; its client-aware law remains G5.

Blocked claims: all effectful-update operations need G5; all locked-operation laws need G1 and G10.
Identity relations for two allocated backing cells need G9 where represented by a table.
Include a paused callback, a competing modify, a failing callback and an interrupted callback.
Retain ordered client host requests, as row 333 requires.

## Placement before proof work

Each assigned claim must receive AGENTS.md's five placement fields before its statement.
Ref value connectors serve `translation-simulation`, R10, under the pure-Step callback profile.
Step typing serves `store-typing`, R3, through the existing `step-language-typed` claim.
Reservation and delivery claims serve `reactive-scheduling`, R10, with admitted tapes and explicit identities.
Subscription finalization serves `scope-lifetime-finalization`, R10, with interruption retained.
Client host-call observations serve `host-session-protocol` and `translation-simulation`, R10.
These placements are proposed; no new registered theorem is claimed here.

## Source anchors

Declarations are the citation authority; ranges below aid this scout's source inspection.

| Declaration | Path | Inspected range |
| --- | --- | --- |
| Ref.modify, modifySome, updateSome, updateSomeAndGet | vendor/effect-4.0.1/src/Ref.ts | 895–901, 1158–1163, 1501–1508, 1638–1646 |
| Ref.set; MutableRef.set | vendor/effect-4.0.1/src/Ref.ts; vendor/effect-4.0.1/src/MutableRef.ts | 306–307; 1063–1070 |
| PartitionedSemaphore.makeUnsafe and its releaseUnsafe, take, withPermits, tryTake | vendor/effect-4.0.1/src/PartitionedSemaphore.ts | 117–309 |
| MutableHashMap iterator | vendor/effect-4.0.1/src/MutableHashMap.ts | 91–95 |
| PubSub.subscribe, unsubscribe, pollForItem, shutdown, endUnsafe | vendor/effect-4.0.1/src/PubSub.ts | 1579–1613, 1714–1735, 791–799, 1019–1040 |
| BoundedPubSubSingle.publish and BoundedPubSubSingleSubscription.poll, unsubscribe | vendor/effect-4.0.1/src/PubSub.ts | 2573–2587, 2649–2680 |
| BackPressureStrategy.handleSurplus, offerUnsafe, removeUnsafe | vendor/effect-4.0.1/src/PubSub.ts | 3022–3040, 3078–3097 |
| SynchronizedRef.modify, modifyEffect, getAndUpdateEffect | vendor/effect-4.0.1/src/SynchronizedRef.ts | 484–489, 538–552, 295–305 |
| onExitUnsafe | vendor/effect-4.0.1/src/internal/effect.ts | 4215–4224 |
| Step | src/Effect4/Modules/Step.lean | declaration named above |
| Ref native authoring forms | src/Effect4/Program/Authoring/Rows.lean | declaration named above |
| NativeOp.row refSet; refStep | src/Effect4/Program/Native.lean; src/Effect4/Machine/Stores.lean | declaration named above |
| Semaphore.Model.take, visit, withdraw | src/Effect4/Laws/Modules/Semaphore/Model.lean | declaration named above |
| waitRetryAt, waitAnswer, protectedBy | src/Effect4/Modules/Waiting.lean | declaration named above |

Latest source SHA-256 values:

```text
Ref.ts 69dc695dbe042baec090178dcc261f9a171e15a9fe6034d1c479408d6369d8fc
PartitionedSemaphore.ts a279af38dd80b386c651ba5665ed0c2481e921dab8cd65addaad686df4595a80
PubSub.ts ab512549c7f76d9a7df8e953268e377eecdbad6ce985a29b03dcd91b596da758
SynchronizedRef.ts 6bbf0416d762fc38365600de74985809e822958ee4ed1e35afe375873c5bf3cb
```

Changed files: this receipt and the three controls beside it.
No source theorem lands; no axiom output is owed or claimed.
Open obligations are the gap table and the proposed placements above.
