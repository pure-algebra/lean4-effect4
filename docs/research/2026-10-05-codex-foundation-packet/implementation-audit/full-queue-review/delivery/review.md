# Full Queue contract: delivery, cancellation, and nonblocking consumers

The selected policies fit together after two cancellation statements are corrected.
Posting an offer's reply delays its caller, not the acceptance already committed by another step.
The owner has authorized the choices through the coordinator; this receipt requests no further approval.

Reviewed HEAD: `a3954d03f2787b856e4f13c6eb63573cac885e34`.
The last check finds no unstaged changes in the two reviewed notes.
No repository edit, Lean command, build, generator, or installation runs.
Four bounded native controls run on each installed version through both source and distribution entries, with bun 1.4.2.
Every assertion passes; the source and distribution observations agree for each version.

## Sources

- The note and model: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-05-claude-lead/queue-contract/queue-contract.md` and `QueueContract.lean` beside it.
- The waiting wrapper: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-05-claude-lead/waiting-design.md`, F5.
- The rulings: `/Users/pooks/Dev/lean4-effect4/docs/core/decisions.md`, rows 219–222, 230, 235, 238, and 239.
- Retained native comparisons: `native-differences.ts`, `native-differences.rc112.out`, and `native-differences.v401.out` beside the contract.
- Pinned implementation: `/Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112/src/Queue.ts`.
- Released implementation: `/Users/pooks/.bun/install/cache/effect@4.0.1@@@1/src/Queue.ts`.
  Its package reports Effect 4.0.1 and repository `Effect-TS/effect`, directory `packages/effect`.
  The new probe outputs record source hashes and the exact imported package paths.

## 1. Posted offer replies: accept, with the commitment kept separate

`acceptLoop` moves pending messages into the buffer and removes a fully accepted offer.
It emits `Note.offered true` or `Note.left []` in that same pure transition.
Only delivery of that decided reply is posted.
The offerer does not retry acceptance when its helper runs.
This is the right distinction from a taker's `Note.again`.

The native `releaseCapacity` also accepts before notifying, but invokes the offerer's resume inline.
The retained D1 result is `[1, 2, some(3)]` on both versions.
The contract predicts `[1, 2, none]` because the producer cannot start its next offer before receiving the posted reply.
That contract result remains a source reading; no suspended-offerer composite has run.

The helper must capture the reply decided by the committing step.
It must not recompute acceptance from the later queue state.
Extend the waiting sketch's `post d unit` to a typed reply payload for offers and batches.
This uses the same detached fork; it needs no new program representation.

### Correction A: the old cancellation acceptance case has the wrong boundary

Waiting-design F5 still requires a blocked offerer's message to be absent when cancellation precedes its posted hint.
That is false when the room-freeing step already accepted the message.
Replace it with these paired cases:

| Sequence | Required result |
| --- | --- |
| Capacity one contains `1`; offer `2` waits; cancel that offer; take `1` | No `2` is accepted; the queue is empty |
| Same initial state; take `1` first, accepting `2` and posting success; cancel before the helper runs | `2` remains accepted; the offerer may exit interrupted before observing success |
| Same second case without cancellation | The helper delivers success, and `2` remains available to a consumer |

Record acceptance, the operation's exit, caller continuation, and fiber exit separately, extending row 222 to offers.
Cancellation of a batch removes only its unaccepted suffix.
It does not promise all-or-nothing batch acceptance.

### Correction B: a missing pending entry does not prove acceptance

Queue-contract F8 says that a missing offer entry means its messages were accepted.
`shutdown` is a direct counterexample in `QueueContract.lean`.
It removes pending entries and emits `offered false` or `left remaining`.

Use this regression: capacity one contains `1`; offer `2` waits; shutdown removes it and posts `false`.
Cancellation before that reply leaves no pending entry, but `2` was never accepted.
For a partly accepted batch, shutdown reports only its unaccepted suffix and drops buffered messages under the shutdown policy.

Replace the inference with: withdrawal removes only a still-pending remainder; absence alone does not classify the offer's outcome.
Accepted messages are not rolled back by withdrawal.
The decided reply remains the payload of its outstanding notification.

### Native batch control, newly checked

Both versions produce the same results under a manual scheduler with automatic yielding disabled:

| Control | Result |
| --- | --- |
| Capacity two; `offerAll [1,2,3,4]`; take `1`; cancel the still-waiting producer | Producer exits interrupted; `clear` returns `[2,3]`; unaccepted `4` is absent |
| Same batch; take `1`, then `2`; do not cancel | Producer succeeds with `[]`; `clear` returns `[3,4]` |

These finite native runs support prefix acceptance and suffix withdrawal.
They do not test the proposed posted offer reply or prove its wrapper law.

## 2. Strict `poll` and `clear`: accept, with precise result meanings

`poll` and `clear` consume only when `takers` is empty in the model.
They never enrol themselves or displace the oldest waiting taker.
Their empty answers therefore mean no message is available to that operation under the order policy.
They do not imply that the buffer is empty.

Minimum contract cases:

- With `[1]` buffered and a waiting batch minimum of three, `poll` returns none and `clear` returns `[]`; size remains one.
- After withdrawing that earlier taker, `poll` returns `1`; an uncancelled earlier taker keeps its turn.
- When `clear` is eligible, it returns the buffer prefix present at its step.
  Pending offers can immediately refill the freed room, so a successful `clear` need not leave size zero.
- In a done queue, `poll` returns none for every end; `clear` returns `[]` for clean end and propagates other ends.

The retained D6 checks native `clear` bypassing the waiting batch.
The new poll control checks the parallel difference directly.
On both rc.112 and 4.0.1, native `poll` returns `some(1)` while the earlier batch remains pending.
With no earlier taker, the positive control also returns `some(1)`.
`poll` calls `takeUnsafe`, which does not test waiting takers, in each implementation.
The contract's `pollRules` expects none in the contended case.
Record `poll` alongside `clear` in the signed difference table.

## 3. `flush` and `Unsafe`: accept the exclusion

The release's `flush` directly invokes `releaseTakers` through `flushUnsafe`.
That changes when receivers run and bypasses the selected posted-only delivery contract.
Refusing it avoids adding another delivery profile to this first surface.
The host-function `Unsafe` family remains outside the admitted application interface.

Freeze the exclusion in the application signature and profile support check, not only in prose.
Use located refusals for these public source names:
`flush`, `flushUnsafe`, `offerUnsafe`, `offerAllUnsafe`, `takeUnsafe`, `failCauseUnsafe`, `endUnsafe`,
`shutdownUnsafe`, `sizeUnsafe`, and `isFullUnsafe`.
Their exclusion does not prohibit an implementation from using internal pure transition functions.
It does not claim those host functions are inherently impossible to model.

## Staged obligations

| Stage and existing destination | Required statement and consumer | Premises, observation, and exclusions |
| --- | --- | --- |
| First positive-capacity Queue; `waiting-request-obligation-preserved`, reactive-scheduling R11/R12 | Keep each decided offer reply until accepted by its receiver or rendered irrelevant by cancellation | Request identity, pending suffix, captured reply and helper ownership; no inference from missing entry alone; not eventual delivery without scheduler premises |
| First Queue; `queue-expansion-agrees`, translation-simulation R10 | Relate offer acceptance and eventual reply separately, and enforce strict `poll`/`clear` | Admitted wrapper and selected profile; rows 219–222, 230, 235, 238; no native Queue equality on the signed differences |
| Batch slice; abstract Queue state laws serving the same agreement claim | Acceptance is an ordered prefix; withdrawal removes only the pending suffix; shutdown's reply is the unaccepted suffix | Fresh request identities and formed reachable states; trace individual acceptance steps; no all-or-nothing batch or liveness claim |
| First application signature; profile support | Refuse `flush` and the named host functions while accepting the declared Queue operations | Exact names and paths in the source/profile interface; no claim of full native API coverage |

These are refinements of the existing placed obligations, not new proved results.
The first slice still supplies concrete goals over its own definitions.
The implementation should first add the single-offer before/after-acceptance pair, then batch suffix and shutdown controls.

## Commands and receipt

All four commands exit zero:

```sh
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/probe.mjs /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/rc112.json
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/probe.mjs /Users/pooks/.bun/install/cache/effect@4.0.1@@@1 > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/v401.json
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/probe.mjs /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect dist > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/rc112-dist.json
bun /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/probe.mjs /Users/pooks/.bun/install/cache/effect@4.0.1@@@1 dist > /private/tmp/codex-effect4-overnight-monitor/2026-10-05-full-queue-review/delivery/v401-dist.json
```

Each output records four asserted observations, package version, imported entry, repository field, and hashes.
Every control executes zero scheduled tasks; operations run through the installed runtime's public Effect API.
The outputs are inspected and compared after all four commands.
`rc112-dist.json` and `v401-dist.json` match the coordinator's distribution-entry choice.
There is no Lean, composite, native-equivalence, or all-schedules proof in this receipt.
