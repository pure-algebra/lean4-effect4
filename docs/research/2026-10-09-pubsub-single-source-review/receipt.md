# PubSub single-slot source challenge

The future host relation needs an exact numeric-admission range in addition to Model.Live.
The current Lean Step/model statement needs no weakening.
The bounded source controls find no bookkeeping mismatch.

## Reviewed tree and retained bytes

Reviewed HEAD: `a12963285539be53706507a09e6b040474857302`.
The reviewed tree is `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
Its new PubSub core files are untracked work in progress.
The law author works concurrently in that tree.
This review writes no file and runs no Lake process there.

Evidence base: `9f46d1fe11119e039c9dfcc767f0fa81885f5001` on `codex/synchronized-ref-pure`.
Only this research directory changes in the review branch.

`source.json` records the full latest PubSub source hash, extracted bytes hash, and hashes of the four reviewed Lean core files.
`single-extract.ts` retains the exact BoundedPubSubSingle and BoundedPubSubSingleSubscription source region, including its trailing comments.
The extraction begins at line 2539 and ends before line 2690 of the named vendored file.
`probe.ts` embeds those unchanged bytes between its sentinel definitions and independent model transcription.
`output.jsonl` retains every measured result.
`bun-version.txt` records Bun 1.4.2.

The source hash is `ab512549c7f76d9a7df8e953268e377eecdbad6ce985a29b03dcd91b596da758`.
The extraction hash is `0e1bd26a7e01d5d6fac187cca12de2eb5f436e9add50034b69b994a18b501341`.

## Command and evidence kind

Run from the evidence worktree:

```sh
bun docs/research/2026-10-09-pubsub-single-source-review/probe.ts
```

The command exits successfully.
The explicit-path diff check reports one new blank line at EOF in single-extract.ts.
That whitespace is an intentional exception because the extract preserves exact vendored bytes.
The diff check passes when only that exact extract is excluded.
Bun transpiles the extracted TypeScript classes and runs their actual method bodies.
Replay is disabled.
Only constructor, subscribe, publish, slide, poll, unsubscribe, and their isEmpty/isFull predicates run.
Distinct sentinel symbols represent AbsentValue and MutableList.Empty.
The independent model transcription uses BigInt for Lean's natural publisher indices, cursors, and retained counts.
A manual logical-name table represents live source subscription objects for these finite observations.

This is a finite source-extraction comparison against an independent model transcription.
It does not execute Lean Step or establish the transcription as a Lean theorem.
It uses no tsgo check and runs no full vendored PubSub module or public wrapper.
It proves no contextual identity correspondence, waiting, cancellation, delivery, scheduling, or host relation.
The current Lean Step/model proofs are separate evidence.

## Strong controls

The bounded exploration compares 2,090 unique reached states and 12,888 transitions.
It uses traces of depth at most nine, subscriber names 0, 1, 2, and messages 0, 1.
Every subscribe uses a currently fresh name.
Replies, projected live state, subscriberCount, and the written Live conditions agree after every transition.
There are zero mismatches in this exploration.

The retained targeted traces also check:

- Slide after one of two readers polls; both readers receive the replacement publication.
- A late subscriber misses the retained old value and receives the later publication.
- Unsubscribe after poll leaves the other reader's retained ownership intact.
- No-subscriber publication succeeds without storing a value or advancing publisherIndex.
- The last unread unsubscribe frees the value; repeated unsubscribe remains inert.

The source and Model both leave cursors and publisherIndex unchanged on slide.
The Step slide writes only remaining and value, matching that rule.
The other Step branches retain the Model's guards and updates through existing map, any, and removeBy builders.
This structural inspection is separate from the executing source comparison.

## Live control: an empty slot may have stale cursors

The trace subscribe 0, publish 7, slide produces this state:

```text
publisherIndex = 1
remaining = 0
subscribers = [{ id = 0, cursor = 0 }]
value = none
```

The written Live conditions hold, and the probe reports Live true.
One live cursor still differs from publisherIndex, while remaining is zero.
Therefore the reader-count equation must remain conditional on a retained value.
An unconditional equation between remaining and the count of unequal cursors rejects the source's slide behavior.

## Confirmed numeric boundary

The probe manually seeds a state with publisherIndex and its one live cursor equal to 2^53.
Remaining is zero and value is none.
The written Live conditions hold, and the probe reports Live true.
This seeded state is not presented as a trace reached by the bounded exploration.

The extracted source accepts publish 7, but JavaScript Number addition leaves publisherIndex at 9,007,199,254,740,992.
The exact natural model advances it to 9,007,199,254,740,993.
The source poll then returns Empty because its unchanged cursor equals publisherIndex.
The exact natural model poll returns 7.

Live alone therefore cannot serve as a sufficient premise for future latest-source agreement.
The future contextual host relation must admit only counters and updates with exact source arithmetic.
It must also state the exact range of any numeric message encoding.
Do not change the independent natural model or weaken the present Step/model equation for this boundary.
No current source-run theorem is contradicted because the present aggregate establishes no source implementation observation.

## Later retention helper

A future capacity-greater-than-one model can share retained-publication ownership facts.
For a retained publication, ownership depends on which live subscriber cursors have not passed its publication index.
A late subscription starts at the publisher frontier and owns no existing retained publication.
Polling advances one cursor and relinquishes that publication's ownership.
Unsubscribe relinquishes that subscriber's ownership throughout its retained suffix.
Slide removes the oldest retained publication and leaves subscription cursors unchanged.
The array source later clamps a stale cursor to its retention frontier before poll or unsubscribe.
These are broadcast retention facts, rather than generic Queue consumption rules.

Placement of this future proposal:

1. Concept: translation-simulation, required property R10, agreement of a source bookkeeping observation with an independently retained-publication model.
2. Question: a proposed helper of the future PubSub contextual source relation under G10; no new theorem or registry claim lands here.
3. Reach: retained slots in the interval from the retention frontier to the publisher frontier, unique live registrations, contextual subscription correspondence, and exact numeric admission.
4. Exclusions: the helper establishes no waiting, delivery order, cancellation, scope finalization, allocation, or whole-wrapper agreement.
5. Unlock: later per-slot count and cursor obligations for capacity greater than one; G1, G7, G9, and G10 remain open.

The immediate action is to retain these controls and record numeric admission in the future host relation's brief.
The current six-operation pure slice can continue without a model or theorem-statement change.
