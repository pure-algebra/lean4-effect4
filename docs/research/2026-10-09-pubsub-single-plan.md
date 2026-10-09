# PubSub: capacity-one pure steps

The first slice models broadcast ownership at capacity one and with replay disabled.
It transcribes latest (Effect 4.0.1), `BoundedPubSubSingle` in `vendor/effect-4.0.1/src/PubSub.ts`, 2539–2680.
The constructor selects this implementation at 543–549.

Base: `08431c4e81c5f48be2ae8ba810e4fecad8c58139`.
The preserved branch is `codex/module-waiting-probe`.
The branch is `codex/pubsub-single`.
Root owns all imports, semantics registry changes, and architecture records.

## Scope and observation

Messages are natural numbers.
A logical subscriber name is model data.
It does not encode a source subscription object or claim runtime identity correspondence.
The state records `publisherIndex`, `remaining`, `value`, and live subscribers with their names and cursors.
A removed entry represents an unsubscribed source object's inert behavior.
The next identity-bearing module slice must supply its contextual correspondence.

The pure observation is each operation's reply and next state.
The source reading connectors observe the existing derived image of that pair.
The source profile excludes replay, capacities other than one, ended and shutdown states, and active waiting pollers or publishers.
A source connection across runs remains open.

| Operation | Independent rule | Source constraint |
| --- | --- | --- |
| initial | Empty slot, zero publisher index, no subscribers | Initial fields of the single-slot class |
| subscribe | Append a fresh logical name at the current publisher index | A late subscriber does not receive the retained old message |
| tryPublish | Full returns false unchanged; no subscribers returns true unchanged; otherwise retain value, count all live readers, and advance index | Publication broadcasts to current subscribers |
| poll | No live unread registration or empty slot returns none unchanged; otherwise answer value, advance only that cursor, and decrement remaining | Only the last reader frees the slot |
| unsubscribe | Remove the registration; decrement remaining only when it owns an unread value | Repeated unsubscribe is inert; the last unread subscriber frees the slot |
| slide | Clear an occupied slot without moving subscriber cursors or publisher index | The next publication replaces the stale item for every unread subscriber |

The three strategies have distinct obligations.
Dropping rejects a full publication without changing the slot.
Sliding first evicts the occupied slot, then tries the new publication.
Backpressure needs waiting registration and cancellation before a public publish wrapper can be claimed.
Strategy decision builders land only if they compose these pure operations without adding that wrapper claim.
The core six operations take priority.

G1 owns poller registration, subscriber traversal, delivery order, and reentrant capacity release.
G7 owns scope registration and unsubscribe finalization.
G9 owns logical names' contextual runtime identity mapping and allocation.
G10 owns a module observation across admitted decisions.
Poller cancellation removes a pending deferred, rather than unsubscribing or refunding an already consumed message.
Backpressure cancellation removes only the pending publisher's remaining entries.
Neither cleanup enters this pure slice.

## Files

| Path | Content |
| --- | --- |
| `src/Effect4/Library/PubSub/Model.lean` | Independent pure state and six operations, without Step imports |
| `src/Effect4/Library/PubSub/Cell.lean` | Derived natural-message schemas and named fields |
| `src/Effect4/Library/PubSub/Data.lean` | Named input contexts and stored Step operations |
| `src/Effect4/Library/PubSub/Steps.lean` | Source builders from the stored steps |
| `src/Effect4/Laws/Library/PubSub/Data.lean` | Carrier value equations and their model/list helpers |
| `src/Effect4/Laws/Library/PubSub/Steps.lean` | Reading and typing connectors and the aggregate |
| `Test/Program/PubSubSingle.lean` | Finite model and stored-step readers with wrong controls |
| `docs/research/2026-10-09-pubsub-single-audit.lean` | Scoped compiled axiom and import checks |
| `docs/research/2026-10-09-pubsub-single-plan.md` | This pre-proof placement |
| `docs/research/2026-10-09-pubsub-single-receipt.md` | Checks, restrictions, remaining obligations, and repeated author work |

No root, authority, generator, semantics registry, or primary-checkout file changes.

## Public author interface

The source builders are `PubSub.initialStep`, `subscribeStep`, `tryPublishStep`, `pollStep`, `unsubscribeStep`, and `slideStep`.
A caller applies each returned term in an existing Ref callback.
The logical subscriber name is a natural term for this model-data profile.

```lean
-- Source interface sketch; this example does not claim an allocation wrapper.
Ref.modifyWith cell (fun state => PubSub.subscribeStep logicalName state)
Ref.modifyWith cell (fun state => PubSub.tryPublishStep message state)
Ref.modifyWith cell (fun state => PubSub.pollStep logicalName state)
```

Named contexts supply source arguments and carriers.
Use `input_values%` if the shared helper lands during this slice.
Keep the identity interpretation explicit.
Do not add a Step constructor or a second list of input metadata.

## Proof placement before work

The proposed pointer is `Effect4.PubSub.Model.single_steps_agree`.
The root places it in the semantics registry as `pubsub-single-steps-agree`, role simulation, concept `translation-simulation`, requirement R10.
Its statement conjoins all six source-reading connectors over exact model images.
Its subscribe clause retains fresh logical names.
Its fold clauses retain value/source scope alignment.
The aggregate proves no runtime or source implementation observation.
Model/Step equations cover their arbitrary data states.
The source interpretation requires distinct live names, bounded cursors, and the retained-value reader-count invariant.
Impossible data states carry no latest-source interpretation.
A latest-host interpretation also needs exact numeric admission for messages, publisher indices, subscriber cursors, and counts.
Every represented numeric value must remain a safe integer; each increment must remain within that admission.
Logical names require contextual identity correspondence rather than numeric field admission.
`Model.Live` alone admits indices where JavaScript number addition stops increasing.
The pure Lean equations retain their unbounded natural-number domains.
After slide, `remaining` is zero even when stale cursors differ from the publisher index.
The retained-value reader-count invariant therefore stays conditional on a present value.

| Group | Concept and required property | Question and role | Reach and premises | What it does not establish | Consumer and requirement |
| --- | --- | --- | --- | --- | --- |
| Value equations | `translation-simulation`; translated pure steps read their independent model values | Helpers of `pubsub-single-steps-agree`, simulation | Natural-message model states; derived carrier interpretation; subscribe freshness retained | Membership, runtime identity, allocation, waiting or source execution | Corresponding six source-reading connectors; R10 |
| Shared list helpers | `translation-simulation`; agreement of carrier list operations | Helpers of the same proposed claim, simulation | Map, any and removal over logical subscriber records | Subscriber delivery, runtime cancellation or whole-run agreement | Poll and unsubscribe carrier equations, through existing `Step.Lists` laws; R10 |
| Source readings and aggregate | `translation-simulation`; exact reply and next-state source observation | `pubsub-single-steps-agree`, simulation, pointer `Effect4.PubSub.Model.single_steps_agree` | Exact input-image readings, canonical records, fresh subscribe name, and fold scope alignment | A general PubSub model, host equality, allocation, finalization, delivery or fairness | Concrete checked Ref callers and later wrapper connections; R10 |
| Typing connectors | `store-typing`; stored steps produce their declared source type | Readers of existing `step-language-typed`, compatibility | Typed inputs, native atom signature, and fold scope alignment | Value membership, codec admission, runtime identity or behavior agreement | Concrete checked Ref callers; R4 |

## Positive and wrong controls

- Two subscribers each receive the same value once.
- The first reader does not free the slot.
- A repeated read consumes no second value and changes no state.
- A late subscriber receives no retained old value.
- A full publication fails without overwriting the value.
- The last unread subscriber's unsubscribe frees the slot.
- Repeated unsubscribe changes nothing.
- Publication with no subscriber stores nothing.
- Slide removes the stale item before the next publication.
- After slide, every live unread subscriber receives the new value.

Each decisive case rejects its competing prediction through an executable wrong control.
Finite checks establish only their selected inputs.

## Finishing criteria

Build each new core and law module through the narrow law target.
Run the battery directly with warnings as errors.
Check the aggregate's axioms and the model/core import directions.
Retain the mandatory positive and wrong controls.
Check written research Markdown and the explicit-path diff.
Commit only the files in this plan.
Report G1, G7, G9, and G10 as open.
