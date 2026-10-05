# QueueSteps readiness follow-up

Status: bounded source review at `b1d8cb2f`, with retained finite Lean outputs.
The monitor runs no Lean, build, generator or host program.

## What the new evidence establishes

`QueueSteps.out` contains seven successful machine answers and seven successful authoring-build verdicts.
The fixture measures typing explicitly for R4 and retains its error type `never`.
R1 and R4 are compared with the abstract model by inspecting their outputs.
There is no proved connector between the term's result and the model's step.
The readiness note states that boundary and the missing host comparison correctly.

The probe now uses `onExit` with `causeIsInterrupt` for withdrawal.
It preserves the delivered exit instead of rebuilding an interruption without its source.
That consumes the earlier recommendation; it is not raised again here.
The guard currently surrounds each restored wait, while the earlier note recommends one request-wide guard before registration.
Do not count this limited probe as a proof of the wider request lifecycle or of repeated waits.
The note already excludes masked callers, hint renewal, ends, other strategies and a delivery-budget theorem.

## One concrete signal-order control

`QueueContract.afterConsume` concatenates accepted-offer answers before the next taker's wake.
`QueueSteps.takeStep` returns those two groups separately.
`QueueSteps.take` posts its taker-hint group first and its offer-answer group second.
The two sources therefore disagree on their ordered notification outputs when both groups are nonempty.

A reachable abstract prefix, in the existing first profile:

1. Start an opened suspend queue of capacity one.
2. Register takers 1 and 2, in that order.
3. Offer message 1 under request 100; leave its posted hint pending.
4. Offer message 2 under request 101; that offer waits behind the full buffer.
5. Taker 1 retries and consumes message 1.

The last step accepts message 2 and leaves taker 2 ready.
The model emits `[offered true to 101, again to 2]`.
The research wrapper posts `[again to 2, offered true to 101]`.
The final buffer is `[2]`, with taker 2 remaining and no pending offer.
The consuming reply is `[1]` in the mirror; no different public answer is asserted.

The smallest first-profile correction posts the offer-answer group before the taker-hint group.
Add this mixed-signal case beside the existing R4 comparison.
Its single-offer-answer control and a single-taker-hint control both retain the current order trivially.
If the eventual contract intentionally ignores notification order, state that observation explicitly and justify the wrapper relation.
Do not silently erase this difference when comparing signals.

`mixed_signals.py` retains this reachable prefix and eight assertions.
It runs under Python 3.13.14 and succeeds.
This is a finite mirror, not a Lean theorem, wrapper execution or host scheduling failure.
It establishes the source-level comparison to add, not a public-result counterexample.

## Q1 connector and reuse

The next useful connector relates one encoded state, one operation reply and its ordered notifications to the abstract step.
Its first domain is opened, positive-capacity suspend queues with singleton offers and scalar takes.
Keep the encoding's request-identity map injective and its queue-order invariant explicit.
A raw arbitrary record is not a reachable typed queue state.

Use `fold_fits` and `fold_typed_atomic_update` for the term's membership and binder rules.
Use `refModify_typed_step` for one cell update answering B while storing A.
Use `acceptLoop_length_le` only after the term/model relation identifies the accepted messages.
None of those existing results establishes notification order or delivery by itself.
The new connector serves the proposed `queue-expansion-agrees` claim under R10.
Its consumer is the first Queue step; its observation is the model state, reply and notification list.
Wrapper ownership, delivery, cancellation, fairness and target execution remain outside that helper.
The immediate prerequisite is a fixed cell encoding and this output comparison.

## A precise face boundary to retain

The real QueueSteps terms use stated accumulator types in `accept`, `removeTaker`, `renewHint` and `wake`.
T5's current brief and FOLD's receipt preserve the unannotated-only reader domain.
T5's named Queue readback acceptance still points to the earlier QueueSkeleton examples.
Therefore T5's general result does not by itself cover readback of these new annotated steps.

Keep a direct emitted-module/readback control for the real R4 program when it becomes printable.
Alternatively, state that annotated reading remains outside the first delivered face.
This is a boundary in readiness and acceptance, not a defect in T5's unfinished implementation.
No new reader or representation is requested by this review.

## Recheck against the new step-slice design

`queue-steps-design.md` lands at `61fecd0c` during this review.
The probe's ordering is unchanged, and the new design does not yet choose the notification-list observation.
The mixed-signal control therefore remains relevant to F3's first step relation.
Keep accepted-offer answers before taker hints, or state and justify a weaker observation explicitly.

F3 needs one precise change before its goals freeze.
The table can grow for a fresh request, but hint renewal updates an existing request's hint.
`QueueSteps.renewHint` retains the identity handle and changes its hint.
For an already enrolled taker without a message, the model's `take` keeps the abstract state unchanged.
The concrete step still renews that hint.
A relation allowing only table extension therefore cannot express this existing path.

Distinguish stable identity extension from current-hint replacement.
Allow the requested identity's hint to change, and keep unrelated entries unchanged.
Relate newly emitted notifications to the hint captured by that step.
Previously posted notifications need their original hint occurrence in the later wrapper relation.
This does not require implementing wrapper cancellation or old-hint delivery in Q1.
A single existing-taker/no-message control checks this relation boundary before the goal is stated.

F1's future-complete schema claim is broader than its listed offer record.
`QueueContract.Offer` also records whether an offer is a batch.
The listed concrete offer contains identity, hint and remaining messages, but no batch discriminator.
Singleton offers suffice for Q1, with the relation explicitly requiring `batch = false`.
Either reserve passive offer-kind data now or qualify the promise that no future step adds a field.
Do not implement batch behavior merely to close that wording gap.

The new slice remains useful without T5 or the mask.
Its goals should retain the restricted first profile, typed state encoding, identity relation and ordered notification observation.
The earlier annotated-readback boundary applies to the later printed wrapper, not to accepting this pure step slice.

## Parent source recheck: first full-buffer offer

A second notification comparison differs on the same prefix.
The model's first suspended offer on a full buffer returns `wake s1`.
The research `offerStep` returns an empty hint list in every pending branch.
With waiting takers, the model repeats the ready head's hint; the research probe emits none.
An earlier pending offer correctly returns no signal in both sources.
An unchanged buffer and reply therefore do not establish the step's notification relation.

Keep this case with the mixed-signal control.
Match `QueueContract.offer` by distinguishing an earlier pending offer from a first offer blocked by capacity.
Emit the model's wake hints in the latter branch.
Alternatively, explicitly justify an observation that permits duplicate-hint suppression.
No lost-message, liveness or host-result failure is claimed.
The parent extends and reruns the finite mirror to twelve assertions, including both no-signal positive controls.
