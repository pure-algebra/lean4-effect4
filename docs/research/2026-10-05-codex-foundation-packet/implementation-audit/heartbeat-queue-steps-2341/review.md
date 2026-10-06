# Queue steps follow-up at 235ed294

Status: source review and retained finite evidence. No Lean command ran in this review.

The earlier advice is consumed in the committed source. The private transcript remains unavailable to the parent.

## Resolved in the reviewed source

- `takeStep` returns accepted offers before taker wakes. The wrapper posts them in that order.
- The first full-buffer offer wakes the earliest taker. An offer behind a pending offer stays silent.
- `withdrawOffer` returns and posts the model's wakes.
- The encoding table can extend or replace a waiting request's current hint. It frames other entries.
- Offer records carry the batch flag. The first profile fixes it to false.
- Each step uses unannotated folds. The retained output reports four `some true` checks for `Term.unannotated`.
- Acceptance names R4 printing and reading after T5. The current printer refusal remains visible.

Sources: `QueueSteps.lean` and `queue-steps-design.md`, under `docs/research/2026-10-05-claude-lead/queue-readiness/`.

## New finding: state-domain closure must precede the step goals

F3 states five premises but does not require an empty peeker list. It also does not constrain every stored taker's bounds.

The first implementation omits these operations. Its planned relation must restrict the states accordingly.

A precise witness extends the retained passing C4:

```lean
s0 := { capacity := some 2, takers := [T 1] }
s1 := { capacity := some 2, takers := [T 1], peekers := [2] }
QueueContract.offer s1 100 7
```

`QueueContract.wake` returns `again 1` followed by `again 2`. `offerAgrees` resolves every `again` through `r.1.takers.find?`.

That lookup silently drops peeker 2. `stateTerm` also omits the peeker list. Thus `offerAgrees s1 100 7` reduces to the same comparison as C4 on `s0`.

The retained C4 result is true. This extension therefore exposes a source-derived false positive in the comparison's unrestricted domain.

The full model reaches `s1` from an empty capacity-two queue by `take 1`, then `peek 2`. The intended first profile excludes `peek`.

This witness does not refute the intended first profile. It shows why its restriction must appear in the relation and checker.

There is a second domain distinction. Replace the stored taker's bounds with two and two, then offer one message.

The model emits no wake. The current concrete `wake` emits the head taker whenever a message exists. Current-request bounds do not restrict stored requests.

Smallest correction: define a closed `FirstProfileState` before stating the goals. Include opened phase, positive bounded capacity and suspend strategy.

Require singleton non-batch pending offers, every stored taker's one/one bounds, and no peekers. State whether unused awaiters are absent or framed.

Use a partial notification encoder that refuses an unrepresented signal. A successful comparison must account for every signal in order.

Keep identity-table injectivity, fresh request conditions and current-hint replacement explicit in the state relation. Do not infer them from finite controls.

Placement: `translation-simulation`, R10, claim `queue-expansion-agrees`. Consumer: each step goal, then the wrapper's law.

Observation: reply, stored value and ordered notifications. Prerequisite: the exact first-profile state predicate and encoding relation.

Exclusions: wrapper delivery, posted helper ownership, cancellation, progress, host execution and broader Queue operations.

## New finding: strengthen the red controls without adding machinery

The first red control compares `takeStep`'s pair-shaped result with a bare state record. It rejects the outer shape.

It does not distinguish the corrected notification order from the earlier reversed order. The positive C1 still checks the corrected source.

The second red control changes both the reply and stored state. It does not isolate the missing-wake defect.

Use C1's expected result with only its ordered notifications reversed. Use C2's expected result with only its wake removed.

When promoted, retain the positive cases and check those mutants through the existing fixture mechanism. No new validator framework is needed.

This is a control-quality correction. It is not a failure of the existing positive results.

## Evidence boundary

The committed output retains eight built scenarios and six successful direct comparisons. R8 retains the log `[1, 101, 2]`.

These are finite retained runs, not new results from this monitor. R8 measures one run, not every possible resumption order.

The relation is still a design. It has no Lean declaration in this slice. Planned goals must preserve the narrowed premises above.

No repository source changed. No build, generator, installation, UI action or Lean runtime probe ran.

## Finite comparison mirror

`comparison_controls.py` retains 17 finite assertions and their exact output. Python 3.13.14 ran the mirror.

It checks the C4 projection, the dropped peeker, and a decoder that refuses missing identities. It also checks stored bounds.

Same-shaped notification mutants are rejected. The bare-state red rejects both the corrected and reversed-order result.

The mirror is not the Lean evaluator. It does not add a theorem or establish host behavior.
