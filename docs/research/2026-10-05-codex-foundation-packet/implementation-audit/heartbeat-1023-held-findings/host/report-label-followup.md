# Host report provenance label

Status: reporting-scope defect, not an execution defect.
`check-keyed.ts` sets `wholeObservationOnHost` from `waits.length === 0`.
The retained routing report sets it to true while `predictedByTheLedger` contains `refusals`.
`keyed-observation.ts` explicitly calls the verdict replay evidence.
The detailed report preserves this distinction, but the aggregate label and evidence sentence do not.

Rename the aggregate to `allFieldsAccountedFor`, or require no predicted fields for independent whole-host measurement.
Keep ledger predictions and their replay checks. The later active evidence sentence already includes this category.
The routing artifact is the counterexample to the literal label; workers supplies the all-measured positive.
This is the existing R8 finite host evidence boundary, not a new semantic goal.
No lane or comparator is rerun by this monitor. Delivery is pending while the UI is locked.

Closing source uses an evidence-row test instead of the earlier waits count.
It still treats a ledger-only row as sufficient for `wholeObservationOnHost`.
The generated per-script table and evidence sentence already preserve all four categories.
Only the aggregate label remains in the proposed correction.
