# Forward lookup interference

Concept: reactive-scheduling, invariants over execution traces, serving R11's release custody.
Question: the existing `command-moves` structure serves `ReleaseCustody.Execution.history`.
Reach: every actual native evaluation and iteration, including machines with duplicate fiber ids.
Limit: lookup and stack transport establish no funding, progress, store ownership, or command closure.
Consumer: `NativeStacks.native_links` and `NativeStacks.iteration_links`, with unchanged statements.

The existing `Interferes` describes every new record's origin.
It permits deletion of old records and does not imply forward lookup survival.
Its membership-only update helper also permits replacement from another record with the same id.
Retain that interface and strengthen the existing native census with `LookupEdits`.
The new update clause consumes the actual first lookup.
Keep existing evaluator theorem names and statements as projections of the single stronger census.
Project exact stack equality through `StackRegion.other_edits_stack`.
Remove the old `NativeStacks` evaluator traversal in the same slice.

Finish after the narrow build, actual consumer rebuild, finite controls, audit, and measured line receipt.
Change no executable code and run no behaviour gate for this proof consolidation.

