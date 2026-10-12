# Source budget through the actual primitive producer

Concept: scope-lifetime-finalization, R11.
Question: actual source-use accounting for `Workers.releases_once` and `Atomic.cleans_once`.
Keep `Opportunities.primitive_debit` in `src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean` unchanged as a statement.
Its consumers are native debit, command debit, and the existing source-opportunity history.

Replace its private `evaluatePrim` classification with the shared indexed `PrimitiveProducer`.
Retain actual lookup, registration, countdown, and current-code equations from that producer.
Keep all lexical, sequential-source, race-free, clear-finalizer, clear-loop, and distinct-owner premises.
This consolidation grants no source admission, current-code permission, or progress.
It serves the original release and cleanup bounds through their checked source-use premises.

Build the changed module and the source-opportunity history consumer.
Audit the changed module and compare every old theorem header.
Remove the old evaluator split in the same slice.
