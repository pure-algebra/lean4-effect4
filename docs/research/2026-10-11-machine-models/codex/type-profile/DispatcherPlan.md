# Empty carriers after the dispatcher field removal

The engine generator rejects five stale function substitutions after the shared machine cleanup.
The dispatcher now has one field, so Lean erases its constructor and inlines empty bucket lists.
The old constructor substitution cannot reach those lists.

Concept: translation-simulation, R8 and M7.
Question: item 12's generated target must consume the actual R1 and R2 source.
Observation: finite engine exits, traces, stores, and scheduler queue projections.
This target repair proves no general compiler simulation.

Keep the abstract dispatcher carrier.
Retain its explicit type substitution and derive the field carrier from the source projection type.
Map Dispatcher.insert to the carrier's enqueue with the exact argument order.
Map RunMachine.dropToken through the existing observer-filter adapter.
Update the reached spawn specialization from the actual generated closure.
Delete stale constructor, empty, enqueue, and old specialization substitutions.

Add an empty operation to the existing carrier table.
Use it only at a constructor field with an explicit field or type carrier and a tracked empty-list argument.
A missing operation leaves the ordinary expression, so OCaml still rejects an unconverted queue.
A nonempty list does not take the empty path.
No machine or program definition changes.

Acceptance requires regeneration, the abstract engine's typecheck, and the existing engine and dispatcher comparisons.
Retain the stale-table failure and empty-operation negative control with the final acceptance output.

The initial field-row attempt refuses the nominal Dispatcher field before output.
The refined lookup reads its existing type row from the kernel projection type.
The field-row checker keeps its existing list requirement.
