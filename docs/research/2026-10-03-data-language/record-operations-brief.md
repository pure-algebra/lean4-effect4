# Record value and type operations

Base: `82d34358e84f0e823be24ba895aa382092c1754c`.
Existing helpers: `e237599b` and `41c82479`.

## Scope

Add value operations in `src/Effect4/Machine/Record.lean`.
Add type operations in `src/Effect4/Program/Record.lean`.
Keep `Term` and its traversals unchanged in this slice.
Relocate `Program.recordParts?` without changing its definition.
The original declaration lives in `src/Effect4/Program/Typed.lean`.

Construction checks parallel columns and distinct supplied names before sorting paired fields.
Lookup checks every name and value before selecting a field.
An outer `none` reports malformed columns.
An inner `none` reports an absent field.
Overwrite replaces one named value and orders the resulting pairs.
Type operations use already computed argument types.
Public program admission owns recursive declaration formation checks before normalization.

## Proof placement

Concept: Store Typing & Value Membership (`docs/core/semantics.md`).
Property: typed value operations retain `Fits` in their current world.
Role: helpers for the existing registry claim `denote-typed`.
Consumer: `evalTerm_progress` in `src/Effect4/Laws/Program/Typed/Denotation.lean`.
Requirement: R3, on the M5 typing path.

Reach: named record frames from decisions row 165 and exact field declarations from row 178.
The operations implement the record forms approved in row 195.
Lookup assumes `Fits` at the declared record type and a declared field.
Required lookup also assumes the declaration marks that field required.
Construction assumes the argument values fit their checked argument types.
Overwrite assumes input-record membership and replacement membership at the replacement type.
The overwrite result has a required field at that type.
Field reads and overwrite check every union alternative before joining their result types.

The exported bridges are `record_build_fits`, `record_fieldType_fits`, and `record_setType_fits`.
Each bridge concludes that its executable operation returns a fitting value.
The helpers for column pairing, ordered names, lookup, and joined results serve these bridges.

These helpers do not prove termination or eventual host replies.
They establish no target execution claim.
Malformed raw frames remain outside the membership premises.
The host boundary remains in `docs/core/host-boundary.md`.

```mermaid
flowchart TD
  N[NamedFit and canonical declarations] --> L[Actual named lookup membership]
  A[Fitting argument values and checked types] --> C[Constructed value membership]
  L --> D[evalTerm_progress]
  C --> D
  N --> U[Actual overwrite membership]
  U --> D
  D --> M[M5]
```

## Finishing criteria

Compile the changed modules and their narrow test module.
Check missing, present undefined, present null, and nested option values.
Check duplicate names, unequal columns, and malformed name frames.
Check replacement types and required-field output flags.
Inspect each exported proof's axioms.
Record any unproved construction connection without weakening its statement.
The coordinator adds the root imports at integration.
