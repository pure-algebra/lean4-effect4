# Atomic scenario: bounded source review

Evidence: reading only. No Lean, build, generator, installation, UI action, or repository edit ran.
The source snapshot and hashes identify the reviewed draft. Its unfinished acceptance remains open.

## New actionable mismatch

`Fault.twice` in `Test/Dogfood/Scenario/Atomic.lean` executes `note cleaned seen` twice inside one finalizer body.
It does not replay one cleanup registration, as the DOGFOOD brief requests.

The associated declaration is `Effect4.Program.Denote.meaning_onExit` in `src/Effect4/Laws/Program/Denote.lean`.
It states that the finalizer receives the body's resulting stores and that its resulting stores survive.
It places no restriction on how many writes the finalizer body performs.
The same law therefore describes both the original finalizer and the `.twice` finalizer.

The green `committed` control checks request 2's failure, the retained account, and presence of `saw 2 2`.
The red control's expected observation retains all three facts and merely duplicates cleanup entries.
It does not falsify that green predicate or the cited finalizer-store law.

Smallest correction: state a scenario-specific committed observation property, using `meaning_onExit` as supporting evidence.
Its mutant must falsify that property; a legal extra reset still satisfies the general law.
State cleanup-log multiplicity separately. The `.twice` mutation may test that exact log property.
Duplicate log entries alone establish no registration replay or finalizer invocation count.
A registration-replay control needs separate evidence of execution under the same registration.
Consumer: the Atomic scenario and its `controlsOf` and `scenario` declarations.
Placement: committed stores serve R4; cleanup identity serves scope-lifetime-finalization, R11, under the DOGFOOD brief.
Exclusions: no host transaction, scheduler liveness, whole-run resource result, or lowered execution claim.

## Actual planned statements

`Bounded` quantifies every driver script after a successful build of `shop .none`, at the battery's fixed budgets.
It bounds the observed window's `used` field by three.
`natField` reads an absent or malformed field as zero, so the statement does not itself assert store formation.

`Counted` states aggregate inequalities: completed <= decided <= six, and deposits <= admitted.
If all six complete, it requires six decisions and equality of deposit and admission counts.
It does not state per-request identity correspondence or cleanup multiplicity.
For example, equal-length deposit histories with different request identities cannot be distinguished by this predicate.
This is a statement-scope limit, not a reachable counterexample to `Counted`.
Keep the prose aggregate, or strengthen the planned statement before claiming per-request exactly-once behavior.

`atomic` currently assembles only `Bounded` and `Counted`.
Its separately named `meaning_onExit` and `syncRow_typed` clauses are not assembled by that theorem.
That association issue is already covered by Message98; do not send it again as a new finding.

## Disposition

Send only the new committed-control mismatch if useful to the active seat.
The planned goals remain open, and this review does not judge unperformed acceptance as failed.
