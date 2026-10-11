# Native source opportunity debit

The native evaluator debit checks at both Workers acquisition paths for every job count.
The whole-command history bound remains open.

- Proof role: preservation.
- Evidence status: proved.
- Concept: scope-lifetime-finalization, R11.
- Consumer: `Workers.Assertions.registrations_step` and application once-placement bounds.
- Base: `890c6ca7`.

## Changes

`SourceOpportunityPrimitive` composes the actual primitive evaluator, scoped entry, scoped exit, and native evaluator.
It consumes the existing source ownership predicates and opportunity projections.
It introduces no program representation or planned goal.

`SourceOpportunity.workers_native_evaluation_debit` reads actual admitted histories at both acquisition sites.
It discharges the fragment, finalizer, loop, sequential-scope, and race restrictions from the unchanged Workers source.
It retains every job count, admitted row table, compile budget, and evaluator yield flag.

The unrestricted machine `Moves.answer` and `Moves.push` rules do not establish numeric debit.
Their replacements and pushed names carry no opportunity bound.
The evaluator proof therefore composes the existing actual producer laws.
Machine footprint laws remain available for settlement identities.

## Checks

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity` succeeds with 1082 targets.
The primitive module takes 2.4 seconds; its scenario reader takes 2.9 seconds.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/SourcePrimitiveAudit.lean` succeeds.
The audit checks 175 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.

## Open work

Command settlement, command preservation, external-answer debit, and history induction remain open.
This checkpoint proves no final registration bound.
The original universal OncePlaced goal also includes syntax outside the checked application fragment.
