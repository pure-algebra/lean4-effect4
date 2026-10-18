# V1 placement packet

The production integration must place these obligations before compiling their proofs.
The temporary files propose these placements and do not edit the central registry.
The implementation contains no core import of Laws.

## Claims and consumers

| Declaration | Concept and property | Question and role | Reach | Exclusions | Consumer |
| --- | --- | --- | --- | --- | --- |
| `Check.combine_deps` | initial-algebras-folds; source annotation agreement | checker decomposition; compatibility | every module or part key, full verdict, and projected layer addresses | admission, progress, native execution | `Checked.ask_value`, policy feed; R14 |
| `Check.run_placed` | initial-algebras-folds; checker-base-natural | helper of checker decomposition | full part verdict at every base address | module admission and cost | decomposition and explanations; R14 |
| `Check.run_part_extends` | initial-algebras-folds; signature support | positive extension compatibility | extending signature data, one positive old part answer, exact table and result | negative hits, module hits, native execution | `Check.extension`; R14 |
| `Check.explain_replays` | initial-algebras-folds; checker-base-natural | local explanation compatibility | an actual selected dependency, its role-specific placement, and its exact refusal | aggregate refusals without a matching local failure | tool explanations; R14 |
| `Check.Checked.ask_value` | host-session-protocol; certified checker substitution | exact ask observation | every certified oracle and key | native callbacks and cost | source-session opening and feed; R6/R14 |
| `Check.extension_hit_retains_positive` | initial-algebras-folds; signature support | helper of positive extension compatibility | every old positive extension hit | refused old answers and module keys | memo reuse after hole-table growth; R14 |

`combine_deps` and `explain_replays` are planned goals in the proposed Laws owner.
`Checked.ask_value` retains its exact old statement and depends on `combine_deps`.
Its module implementation now combines actual dependency answers.
The trace contains those actual part asks, without a synthetic module answer.
Trace validity uses `Oracle.agrees` and no planned goal.

`Oracle.eq_uncached` and `Oracle.transparent` remain in core with their original proofs.
The certified extension constructor uses the pure support connector and the core restriction helper.
It imports no Laws module and uses no planned goal.
The positive-answer support theorem proves that the added guard loses no planned positive hit.

## Central anchors

Add `Effect4.Laws.Program.CheckAgreement` at the checking-law anchor in `src/Effect4/Laws.lean`.
The S0 `Effect4.Program.Check` root reaches all new core owners through its imports.
The existing `Test.Program.CheckCacheControls` import reaches the replaced V1 battery.
No new Test root import is required.

The exact registry names remain the coordinator's placement decision.
Register `combine_deps` and `explain_replays` as planned goals before their consumers land.
Keep their requirement, observation, fragment, and exclusions separate from their measured proof status.
Regenerate semantics through its producer after placement.

## Native recommendations

Add `Effect4.Program.Check.extension` and `Effect4.Program.Check.explain` to the API nominal roots when exported.
Keep S0's abstract `Checked`, `Memo`, `Oracle`, and `HitRule` packages.
`Run.Kit.check` now restricts `Check.run` to an empty hole table.
The coordinator must regenerate the reached translation groups and run the OCaml gate.
Temporary Lean checks do not establish native execution.

## Existing statement transport

Three placed Laws statements retain their original declaration names, signatures, and placement attributes.
Their proofs call pure core helpers with the following names.

| Existing Laws statement | Core helper |
| --- | --- |
| `SigApp.withHoles_extends` | `SigApp.withHoles_extendsCore` |
| `Annotate.check_alg_agreeOn` | `Annotate.check_alg_agreeOnCore` |
| `Annotate.check_restrict` | `Annotate.check_restrictCore` |

Lean refuses adding placement metadata to imported declarations.
The exact wrapper statements therefore remain in their original Laws owners.
The helpers serve those original claims and the certified extension constructor.
This transport changes no premise or observation of those statements.

The former proved `Checked.ask_value` statement becomes proved modulo `combine_deps` in this slice.
This is an explicit proof-status regression, accepted for the planned-goal completion condition.
It retains its exact observation and hypotheses.
Core trace validity remains independent of both planned goals.
