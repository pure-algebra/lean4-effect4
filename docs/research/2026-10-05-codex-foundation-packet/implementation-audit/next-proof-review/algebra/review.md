# Reusable algebra and structural laws after Queue

The next useful work finishes existing connectors. A new algebra campaign is unnecessary for the next Queue slice.

Snapshot: `0e6077b6d859cf7030b05654a9ec3dbe1781b993`.
Evidence status: read-only source review. No Lean, compiler, generator, runtime, or gate runs occur.
Proposed statements and controls below are uncompiled. Later T5 changes are outside this cut.

## What already exists

| Owner | Existing declarations | Reach |
| --- | --- | --- |
| `Program/Fold.lean` | `TermHom`, `EffHom`, `hom_eq_cata_term`, `hom_eq_cata_eff` | Uniqueness of the generated syntax folds |
| `Laws/Program/Folds/Term.lean` | `fold_of` connectors for evaluation, typing, scope and weakening | The existing traversals are algebras over `Term`; no second traversal framework is needed |
| `Laws/Program/Folds/Denote.lean` | `denote.eq_cata`, budgeted and signature-parameterized connectors | Denotation and agreement measures use the same generated fold |
| `Laws/Program/Typed/ListFold.lean` | `ListFoldRules`, `fold_typed_atomic_update`, `refModify_typed_step` | Scope, evaluation, failure, weakening, typed progress, membership and one typed store update |
| `Laws/Program/MeaningEq.lean` | `StraightEq.bind`, `onExit`, `select`, `catchCause`, `matchCause`, `exit`, `suspend_remove`, `run_agrees` | Equal exits and complete stores on the straight fragment, with separate sufficient budgets |
| `Laws/Program/Typing/Sound.lean` | `hasTy_weaken`, checker agreement and constructor equations | Existing checker and declarative typing connection; signature naturality remains explicit |
| `Laws/Effects/Sum.lean` and pinned Effects package | `sum_is_coproduct`, `program_is_free`, `interpret_isMonadMorphism`, handler uniqueness | Free-monad algebra; not raw `Eff.bind` reassociation |

The generated report marks `fold-typed-atomic-update`, `operation-data-scoped`, `queue-steps-agree`, and `straight-composition-agreement` proved at this cut.
These statuses concern their exact statements. They do not prove Queue wrappers or target execution.
The Effects checkout matches the manifest revision `a4ee7a14248ee5976039b73039319efa87834986`.

## 1. Small missing connector worth landing: capture of a minted caller name

Status: already identified in the final QSTEPS receipt, open item 3. This needs a small proof, not another capture representation.

Concept: `translation-simulation`, R10. Role: helper of `queue-steps-agree` and the proposed wrapper claim `queue-expansion-agrees`.
Consumer: `takeStep_agrees`, `withdrawTake_agrees`, and `withdrawOffer_agrees` require `Captured`; `Test/Program/QueueScenarios.lean` supplies identities through `bindWith`.

`captured_var` covers nonreserved author-written names. `bindWith` instead returns `minted`, which reads reserved names.
Add the corresponding helper using `Names.resolve_append_ne` twice and `List.getElem?_append_left`.
Keep it in `Laws/Modules/Queue/Reading.lean` until another module actually consumes it, as the receipt already requests.

Exact proposed premises:

- The caller's name resolves to index `i` in the existing environment.
- The captured values contain `v` at `i`.
- Both new fold names differ from the caller's name.

Conclusion: `Captured (minted name) env path vals v`.
Then discharge the two distinctness premises for the actual `bindWith` identity, whose fixed stem is `answer`.
Do not assert that arbitrary stems and depths encode injectively without proving that separate statement.

Positive control: a `bindWith`-allocated identity, transported through `foldWith`, feeds `withdrawTake_agrees` without an assumed `Captured` field.
Red control: choose a caller name equal to the new accumulator name; last-name lookup reads the accumulator instead of the earlier value.
Keep identical value types in this control, so type agreement cannot hide the error.

A broader proposed shortcut is false: `TermSrc.Scoped` alone cannot establish capture preservation.
`TermSrc` is an arbitrary function of `Env` and path, not stored syntax.
For example, a source that returns the current name count as a natural literal remains scoped and typed under every environment.
Its returned value changes when two names are appended. This is a source-derived falsifier candidate, not an executed probe.

This helper establishes preservation of one read under two binders. It establishes no wrapper typing, resource cleanup, scheduling, or host law.
Prerequisites: existing resolution and lookup laws only. No generated syntax changes are needed.

## 2. Already planned: checker construction lemmas for the five Queue typing goals

The receipt's final section already proposes `Checking.lean`, symbolic atom rules, record rules, and a two-binder fold rule.
The five exact goals remain `proof_goal` declarations in `Laws/Modules/Queue/Typing.lean`.
Therefore this is a prepared proof slice, not an unidentified language gap.

Concept: `store-typing`, R4. Role: compatibility helpers of those existing planned goals and `fold-typed-atomic-update`.
Consumers: `withdrawOffer_typed` first, then the other four goals; each reaches `step_keeps_cell` through its existing typing premise.

Keep the proposed source judgment definitionally tied to successful elaboration and `argTy sig types const`.
It must retain the literal flag; replacing it everywhere with `termTy` loses the record and const-generic argument rules.
Do not add an independent acceptance checker or expand the grammar.

The smallest missing general helper is the introduction direction of `termTy_fold_inv`.
Its premises are the list type, initial type, chosen accumulator, both subtype checks, and the body type under `env ++ [accumulator, item]`.
Its conclusion is the existing `termTy` equation for the fold.
`ListFoldRules.typing` currently supplies inversion, not this introduction rule.

For records, preserve the raw formation guard before the existing `Record.check` premise.
`termTy_record_inv` extracts argument checking but does not supply a reverse theorem without that formation premise.
For overwrite and field reads, retain `Record.setType` and `Record.fieldType` as the acceptance owners.
Reuse `Ty.sub_refl`, `sub_nil_list`, `Ty.sub_args_list`, `cellTy_normal`, `offerTy_normal`, and `cellFields_normal`.
The existing record membership/progress theorems already connect successful checking to evaluation; do not reprove them.

Preserve the five goal headers: arbitrary signature with native atom table, arbitrary `A`, and the full `MessageTy A` premise.
A helper may expose `sig.constAtom` when needed; it must not silently add that premise to the frozen goals.
Keep `MessageTy`'s canonicality and both formation checks. Do not replace them with a finite type list.

Positive controls: finish `withdrawOffer_typed` at symbolic `A`, then consume it through `step_keeps_cell` at the declared local scope.
Retain a concrete nontrivial record message type as a readable example.
Red controls: a fold body above its accumulator type; duplicate raw record fields; reversed accumulator/item positions; a captured input moved without remapping.
Existing finite checks remain useful controls, but they do not close the universal goals.

This closes local checker equations and the conditional store consumer. It establishes no notification delivery, cancellation law, or whole-wrapper theorem.
Prerequisites: none beyond existing source laws; source-to-wrapper environment transport remains explicit work.

## 3. Defer: broader source composition or addressed semantic transport

The current named nested-rewrite consumer already works.
`Test.Program.MeaningEqContract.rewrite_agrees` combines `StraightEq.bind` and `StraightEq.onExit` around two suspension removals.
Its runtime consumer observes failure and the final cell value, with separate budgets.
The test also refuses exit-only comparison and comparison outside `Straight`.
No additional monad or handler framework is required for that consumer.

`Node.replaceAt_spec` in `Laws/Program/References.lean` proves structural replacement and reversal, not semantics.
`Api.Built.rebuild` separately rechecks admission. `Test/Program/AuthorContract.lean` exercises intentional behavior-changing edits.
There is no current semantic caller in those tests that needs an automatic addressed-rewrite theorem.
Do not schedule that theorem merely because the structural API exists.

If a real optimization later uses `replaceAt`, its helper can serve `straight-composition-agreement`, concept `translation-simulation`, R8.
Require an actual replaced Eff child, a successful path edit, straight fragment witnesses, and `StraightEq` for the old and new children.
Consume the existing constructor congruences and `run_agrees`; exclude arbitrary layers, host rows, traces, and equal small-fuel runs.
A positive control is the existing nested suspension rewrite. An exit-equal but store-different replacement must remain red.

The broader `composeAt` identity and associativity proposal in `system-map.md` is still explicitly future work.
Raw `Eff.bind` is not categorical composition because its variables are absolute positions.
The separate residual `TypedProg` bind counterexample does not establish this source-level claim; do not merge the two issues.
Before a general category law, choose a real transformation consumer and its environment/observation contract.
The existing free-monad laws belong to the Effects representation and cannot discharge that missing connection automatically.

## Suggested order

Land the minted-capture connector with one existing Queue consumer.
Finish the already planned shared checker slice, starting with one universal goal and its store consumer.
Use existing `StraightEq` laws for concrete straight rewrites. Defer a broader algebra project until a caller needs it.

No QTYPES brief is present in the inspected lead brief directory during this bounded check. The existing receipt supplies the current typing plan.
