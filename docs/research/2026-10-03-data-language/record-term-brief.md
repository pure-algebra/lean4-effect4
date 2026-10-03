# Record term core slice

Status: prepared from source. No syntax edit or Lean command has started.
Current seat head: `5208a4f3`. The coordinator supplies a combined base before implementation.
Contract: `record-contract.md` in the coordinator's data-language-wave worktree.

## Contract and division

Append `FieldReadMode.required` and `optional`, then `Term.record`, `field` and `recordSet` exactly as the contract specifies.
Existing constructor positions stay fixed. `Terms` keeps its existing two constructors.
The record declaration is raw type data. It is not inferred from the supplied values.
The literal policy is fixed inside each new constructor, independent of an enclosing atom's flag.

This seat owns `Machine/Term.lean`, including the small evaluator branches.
Those branches call the operations seat's `Machine.Record.build`, `read` and `set`.
The operations seat owns the value helpers, record type helpers, and membership, evaluation and handle proofs in Laws.
The coordinator owns the target printer, target reader, generated outputs and generator inputs.
No two seats edit `Machine/Term.lean` at once.

Construction evaluates the supplied `Terms` in order, then calls `build` with their supplied names.
The evaluator ignores type metadata; the checker validates that metadata before normalization.
Field reads evaluate the target once and translate the stored mode to the helper's explicit mode.
Overwrite evaluates the target, then the replacement, and calls `set`.
Raw evaluation may refuse; the operations seat extends the existing typed progress proof.

The term checker uses the existing `Formation.sites false` check on the complete declared record.
It then calls `Record.check` with argument types computed under the literal-retaining flag.
A field target uses the ordinary flag. An overwrite replacement uses the literal-retaining flag.
This retains literal discriminants without refining a variable typed as general `string`.
`Formation.programSites` also collects every declared record under its existing located term callback.
The public raw check therefore sees metadata before any program typing call.

## Exact edit fence

- `src/Effect4/Machine/Term.lean`: type-data import, mode alphabet, appended term constructors, scope and evaluator branches; revise affected module comments.
- `src/Effect4/Program/Eff.lean`: term weakening and its existing literal inversion lemma only.
- `src/Effect4/Program/Typing/Rules.lean`: the new term rules, literal split, weakening and tag-test weakening consumers.
- `src/Effect4/Program/Formation.lean`: the located term metadata collector.
- `src/Effect4/Laws/Program/Signature.lean`: the direct term-type congruence consumer.
- `Test/Program/RecordTerms.lean`: dedicated core typing, scope, weakening and formation controls.
- `Test/Program/FormationContract.lean`: the new raw term metadata entry-point controls.
- This brief and its final receipt.

`Program/Checker.lean` and its agreement laws should consume the new `termTy` unchanged.
A source change there requires a concrete need and coordination first.
`Laws/Program/Folds/Term.lean` remains the shared verification consumer; its commands should regenerate their proofs in elaboration.
The coordinator owns any edit there caused by target printer or reader work.
This fence does not add authoring wrappers; their owner must be assigned before that API work begins.

No syntax, generator, root import or policy file has been changed by this preparation.

## Proof placement

| Obligation | Concept and existing question | Reach and hypotheses | Consumer and requirement | Exclusions |
| --- | --- | --- | --- | --- |
| Raw record metadata is included in formation | Type algebra; `raw-formation`, decidability | Every record term at every generated term path; the original declared type | Runtime and code generation admission certificates; R3 and R8 | No target spelling or evaluation claim |
| New compound terms retain the existing literal split | Residual Program Typing; helper for `denote-typed` | Either enclosing literal flag; direct literal children use the new constructor's fixed rule | Existing `argTy_cases`, then term evaluation proofs; M5 and R3 | Does not refine arbitrary string variables |
| Weakening keeps the exact typing result | Residual Program Typing; existing binder-typing compatibility | Any signature, inserted type, environment split and term; success and refusal | `termTy_weaken`, program weakening and scoped authoring; R3 | No arbitrary relocation without a variable map |
| Signature extension keeps term typing | Residual Program Typing; existing signature-extension compatibility | Equal atom typing and constant flags; every new term | `SigExtends.termTy` and existing program-source proofs; R3 | No change to row or service premises |
| The checker still agrees with its judgment | Residual Program Typing; existing checker agreement | Existing signature and environment assumptions, extended term rules | `CheckSound`, `CheckInversion`, then M5 | Invariant evidence alone gives no progress |
| Evaluation produces a fitting result | Residual Program Typing; `denote-typed` | Fitting environment, successful term typing, existing native atom assumption | Operations seat's `evalTerm_progress`, then M5 | Operations-owned; no host liveness or target execution claim |

The first five obligations are direct consumers or repairs of existing claims.
The operations seat owns the last theorem and its record helper premises.
No new parallel proof graph is needed.

## Source consumer map

The structural changes are concentrated in `Machine/Term.lean`, `Program/Eff.lean` and `Typing/Rules.lean`.
`argTy_cases`, `argTy_weaken`, `argsTy_weaken` and `tagTest?_weaken` currently enumerate term shapes.
`Laws/Program/Signature.lean` has mutual `argTy_congr` and `argsTy_congr` with the same enumeration.
These consumers belong to this seat.

The operations seat must extend both existing semantic routes:

- `Laws/Program/Typed.lean`: `evalTerm_hasTy`, `evalTerms_hasTy`, `evalTerm_isSome` and `evalTerms_isSome`.
- `Laws/Program/Typed/Denotation.lean`: `evalTerm_progress` and `evalTerms_progress` with `FitsAll`.
- `Laws/Program/Handles/Term.lean`: `evalTerm_keys`, `evalTerms_keys` and `evalTerm_registered`.

The last file matters for raw terms too. Successful record construction, reads and overwrite must not invent handles.
The proofs may use the new helper laws, but must retain the existing unconditional key-containment statements.

The coordinator's direct target consumers include `Codegen/PrintLeaf.lean`, `Codegen/Read.lean` and `Codegen/Diagnostics.lean`.
`codesOf` currently enumerates the three old term constructors inside `.term`; it needs three more cases.
The associated target-code claims must stay narrower than Lean's formation refusals.
The reconstruction proofs in `Laws/Codegen/ReadPrint.lean`, `Module.lean` and `Laws/Api/ModuleReadable.lean` follow those changes.
The existing `Terms.names?` and `noRow` traversals must keep their refusal meaning for non-name record expressions.

The fold consumer `Laws/Program/Folds/Term.lean` covers the scope, weakening, evaluation and typing traversals together with the target traversals.
It cannot be the first isolated check while the target printer still lacks the new cases.
Other program and machine proofs read `termTy` or `evalTerm` abstractly; rebuild their narrow direct consumers after the bridge proofs land.

## Dependency order and root generators

1. Integrate the checked `Machine.Record` and `Program.Record` helper commit, stage-zero tooling, and this seat's admission commits.
2. Add the mode and term constructors plus exhaustive core scope, evaluation and weakening branches.
3. The coordinator regenerates group `Fold`, whose output is `src/Effect4/Program/Fold.lean`.
4. Add term typing, raw metadata collection and direct weakening and signature proofs against that regenerated fold.
5. The coordinator repairs the target traversals and regenerates the Program canonical group.
6. The operations seat completes both evaluation proof routes and handle containment, then each seat runs its narrow checks.
7. The coordinator regenerates dependent Refusals and Runner outputs, measures policy changes, and checks the combined root.

The Program group must put `FieldReadMode` and `Ty` before `Term` in its type list.
`Ty` moves as a whole sort block; no old constructor position changes.
Its output is `src/Effect4/Store/Domain/Derived/Program.lean`.
The existing Program guard input should gain mode and term roundtrips and retained-old-byte controls.

`Eff` gains no constructor in this slice, so the binder table and its generated authoring families do not need invented binder rows.
Run the reached generator closure and expect unchanged outputs for unaffected groups.
`Decision.recordTag` belongs to the separate decision slice; its canonical and target changes must be coordinated there.

## Remaining coordination points

`Record.check` currently returns only `Option Ty`.
It can reject a duplicate supplied name or unknown supplied name, but does not retain that name as a separate diagnostic.
The contract's sentence about refusals naming the offending field should be read against this limitation.
If a distinct supplied-field diagnostic is required, assign that shared result before adding a second checker.
Declared duplicate fields already have the located formation refusal.

The `Machine/Term.lean` module comments currently say the machine needs no type language.
Retained record metadata changes that dependency to `TyEq`, while still excluding the checker and Laws graph.
The source comments and later LCNF lowering input census must describe that exact boundary.

The coordinator will supply the combined base and build slot before implementation.
No Lean, generator, full battery, push or syntax edit was performed while preparing this brief.
