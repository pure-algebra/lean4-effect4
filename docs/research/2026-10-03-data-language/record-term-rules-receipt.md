# Record term typing and authoring stage

This checked stage unblocks the coordinator's Program codec regeneration.
The `Laws/Program/Signature.lean` proof migration and target-dependent formation fixture remain for the final combined pass.
The operations seat still owns term evaluation membership, progress and handle-containment proofs.

Stage base: source `70d35a9d` plus generated Fold `33b5d1e2`.
The local generated-Fold equivalent is `2f6f4521`.
Dependencies include checked record operations `6a02b2b8` and `5b074be3`.
Branch: `codex/data-admission`.

## Changes

Record construction checks raw metadata, then checks supplied argument types against the full declaration.
Direct string literals retain their literal type within construction and overwrite.
The outer atom flag does not change a compound record operation's rule.
Required and optional reads call the same record type helper under their stored mode.
Overwrite derives the resulting record type; it does not claim input-output record subtyping.

The raw annotation collector composes generated program views with generated term and cause folds.
It visits term leaves, cause leaves, optional terms and the existing cursor annotation.
Formation expands these annotations into subtype occurrences.
The integer-profile scan reuses the same annotations, keeping the existing cursor path and DI-92 restriction.
Formation, typing, integer profile, inhabitance and the other program admission judgments remain separate.

The authoring module adds `record`, `field`, `optionalField` and `recordSet` to the existing scope reader.
The record builder accepts a full field declaration and named supplied sources.
It retains absent optional fields and resolves child names in order at the existing term path.
Four scope theorems certify the reconstructed terms. They do not claim formation or typing from name resolution.

The source-stage brief contains the five-part proof placement.
This stage extends the existing `argTy_cases`, `argTy_weaken`, `argsTy_weaken` and `tagTest?_weaken` laws.
Their consumers remain term evaluation, binder weakening and the existing checker.
The four new authoring scope laws serve `TermSrc.Scoped`, with concrete record-builder examples.
The shared annotation collection serves `raw-formation` and the existing DI-92 scan.
No theorem premise was weakened and no new axiom was introduced.

## Verification

```text
LEAN_NUM_THREADS=3 lake build Effect4.Program.Native Effect4.Program.Admission Effect4.Program.Authoring.Records Effect4.Laws.Program.Authoring.Records
PASS: 230 jobs

LEAN_NUM_THREADS=3 lake build Test.Program.RecordTerms Test.Program.AuthoringRecords
PASS: 232 jobs

git diff --check
PASS
```

The core fixture contains 47 finite guards. The authoring fixture contains 10 finite guards and four scope examples.
Controls include missing required fields, duplicate declarations or supplied names, wrong types, unknown fields and mismatched column lengths.
They cover nested optional presence, union branch refusal, literal discriminants and a general string that cannot satisfy a literal declaration.
The annotation tests visit statements, causes, optional interruptors, layers and nested atom arguments.
A discarded integer-typed record is still refused, and the old cursor refusal path is unchanged.

Axiom queries report `[propext]` for `evalTerm`, `Term.weaken_eq_lit`, `instDecidableEqTerm` and `tagTest?_weaken`.
They report `[propext, Quot.sound]` for `argTy_weaken`, `argTy_cases`, `Formation.checkInput_eq_none_iff` and all four authoring scope laws.
The latter declarations are `Authoring.record_scoped`, `field_scoped`, `optionalField_scoped` and `recordSet_scoped`.
Logs: `/tmp/record-term-rules-stage.log` and `/tmp/record-term-rules-fixtures.log`.

Intermediate failures were an unused simplification argument, reserved local binder names and one ambiguous fixture type annotation.
They were repaired locally; the final commands above passed.
No full battery, generator, target check or root axiom gate ran in this stage.
The Lean slot is released.

## Integration requirements

The coordinator adds the new authoring module at the application import and the scope-law module at the Laws root.
The focused fixtures are `Test.Program.RecordTerms` and `Test.Program.AuthoringRecords`.
Program canonical generation still needs `FieldReadMode` and `Ty` before `Term`.
The coordinator owns generated outputs and policy measurements.
The operations and target seats retain their assigned source and proof files.

The core branch keeps two final-consumer edits outside this stage commit:
`Laws/Program/Signature.lean` and `Test/Program/FormationContract.lean`.
They will be checked and committed when the target traversal dependencies are restored.
