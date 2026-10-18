# V1 law owner changes

The existing registry pointer `Effect4.Program.cata_eff_congr_on` retains its exact declaration name and statement.
Only its source owner changes, from Laws Signature to core SignatureSupport.
No existing registry pointer loses its declaration in this patch.
The coordinator adds the new checker claims and records the exact `Checked.ask_value` status regression.

## Retained placed declarations

| Declaration | Final owner | Change |
| --- | --- | --- |
| `Effect4.Program.SigApp.withHoles_extends` | Laws Program Sketch | Exact statement retained; proof calls `withHoles_extendsCore` |
| `Effect4.Program.Annotate.check_alg_agreeOn` | Laws Program Typing Restrict | Exact statement retained; proof calls `check_alg_agreeOnCore` |
| `Effect4.Program.Annotate.check_restrict` | Laws Program Typing Restrict | Exact statement retained; proof calls `check_restrictCore` |
| `Effect4.Program.Check.Checked.ask_value` | Laws Program CheckAgreement | Exact old core statement moved; now modulo `combine_deps` |

## Same-name moves to SignatureSupport

All names below retain the prefix `Effect4.Program`.
The final source owner is `src/Effect4/Program/Typing/SignatureSupport.lean`.

From `Laws/Program/Signature.lean`:

- `argTy_congr`, `argsTy_congr`, `termTy_congr`, `causeTy_congr`.
- `SigExtends.refl`, `SigExtends.trans`, `SigExtends.termTy`, `SigExtends.causeTy`, `SigExtends.bodyRequires`, `SigExtends.termUse`.
- `rows_append`, `SigApp.rows_append`, `readsAlg`.
- `cata_eff_congr_on`, `cata_stmt_congr_on`, `cata_stmts_congr_on`, `cata_effs_congr_on`.
- `cata_action_congr_on`, `cata_layer_congr_on`, `cata_layers_congr_on`.
- `SigOkOp`, `SigOkKey`, `SigOkDef`, `SigProgram`.
- `termDiagnostic_ext`, `termRefusal_ext`, `term?_ext`, `cause?_ext`.

From `Laws/Program/Definitions.lean`:

- `Signature.withDefs_dom_of_none`, `Signature.withDefs_rowOf_of_none`.
- `Signature.withDefs_dom_call`, `Signature.withDefs_rowOf_call`.
- `SigExtends.withDefs`, `SigExtends.withParams`.

From `Laws/Program/Typing/CheckCache.lean`:

- `SigData.extends_of_extendsB`.

The `fold_of Annotate.check` declaration moves from Laws Typing Annotate into core `AnnotateFold.lean`.
Its generated declaration names retain the same owner namespace.

## Deleted obsolete cache claims

The following declarations disappear with their old cache representation.
Their prefix is `Effect4.Program.CheckCache`.

- `Entry.Valid`.
- `Entry.compute_valid`.
- `lookup_sound`.
- `insert_valid`.
- `evaluateCandidate_valid_and_sound`.

No pointer in the current `tools/ProofGraph/Registry.lean` names those five declarations.
The existing `bodyAt_sig_index` and `sketchSigData_signature` laws remain in their old Laws owner.
The new certified `Memo` and `HitRule` API replaces the deleted cache claims.

## Registry inspection

The inspection uses production HEAD `0bb42e37d4fa99fd84979df03beb3dd0391a4e98`.
The current explicit moved declaration pointer is the fold claim's `cata_eff_congr_on` witness.
Its exact name survives the move, so its pointer needs no replacement.
The annotated wrappers retain their existing semantic metadata in Laws.
The new core helpers receive no imported metadata reassignment.
