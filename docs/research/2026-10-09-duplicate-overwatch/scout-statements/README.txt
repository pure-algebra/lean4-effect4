Completed source comparison evidence for 7b73d59c -> 7334f119.

Replay:
  python3 /tmp/effect4-duplicate-overwatch-0647/scout-statements/compare.py

compare.py runs read-only Git commands against immutable commits.
comparison.json retains before/after normalized headers, per-file counts, deleted declarations,
attribute/import checks, reference-scan commands and outputs, and per-file diff hashes.
summary.json is the compact result. review.diff retains the exact reviewed diff.

Original completed current-tree scan commands (primary was clean at 7334f119):
  rg -n 'compileEff_zero|point_refresh|sizeOf_field_lt_record|Typed\.subN_never|Typed\.mem_zip_self|Typed\.complete_cells_length|failureFits_cause|exitOk_failure_error|commandOwner_rupdate|seq_typed_sameError|subN_list_exitOf|machineTyped_of_configTyped|fresh_forks_without_parent|\bsub_sound\b|AnswerDecision\.prepareExternalAnswer_sites|Simulation\.bool_eq_false_of_not' src Test tools scripts generated docs/core docs/ARCHITECTURE.md
  rg -n 'attribute.*(compileEff_zero|point_refresh|sizeOf_field_lt_record|subN_never|mem_zip_self|complete_cells_length|failureFits_cause|exitOk_failure_error|commandOwner_rupdate|seq_typed_sameError|subN_list_exitOf|machineTyped_of_configTyped|fresh_forks_without_parent|sub_sound|prepareExternalAnswer_sites)' src Test tools
Both returned no matches. The immutable replay uses Git grep and additionally distinguishes
shared short names from deleted qualified declarations. The retained full proof-style baseline
reference to FrameOwned.prepareExternalAnswer_sites names the shared surviving original.

Manual source review also compared replacement laws and proof bodies in:
  Laws.Program.Agreement: compileEff_at_zero
  Laws.Program.Guard.FrameOwned: prepareExternalAnswer_sites
  Laws.Program.Guard.Finish: interruptedAt_update
  Laws.Program.Simulation.Hooks: point_congr
  Store.Domain.Store: bool_eq_false_of_not
  Program.Ty: sizeOf_field_lt, mem_zip_self
  Laws.Machine.StoresLaws: DeferredStore.complete_cells_length
  Laws.Program.Bounds: subN_never
  Laws.Program.Typed.Membership: fitsExit_failure_cause
  Laws.Program.Typed.Seq: exitOk_failure_of_errorN, seq_typed, seqGuard_typed, guardBind_typed
  Laws.Program.Typed.Commands.Race: commandOwner_update
  Laws.Program.Typed.Denotation: subN_listExitOf

Result: 21 changed proof files; 1,392 surviving theorem headers match; no changed headers,
imports, or attribute directives. RegistrationYield's caller update is retained in review.diff.
No Lean build, runtime check, or compiled axiom audit belongs to this evidence.
