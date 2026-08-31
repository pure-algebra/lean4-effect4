import Effect4Test.Schema.PayloadSurface

/-!
Transitive ownership check for the required downward module chain:
`Check -> Document -> Representation -> Payload -> Data.Json`.
-/

open Lean Elab Command

private def declarationModule (env : Environment) (name : Name) : CommandElabM Name := do
  let some moduleIndex := env.getModuleIdxFor? name
    | throwError "schema payload ownership mismatch for {name}: declaration is absent or local"
  let some moduleName := env.header.moduleNames[moduleIndex]?
    | throwError "schema payload ownership mismatch for {name}: invalid module index {moduleIndex}"
  pure moduleName

private def requireOwner (name expectedModule : Name) : CommandElabM Unit := do
  let actualModule ← declarationModule (← getEnv) name
  unless actualModule == expectedModule do
    throwError
      "schema payload ownership mismatch for {name}: expected module {expectedModule}, found {actualModule}"

run_cmd do
  requireOwner ``Effect4.Json "Effect4.Data.Json".toName
  requireOwner ``Effect4.ReferenceKey "Effect4.Schema.Payload".toName
  requireOwner ``Effect4.RepresentationAnnotation "Effect4.Schema.Payload".toName
  requireOwner ``Effect4.Representation "Effect4.Schema.Representation".toName
  requireOwner ``Effect4.Check "Effect4.Schema.Representation".toName
  requireOwner ``Effect4.ReferenceEntry "Effect4.Schema.Document".toName
  requireOwner ``Effect4.Document "Effect4.Schema.Document".toName
  requireOwner ``Effect4.MultiDocument "Effect4.Schema.Document".toName
  requireOwner ``Effect4.Representation.FieldAdmissible "Effect4.Schema.Check".toName
  requireOwner ``Effect4.Document.FieldAdmissible "Effect4.Schema.Check".toName

#effect4_check_declaration_owners Effect4.Schema.Check [
  Effect4.Annotations.FieldAdmissible,
  Effect4.Annotations.fieldAdmissible,
  Effect4.Annotations.fieldAdmissible_iff,
  Effect4.Annotations.fieldAdmissible_none,
  Effect4.Annotations.fieldAdmissible_some_iff,
  Effect4.Representation.FieldAdmissible,
  Effect4.Representation.fieldAdmissible,
  Effect4.Representation.fieldAdmissible_iff,
  Effect4.Check.FieldAdmissible,
  Effect4.Check.fieldAdmissible,
  Effect4.Check.fieldAdmissible_iff,
  Effect4.Representation.fieldAdmissible_declaration_iff,
  Effect4.Representation.fieldAdmissible_reference_iff,
  Effect4.Representation.fieldAdmissible_suspend_iff,
  Effect4.Representation.fieldAdmissible_null_iff,
  Effect4.Representation.fieldAdmissible_undefined_iff,
  Effect4.Representation.fieldAdmissible_void_iff,
  Effect4.Representation.fieldAdmissible_never_iff,
  Effect4.Representation.fieldAdmissible_unknown_iff,
  Effect4.Representation.fieldAdmissible_any_iff,
  Effect4.Representation.fieldAdmissible_string_iff,
  Effect4.Representation.fieldAdmissible_number_iff,
  Effect4.Representation.fieldAdmissible_boolean_iff,
  Effect4.Representation.fieldAdmissible_bigint_iff,
  Effect4.Representation.fieldAdmissible_symbol_iff,
  Effect4.Representation.fieldAdmissible_literal_string_iff,
  Effect4.Representation.fieldAdmissible_literal_number_iff,
  Effect4.Representation.fieldAdmissible_literal_bigint_iff,
  Effect4.Representation.fieldAdmissible_literal_boolean_iff,
  Effect4.Representation.fieldAdmissible_toLiteralValue_iff,
  Effect4.Representation.fieldAdmissible_toLiteralValue_of_finite,
  Effect4.Representation.fieldAdmissible_uniqueSymbol_iff,
  Effect4.Representation.fieldAdmissible_objectKeyword_iff,
  Effect4.Representation.fieldAdmissible_enum_iff,
  Effect4.Representation.fieldAdmissible_templateLiteral_iff,
  Effect4.Representation.fieldAdmissible_arrays_iff,
  Effect4.Representation.fieldAdmissible_objects_iff,
  Effect4.Representation.fieldAdmissible_union_iff,
  Effect4.Check.fieldAdmissible_filter_iff,
  Effect4.Check.fieldAdmissible_filterGroup_iff,
  Effect4.Document.FieldAdmissible,
  Effect4.Document.fieldAdmissible,
  Effect4.Document.fieldAdmissible_iff,
  Effect4.Document.fieldAdmissible_mk_iff,
  Effect4.MultiDocument.FieldAdmissible,
  Effect4.MultiDocument.fieldAdmissible,
  Effect4.MultiDocument.fieldAdmissible_iff,
  Effect4.MultiDocument.fieldAdmissible_mk_iff,
  Effect4.Annotations.not_fieldAdmissible_nonFinite,
  Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotations,
  Effect4.Representation.not_fieldAdmissible_nonFiniteElementAnnotations,
  Effect4.Representation.not_fieldAdmissible_nonFinitePropertyAnnotations,
  Effect4.Check.not_fieldAdmissible_nonFiniteAnnotations,
  Effect4.Representation.not_fieldAdmissible_emptyReferenceKey,
  Effect4.Representation.not_fieldAdmissible_emptyAnnotationId,
  Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotationPayload,
  Effect4.Representation.not_fieldAdmissible_nonFiniteLiteral,
  Effect4.Representation.not_fieldAdmissible_suspendChecks,
  Effect4.Check.not_fieldAdmissible_emptyFilterGroup,
  Effect4.MultiDocument.not_fieldAdmissible_emptyRoots,
  Effect4.Representation.not_fieldAdmissible_throughFilterSchemas,
  Effect4.Representation.fieldAdmissible_nonEmptyReferenceKey,
  Effect4.Representation.fieldAdmissible_finiteLiteral,
  Effect4.Representation.fieldAdmissible_suspendEmptyChecks,
  Effect4.Representation.fieldAdmissible_nonFiniteEnumValue,
  Effect4.Representation.fieldAdmissible_nonFinitePropertyKey,
  Effect4.Representation.fieldAdmissible_aliasedEnum,
  Effect4.Representation.fieldAdmissible_optionalBeforeRequiredElement,
  Effect4.Representation.fieldAdmissible_duplicatePropertyKeys,
  Effect4.Document.fieldAdmissible_danglingReference,
  Effect4.Document.fieldAdmissible_deadReferenceEntry,
  Effect4.Document.fieldAdmissible_emptyTableKey,
  Effect4.MultiDocument.fieldAdmissible_emptyTableKey,
  Effect4.MultiDocument.fieldAdmissible_two_roots]
