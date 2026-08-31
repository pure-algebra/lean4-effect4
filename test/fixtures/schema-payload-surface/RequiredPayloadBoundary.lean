import Lean
import Effect4.Schema.Payload

/-!
This is the import-boundary half of the payload surface gate.  It deliberately
imports `Effect4.Schema.Payload` alone: the D2–D3 declarations must be present
and owned by that module, D0–D1 must remain owned by `Effect4.Data.Json`, and no
representation, document, or admission declaration may leak downward.
-/

open Lean Meta Elab Command

private def payloadPublicTypes : List Name :=
  [``Effect4.ReferenceKey, ``Effect4.GlobalSymbolKey, ``Effect4.AnnotationEntry,
   ``Effect4.Annotations, ``Effect4.LiteralValue, ``Effect4.EnumValue,
   ``Effect4.EnumEntry, ``Effect4.PropertyKey,
   ``Effect4.RepresentationAnnotation, ``Effect4.CheckRepresentationAnnotationOf,
   ``Effect4.ElementOf, ``Effect4.PropertySignatureOf, ``Effect4.IndexSignatureOf]

private def d7PublicNames : List Name :=
  ["Effect4.Annotations.FieldAdmissible".toName,
   "Effect4.Annotations.fieldAdmissible".toName,
   "Effect4.Annotations.fieldAdmissible_iff".toName,
   "Effect4.Annotations.fieldAdmissible_none".toName,
   "Effect4.Annotations.fieldAdmissible_some_iff".toName,
   "Effect4.Representation.FieldAdmissible".toName,
   "Effect4.Representation.fieldAdmissible".toName,
   "Effect4.Representation.fieldAdmissible_iff".toName,
   "Effect4.Check.FieldAdmissible".toName,
   "Effect4.Check.fieldAdmissible".toName,
   "Effect4.Check.fieldAdmissible_iff".toName,
   "Effect4.Representation.fieldAdmissible_declaration_iff".toName,
   "Effect4.Representation.fieldAdmissible_reference_iff".toName,
   "Effect4.Representation.fieldAdmissible_suspend_iff".toName,
   "Effect4.Representation.fieldAdmissible_null_iff".toName,
   "Effect4.Representation.fieldAdmissible_undefined_iff".toName,
   "Effect4.Representation.fieldAdmissible_void_iff".toName,
   "Effect4.Representation.fieldAdmissible_never_iff".toName,
   "Effect4.Representation.fieldAdmissible_unknown_iff".toName,
   "Effect4.Representation.fieldAdmissible_any_iff".toName,
   "Effect4.Representation.fieldAdmissible_string_iff".toName,
   "Effect4.Representation.fieldAdmissible_number_iff".toName,
   "Effect4.Representation.fieldAdmissible_boolean_iff".toName,
   "Effect4.Representation.fieldAdmissible_bigint_iff".toName,
   "Effect4.Representation.fieldAdmissible_symbol_iff".toName,
   "Effect4.Representation.fieldAdmissible_literal_string_iff".toName,
   "Effect4.Representation.fieldAdmissible_literal_number_iff".toName,
   "Effect4.Representation.fieldAdmissible_literal_bigint_iff".toName,
   "Effect4.Representation.fieldAdmissible_literal_boolean_iff".toName,
   "Effect4.Representation.fieldAdmissible_toLiteralValue_iff".toName,
   "Effect4.Representation.fieldAdmissible_toLiteralValue_of_finite".toName,
   "Effect4.Representation.fieldAdmissible_uniqueSymbol_iff".toName,
   "Effect4.Representation.fieldAdmissible_objectKeyword_iff".toName,
   "Effect4.Representation.fieldAdmissible_enum_iff".toName,
   "Effect4.Representation.fieldAdmissible_templateLiteral_iff".toName,
   "Effect4.Representation.fieldAdmissible_arrays_iff".toName,
   "Effect4.Representation.fieldAdmissible_objects_iff".toName,
   "Effect4.Representation.fieldAdmissible_union_iff".toName,
   "Effect4.Check.fieldAdmissible_filter_iff".toName,
   "Effect4.Check.fieldAdmissible_filterGroup_iff".toName,
   "Effect4.Document.FieldAdmissible".toName,
   "Effect4.Document.fieldAdmissible".toName,
   "Effect4.Document.fieldAdmissible_iff".toName,
   "Effect4.Document.fieldAdmissible_mk_iff".toName,
   "Effect4.MultiDocument.FieldAdmissible".toName,
   "Effect4.MultiDocument.fieldAdmissible".toName,
   "Effect4.MultiDocument.fieldAdmissible_iff".toName,
   "Effect4.MultiDocument.fieldAdmissible_mk_iff".toName,
   "Effect4.Annotations.not_fieldAdmissible_nonFinite".toName,
   "Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotations".toName,
   "Effect4.Representation.not_fieldAdmissible_nonFiniteElementAnnotations".toName,
   "Effect4.Representation.not_fieldAdmissible_nonFinitePropertyAnnotations".toName,
   "Effect4.Check.not_fieldAdmissible_nonFiniteAnnotations".toName,
   "Effect4.Representation.not_fieldAdmissible_emptyReferenceKey".toName,
   "Effect4.Representation.not_fieldAdmissible_emptyAnnotationId".toName,
   "Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotationPayload".toName,
   "Effect4.Representation.not_fieldAdmissible_nonFiniteLiteral".toName,
   "Effect4.Representation.not_fieldAdmissible_suspendChecks".toName,
   "Effect4.Check.not_fieldAdmissible_emptyFilterGroup".toName,
   "Effect4.MultiDocument.not_fieldAdmissible_emptyRoots".toName,
   "Effect4.Representation.not_fieldAdmissible_throughFilterSchemas".toName,
   "Effect4.Representation.fieldAdmissible_nonEmptyReferenceKey".toName,
   "Effect4.Representation.fieldAdmissible_finiteLiteral".toName,
   "Effect4.Representation.fieldAdmissible_suspendEmptyChecks".toName,
   "Effect4.Representation.fieldAdmissible_nonFiniteEnumValue".toName,
   "Effect4.Representation.fieldAdmissible_nonFinitePropertyKey".toName,
   "Effect4.Representation.fieldAdmissible_aliasedEnum".toName,
   "Effect4.Representation.fieldAdmissible_optionalBeforeRequiredElement".toName,
   "Effect4.Representation.fieldAdmissible_duplicatePropertyKeys".toName,
   "Effect4.Document.fieldAdmissible_danglingReference".toName,
   "Effect4.Document.fieldAdmissible_deadReferenceEntry".toName,
   "Effect4.Document.fieldAdmissible_emptyTableKey".toName,
   "Effect4.MultiDocument.fieldAdmissible_emptyTableKey".toName,
   "Effect4.MultiDocument.fieldAdmissible_two_roots".toName]

private def declarationModule (env : Environment) (name : Name) : CommandElabM Name := do
  let some moduleIndex := env.getModuleIdxFor? name
    | throwError "schema payload ownership mismatch for {name}: declaration is absent or local"
  let some moduleName := env.header.moduleNames[moduleIndex]?
    | throwError "schema payload ownership mismatch for {name}: invalid module index {moduleIndex}"
  pure moduleName

private def requireOwners (expectedModule : Name) (names : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for name in names do
    let actualModule ← declarationModule env name
    unless actualModule == expectedModule do
      throwError
        "schema payload ownership mismatch for {name}: expected module {expectedModule}, found {actualModule}"

private def isGeneratedTypeCompanion (expected : List Name) (name : Name) : Bool :=
  match name with
  | .str parent suffix =>
      (suffix == "noConfusionType" || suffix == "ctorElimType") &&
        expected.contains parent
  | _ => false

private def isPublicTypeDeclaration (expected : List Name)
    (name : Name) (info : ConstantInfo) : MetaM Bool := do
  if name.isInternal then
    return false
  match info with
  | .inductInfo _ => return true
  | .defnInfo definition =>
      match definition.hints with
      | .abbrev =>
          if isGeneratedTypeCompanion expected name then
            return false
          forallTelescopeReducing info.type fun _ result => do
            return (← whnf result).isSort
      | _ => return false
  | _ => return false

private def requireExactPayloadPublicTypes : MetaM Unit := do
  let env ← getEnv
  let expectedModule := "Effect4.Schema.Payload".toName
  let mut actual : List Name := []
  for (name, info) in env.constants.toList do
    let owner := do
      let moduleIndex ← env.getModuleIdxFor? name
      env.header.moduleNames[moduleIndex]?
    if owner == some expectedModule then
      if ← isPublicTypeDeclaration payloadPublicTypes name info then
        actual := name :: actual
  let unexpected := actual.filter fun name => !payloadPublicTypes.contains name
  let missing := payloadPublicTypes.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    throwError
      "schema payload public type census mismatch: unexpected {unexpected.reverse}; missing {missing}"

run_cmd do
  let importedModules := (← getEnv).header.moduleNames
  for forbiddenModule in [
      "Effect4.Schema.Representation".toName,
      "Effect4.Schema.Document".toName,
      "Effect4.Schema.Check".toName,
      "Effect4.Schema.Value".toName] do
    if importedModules.contains forbiddenModule then
      throwError
        "schema payload import-boundary mismatch: forbidden upward module {forbiddenModule} is imported by Effect4.Schema.Payload"
  requireOwners "Effect4.Data.Json".toName [
    ``Effect4.Float64, ``Effect4.Float64.mk, ``Effect4.Float64.bits,
    ``Effect4.Json, ``Effect4.Json.null, ``Effect4.Json.bool,
    ``Effect4.Json.number, ``Effect4.Json.str, ``Effect4.Json.arr, ``Effect4.Json.obj
  ]
  requireOwners "Effect4.Schema.Payload".toName [
    ``Effect4.ReferenceKey, ``Effect4.ReferenceKey.mk, ``Effect4.ReferenceKey.value,
    ``Effect4.GlobalSymbolKey, ``Effect4.GlobalSymbolKey.mk, ``Effect4.GlobalSymbolKey.key,
    ``Effect4.AnnotationEntry, ``Effect4.AnnotationEntry.mk,
    ``Effect4.AnnotationEntry.key, ``Effect4.AnnotationEntry.payload,
    ``Effect4.Annotations,
    ``Effect4.LiteralValue, ``Effect4.LiteralValue.string,
    ``Effect4.LiteralValue.number, ``Effect4.LiteralValue.bigint,
    ``Effect4.LiteralValue.boolean,
    ``Effect4.EnumValue, ``Effect4.EnumValue.string, ``Effect4.EnumValue.number,
    ``Effect4.EnumEntry, ``Effect4.EnumEntry.mk,
    ``Effect4.EnumEntry.name, ``Effect4.EnumEntry.value,
    ``Effect4.PropertyKey, ``Effect4.PropertyKey.string,
    ``Effect4.PropertyKey.number, ``Effect4.PropertyKey.globalSymbol,
    ``Effect4.RepresentationAnnotation, ``Effect4.RepresentationAnnotation.mk,
    ``Effect4.RepresentationAnnotation.id, ``Effect4.RepresentationAnnotation.payload,
    ``Effect4.CheckRepresentationAnnotationOf,
    ``Effect4.CheckRepresentationAnnotationOf.mk,
    ``Effect4.CheckRepresentationAnnotationOf.id,
    ``Effect4.CheckRepresentationAnnotationOf.payload,
    ``Effect4.CheckRepresentationAnnotationOf.schemas,
    ``Effect4.ElementOf, ``Effect4.ElementOf.mk,
    ``Effect4.ElementOf.isOptional, ``Effect4.ElementOf.type,
    ``Effect4.ElementOf.annotations,
    ``Effect4.PropertySignatureOf, ``Effect4.PropertySignatureOf.mk,
    ``Effect4.PropertySignatureOf.name, ``Effect4.PropertySignatureOf.type,
    ``Effect4.PropertySignatureOf.isOptional,
    ``Effect4.PropertySignatureOf.isMutable,
    ``Effect4.PropertySignatureOf.annotations,
    ``Effect4.IndexSignatureOf, ``Effect4.IndexSignatureOf.mk,
    ``Effect4.IndexSignatureOf.parameter, ``Effect4.IndexSignatureOf.type
  ]
  liftTermElabM requireExactPayloadPublicTypes
  let env ← getEnv
  for forbidden in [
      "Effect4.Representation".toName, "Effect4.Check".toName,
      "Effect4.ReferenceEntry".toName, "Effect4.Document".toName,
      "Effect4.MultiDocument".toName,
      "Effect4.Representation.FieldAdmissible".toName] do
    if (env.find? forbidden).isSome then
      throwError
        "schema payload import-boundary mismatch: higher declaration {forbidden} is visible from Effect4.Schema.Payload alone"
  for forbidden in d7PublicNames do
    if (env.find? forbidden).isSome then
      throwError
        "schema payload D7 boundary mismatch: higher admission declaration {forbidden} is visible from Effect4.Schema.Payload alone"
