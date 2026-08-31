import Lean
import Effect4.Schema.Payload

/-!
This is the import-boundary half of the payload surface gate.  It deliberately
imports `Effect4.Schema.Payload` alone: the D2–D3 declarations must be present
and owned by that module, D0–D1 must remain owned by `Effect4.Data.Json`, and no
representation, document, or admission declaration may leak downward.
-/

open Lean Elab Command

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
  let env ← getEnv
  for forbidden in [
      "Effect4.Representation".toName, "Effect4.Check".toName,
      "Effect4.ReferenceEntry".toName, "Effect4.Document".toName,
      "Effect4.MultiDocument".toName,
      "Effect4.Representation.FieldAdmissible".toName] do
    if (env.find? forbidden).isSome then
      throwError
        "schema payload import-boundary mismatch: higher declaration {forbidden} is visible from Effect4.Schema.Payload alone"
