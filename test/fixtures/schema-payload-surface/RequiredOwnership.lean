import Lean
import Effect4.Schema.Check

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
