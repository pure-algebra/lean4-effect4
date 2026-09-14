import Effect4.Codegen.EffectfulField

/-!
Frozen public surface for the checked effectful-field TypeScript target.
-/

open TypeScript

namespace Test.Codegen.EffectfulFieldContract

open Effect4
open Effect4.Codegen Effects

private def spec : EffectfulFieldSpec where
  alphabet := { value := 7 }
  readOperation := { value := 11 }
  writeOperation := { value := 12 }

private def property : PropertySignature :=
  Schema.property "email" Schema.string false false
    (EffectfulFieldSpec.annotationKey.singleton spec)

private def readBinding : EffectfulField.OperationBinding where
  alphabet := { value := 7 }
  operation := { value := 11 }
  serviceName := "UserFieldPolicy"
  serviceImport := "./policy.js"
  methodName := "readEmail"
  errorType := "ReadEmailError"
  errorImport := "./model.js"

private def writeBinding : EffectfulField.OperationBinding where
  alphabet := { value := 7 }
  operation := { value := 12 }
  serviceName := "UserFieldPolicy"
  serviceImport := "./policy.js"
  methodName := "writeEmail"
  errorType := "WriteEmailError"
  errorImport := "./model.js"

private def request : EffectfulField.Request where
  sourceType := "User"
  sourceImport := "./model.js"
  property := property
  read := readBinding
  write := writeBinding

#guard EffectfulField.requestReady request

#guard match EffectfulField.decl? request with
  | some (.effectfulField declaration) =>
      declaration.fieldName == "email" &&
      declaration.sourceType == "User" &&
      declaration.fieldType == "string" &&
      declaration.readService == "UserFieldPolicy" &&
      declaration.readMethod == "readEmail" &&
      declaration.readError == "ReadEmailError" &&
      declaration.writeService == "UserFieldPolicy" &&
      declaration.writeMethod == "writeEmail" &&
      declaration.writeError == "WriteEmailError"
  | _ => false

example : EffectfulField.generate? request house0 =
    EffectfulField.source? request house0 := rfl

end Test.Codegen.EffectfulFieldContract
