import Effect4.Codegen.EffectfulField

namespace Effect4.Harness.SchemaEffectfulField

open Effect4
open Effect4.Codegen

private def spec : EffectfulFieldSpec :=
  { alphabet := ⟨7⟩, readOperation := ⟨11⟩, writeOperation := ⟨12⟩ }

private def property : PropertySignature :=
  Schema.property "email" Schema.string false false
    (EffectfulFieldSpec.annotationKey.singleton spec)

private def readBinding : EffectfulField.OperationBinding :=
  { alphabet := ⟨7⟩
    operation := ⟨11⟩
    serviceName := "UserFieldPolicy"
    serviceImport := "./policy.ts"
    methodName := "readEmail"
    errorType := "ReadEmailError"
    errorImport := "./model.ts" }

private def writeBinding : EffectfulField.OperationBinding :=
  { alphabet := ⟨7⟩
    operation := ⟨12⟩
    serviceName := "UserFieldPolicy"
    serviceImport := "./policy.ts"
    methodName := "writeEmail"
    errorType := "WriteEmailError"
    errorImport := "./model.ts" }

private def request : EffectfulField.Request :=
  { sourceType := "User"
    sourceImport := "./model.ts"
    property
    read := readBinding
    write := writeBinding }

def generate : IO Unit :=
  match EffectfulField.generate? request TypeScript.house0 with
  | some source => IO.print source
  | none => throw <| IO.userError "effectful-field request was refused"

end Effect4.Harness.SchemaEffectfulField

def main : IO Unit := Effect4.Harness.SchemaEffectfulField.generate
