import Effect4.Target.TypeScript.EffectfulField

/-!
Frozen public surface for the checked effectful-field TypeScript target.
-/

namespace Effect4Test.Target.TypeScript.EffectfulFieldContract

open Effect4
open Effect4.Target.TypeScript

#check (@EffectfulFieldDecl : Type)
#check (@EffectfulFieldDecl.mk :
  String -> String -> String -> String -> String -> String ->
    String -> String -> String -> EffectfulFieldDecl)

#check (@Decl.effectfulField : EffectfulFieldDecl -> Decl)

#check (@EffectfulField.OperationBinding : Type)
#check (@EffectfulField.OperationBinding.mk :
  AlphabetId -> OperationId -> String -> String -> String -> String -> String ->
    EffectfulField.OperationBinding)

#check (@EffectfulField.Request : Type)
#check (@EffectfulField.Request.mk :
  String -> String -> PropertySignature ->
    EffectfulField.OperationBinding -> EffectfulField.OperationBinding ->
      EffectfulField.Request)

#check (@EffectfulField.requestReady : EffectfulField.Request -> Bool)
#check (@EffectfulField.RequestReady : EffectfulField.Request -> Prop)
#check (@EffectfulField.requestReady_iff :
  forall request, EffectfulField.requestReady request = true <->
    EffectfulField.RequestReady request)
#check (@EffectfulField.decl? : EffectfulField.Request -> Option Decl)
#check (@EffectfulField.module? : EffectfulField.Request -> Option Module)
#check (@EffectfulField.source? :
  EffectfulField.Request -> Style -> Option String)
#check (@EffectfulField.generate? :
  EffectfulField.Request -> Style -> Option String)
#check (@EffectfulField.decl?_never_raw :
  forall {request declaration}, EffectfulField.decl? request = some declaration ->
    forall text, declaration != Decl.raw text)

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

#guard EffectfulField.decl? request = some (.effectfulField
  { fieldName := "email"
    sourceType := "User"
    fieldType := "string"
    readService := "UserFieldPolicy"
    readMethod := "readEmail"
    readError := "ReadEmailError"
    writeService := "UserFieldPolicy"
    writeMethod := "writeEmail"
    writeError := "WriteEmailError" })

example : EffectfulField.generate? request house0 =
    EffectfulField.source? request house0 := rfl

end Effect4Test.Target.TypeScript.EffectfulFieldContract
