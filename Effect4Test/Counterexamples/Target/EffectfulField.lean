import Effect4.Target.TypeScript.EffectfulField

/-!
Executable witnesses for `E4-TARGET-CE-005` through `E4-TARGET-CE-008`.
-/

namespace Effect4Test.Counterexamples.Target.EffectfulField

open Effect4
open Effect4.Target.TypeScript

private def spec : EffectfulFieldSpec where
  alphabet := { value := 7 }
  readOperation := { value := 11 }
  writeOperation := { value := 12 }

private def valid : AnnotationEntry := EffectfulFieldSpec.annotationKey.entry spec

private def binding (operation : Nat) : EffectfulField.OperationBinding where
  alphabet := { value := 7 }
  operation := { value := operation }
  serviceName := "UserFieldPolicy"
  serviceImport := "./policy.js"
  methodName := if operation = 11 then "readEmail" else "writeEmail"
  errorType := if operation = 11 then "ReadEmailError" else "WriteEmailError"
  errorImport := "./model.js"

private def requestWith (annotations : Annotations)
    (read : EffectfulField.OperationBinding := binding 11) :
    EffectfulField.Request where
  sourceType := "User"
  sourceImport := "./model.js"
  property := Schema.property "email" Schema.string false false annotations
  read := read
  write := binding 12

/-! `E4-TARGET-CE-005`: malformed same-name evidence beside one valid marker
must not disappear through a typed annotation projection. -/

#guard !EffectfulField.requestReady (requestWith
  (some [{ key := EffectfulFieldSpec.annotationKey.name, payload := .null }, valid]))

#guard !EffectfulField.requestReady (requestWith (some [valid, valid]))

/-! `E4-TARGET-CE-006`: local operation equality does not erase alphabet
identity. -/

private def wrongAlphabet : EffectfulField.OperationBinding :=
  { binding 11 with alphabet := { value := 8 } }

#guard !EffectfulField.requestReady (requestWith (some [valid]) wrongAlphabet)

/-! `E4-TARGET-CE-007`: the rendered API retains directional Effect rows and
the rc.112 `Effect.Services` projection. -/

example (source : String)
    (generated : EffectfulField.source? (requestWith (some [valid])) house0 =
      some source) :
    source.contains "Effect.Services<ReturnType<typeof email.get>>" = true /\
    source.contains "Effect.Services<ReturnType<typeof email.replace>>" = true /\
    source.contains "ReadEmailError | WriteEmailError" = true := by
  exact EffectfulField.source_contains_directional_rows generated

/-! `E4-TARGET-CE-008`: checked lowering cannot produce the raw declaration
escape hatch. -/

example {declaration : Decl}
    (lowered : EffectfulField.decl? (requestWith (some [valid])) =
      some declaration) (text : String) : declaration != .raw text :=
  EffectfulField.decl?_never_raw lowered text

end Effect4Test.Counterexamples.Target.EffectfulField
