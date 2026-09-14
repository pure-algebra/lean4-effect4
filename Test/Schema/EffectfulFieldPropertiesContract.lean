import Effect4.Schema.EffectfulField

/-!
# Effectful-field property discovery surface

Breaker-owned declaration and reduction battery for
`Test/contracts/schema-effectful-field-properties.contract.md`.
-/

namespace Test.Schema.EffectfulFieldPropertiesContract

open Effect4

universe u

private def spec : EffectfulFieldSpec where
  alphabet := { value := 7 }
  readOperation := { value := 11 }
  writeOperation := { value := 12 }

private def marked : PropertySignatureOf Nat where
  name := .string "count"
  type := 0
  isOptional := false
  isMutable := true
  annotations := EffectfulFieldSpec.annotationKey.singleton spec

private def unmarked : PropertySignatureOf Nat :=
  { marked with annotations := none }

#guard marked.effectfulFieldSpec = some spec
#guard marked.hasEffectfulField = true
#guard unmarked.effectfulFieldSpec = none
#guard unmarked.hasEffectfulField = false

example : EffectfulFieldSpec.RawAdmissible marked.annotations := by
  exact ⟨spec, rfl⟩

private def schemaProperty : PropertySignature :=
  { name := .string "count"
    type := .number none []
    isOptional := false
    isMutable := true
    annotations := EffectfulFieldSpec.annotationKey.singleton spec }

#guard Representation.effectfulFieldProperties
    (.objects none [] [schemaProperty] []) = [(schemaProperty, spec)]

end Test.Schema.EffectfulFieldPropertiesContract
