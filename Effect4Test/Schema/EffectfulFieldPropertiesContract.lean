import Effect4.Schema.EffectfulField

/-!
# Effectful-field property discovery surface

Breaker-owned declaration and reduction battery for
`test/contracts/schema-effectful-field-properties.contract.md`.
-/

namespace Effect4Test.Schema.EffectfulFieldPropertiesContract

open Effect4

universe u

#check (@PropertySignatureOf.effectfulFieldSpec.{u} :
  {A : Type u} -> PropertySignatureOf A -> Option EffectfulFieldSpec)

#check (@PropertySignatureOf.hasEffectfulField.{u} :
  {A : Type u} -> PropertySignatureOf A -> Bool)

#check (@PropertySignatureOf.hasEffectfulField_eq_true_iff.{u} :
  {A : Type u} -> forall (property : PropertySignatureOf A),
    property.hasEffectfulField = true <->
      EffectfulFieldSpec.RawAdmissible property.annotations)

#check (Representation.effectfulFieldProperties :
  Representation -> List (PropertySignature × EffectfulFieldSpec))

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

end Effect4Test.Schema.EffectfulFieldPropertiesContract
