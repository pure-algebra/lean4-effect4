import Effect4.Schema.Authoring

/-! Representative construction receipts for the Schema authoring facade. -/

namespace Test.Schema.AuthoringContract

open Effect4

private def nameSchema : Representation :=
  Effect4.Schema.struct [Effect4.Schema.property "name" Effect4.Schema.string]

#guard Effect4.Schema.Check.pattern "^[a-z]+$" =
  Effect4.Check.filter
    { id := "effect/schema/isPattern"
      payload := .obj [("source", .str "^[a-z]+$"), ("flags", .str "")]
      schemas := none }
    none false

#guard Effect4.Schema.withCheck Effect4.Schema.string Effect4.Schema.Check.trimmed =
  some (.string none [Effect4.Schema.Check.trimmed])

#guard Effect4.Schema.withCheck (Effect4.Schema.reference "Node")
    Effect4.Schema.Check.trimmed = none

#guard Effect4.Schema.withCheck (Effect4.Schema.suspend Effect4.Schema.string)
    Effect4.Schema.Check.trimmed = none

#guard nameSchema = .objects none []
  [{ name := .string "name", type := .string none [], isOptional := false,
     isMutable := false, annotations := none }] []

end Test.Schema.AuthoringContract
