import Effect4.Schema.Authoring

/-! Representative construction receipts for the Schema authoring facade. -/

namespace Test.Schema.AuthoringContract

open Effect4

#check (Effect4.Schema.string : Representation)
#check Effect4.Schema.Predicate.decide
#check Effect4.Schema.Predicate.and
#check Effect4.Schema.Predicate.contramap
#check Effect4.Schema.check
#check (@Effect4.Schema.Check.named :
  String → Json → Option (List Representation) → Annotations → Bool → Check)
#check (@Effect4.Schema.withCheck :
  Representation → Check → List Check → Option Representation)

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

private def even (value : Nat) : Bool := value % 2 == 0
private def positive (value : Nat) : Bool := value > 0

#guard Effect4.Schema.check (Effect4.Schema.Predicate.and even positive) 4
#guard !Effect4.Schema.check (Effect4.Schema.Predicate.and even positive) 3
#guard Effect4.Schema.check
  (Effect4.Schema.Predicate.contramap String.length positive) "Lean"

#guard Effect4.Schema.check
  (Effect4.Schema.Predicate.all [even, positive, fun value => value < 10]) 4

#guard Effect4.Schema.check
  (Effect4.Schema.Predicate.any [even, fun value => value == 3]) 3

#guard Effect4.Schema.check (Effect4.Schema.Predicate.each positive) [1, 2, 3]

#guard nameSchema = .objects none []
  [{ name := .string "name", type := .string none [], isOptional := false,
     isMutable := false, annotations := none }] []

end Test.Schema.AuthoringContract
