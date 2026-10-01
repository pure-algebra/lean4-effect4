import Effect4.Schema.Bridge

/-! RED CONTROL (must fail): claims `Ty` reads a record schema. It cannot: `ofSchema` has no
`objects` arm (`src/Effect4/Schema/Bridge.lean`). Expected: `#guard` fails, exit 1. -/

set_option autoImplicit false
open Effect4 Effect4.Program

def userRep : Representation :=
  Schema.struct [Schema.property "id" Schema.number, Schema.property "name" Schema.string]

#guard Ty.ofSchema userRep ≠ none
