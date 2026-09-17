import Effect4.Laws.Program.Decision

/-!
# Decision contract — the value-decided fork's carrier (the `select` packet, step 1)

`Decision` (`src/Effect4/Program/Decision.lean`) is read by the runtime (`decide`) and the
checker (`arms`); the pins fix the three decisions on the values and types they see, the
refusals (`none`) on the wrong shapes, and the columns a tag decision accepts
(`Ty.taggedColumn`, `Ty.payloadTy`). The laws (`Laws/Program/Decision.lean`) are printed
at the axiom ceiling.
-/

set_option autoImplicit false

namespace Test.Program.DecisionContract

open Effect4 Effect4.Program Effect4.Store

/-! ## The runtime selection -/

#guard Decision.decide .bool (.bool true) = some (true, none)
#guard Decision.decide .bool (.bool false) = some (false, none)
#guard Decision.decide .bool (.nat 1) = none
#guard Decision.decide .option .none = some (true, none)
#guard Decision.decide .option (.some (.nat 3)) = some (false, some (.nat 3))
#guard Decision.decide .option (.nat 3) = none
#guard Decision.decide (.tag "A") (.list [.str "A", .nat 7]) = some (true, some (.nat 7))
#guard Decision.decide (.tag "A") (.list [.str "B", .nat 7])
  = some (false, some (.list [.str "B", .nat 7]))
#guard Decision.decide (.tag "A") (.nat 1) = some (false, some (.nat 1))

/-! ## The tagged-value reader -/

#guard Val.tagPayload? "A" (.list [.str "A", .nat 7]) = some (.nat 7)
#guard Val.tagPayload? "A" (.list [.str "B", .nat 7]) = none
#guard Val.tagPayload? "A" (.list [.str "A"]) = none
#guard Val.tagPayload? "A" (.pair (.str "A") (.nat 7)) = none

/-! ## The checker's arms -/

/-- A column with one member tagged `A` and a scalar beside it. -/
def column : Ty := .union (.prod (.lit "A") .nat) .string

#guard Decision.arms .bool .bool = some ([], [])
#guard Decision.arms .bool .nat = none
#guard Decision.arms .option (.option .nat) = some ([], [.nat])
#guard Decision.arms .option .nat = none
#guard Decision.arms (.tag "A") column = some ([.nat], [.string])
-- no member carries the tag: refused
#guard Decision.arms (.tag "A") (.union (.prod (.lit "B") .nat) .string) = none
-- a list member is not a tagged column: refused
#guard Decision.arms (.tag "A") (.union (.prod (.lit "A") .nat) (.list .nat)) = none
-- an untagged pair is not a tagged column: refused
#guard Decision.arms (.tag "A") (.union (.prod (.lit "A") .nat) (.prod .nat .nat)) = none

#guard Ty.taggedColumn column = true
#guard Ty.taggedColumn (.list .nat) = false
#guard Ty.payloadTy "A" column = some .nat
#guard Ty.payloadTy "B" column = none

/-! ## The binder counts agree with the arms -/

#guard Decision.binds .bool = (0, 0)
#guard Decision.binds .option = (0, 1)
#guard Decision.binds (.tag "A") = (1, 1)

/-! ## The laws, at the axiom ceiling -/

#print axioms Effect4.Program.Decision.arms_length
#print axioms Effect4.Program.NativeAtom.tagHit_eq
#print axioms Effect4.Program.Ty.payload_hasTy
#print axioms Effect4.Program.Decision.decide_typed

end Test.Program.DecisionContract
