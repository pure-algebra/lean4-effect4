import Effect4.Schema.Bridge

/-! RED CONTROL (must fail): claims `ofSchema` reads rc.112's flat three-literal union
(`Schema.Literals(["a","b","c"])`). It reads only two-member unions. Expected: exit 1. -/

set_option autoImplicit false
open Effect4 Effect4.Program

def lit3 : Representation :=
  .union none [] [Schema.literalString "a", Schema.literalString "b", Schema.literalString "c"] .anyOf

#guard Ty.ofSchema lit3 ≠ none
