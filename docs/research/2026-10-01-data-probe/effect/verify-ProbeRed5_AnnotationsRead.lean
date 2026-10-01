import Effect4.Schema.Bridge

/-! RED CONTROL (must fail): claims `ofSchema` tells a `parseOptions`-annotated string schema from
the plain one. It cannot: annotations are not read (`Schema/Bridge.lean`, `ofSchema` docstring).
Expected: the `#guard` fails, exit 1. -/

set_option autoImplicit false
open Effect4 Effect4.Program

def strictAnn : Annotations :=
  some [⟨"parseOptions", .obj [("onExcessProperty", .str "error")]⟩]

#guard Ty.ofSchema (.string strictAnn []) ≠ Ty.ofSchema Schema.string
