import ProbeU.Generic

/-!
# Probe U — the classifier table's row type

One constructor's answers to the five questions the classifier traversals of `Ty` ask (the
table is `U/tables/ty-classes.json`, emitted as `tyClasses`).
-/

set_option autoImplicit false

namespace ProbeU

/-- One constructor's answers. -/
structure ClassRow where
  /-- The node is a template parameter. -/
  param : Bool
  /-- The node holds no handle (`handleFreeAlg`, `Laws/Program/Typed/Membership.lean:2264`). -/
  handleFree : Bool
  /-- The JSON codec has an arm for the node (`Codec.isSupported`, `Schema/Codec.lean:42`). -/
  codec : Bool
  /-- A parameter may sit below this head (`valueVarsAlg`, `Laws/Program/TypeAlgebra.lean:1197`). -/
  valueFormer : Bool
  /-- Inference reads this head's children by position (`Ty.templateAdmissible`,
  `Laws/Program/Template.lean:264`). -/
  positional : Bool

end ProbeU
