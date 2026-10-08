/-!
Finite review controls for TyModel at 3af74a28.
The runner appends this file to the submitted TyModel declarations.
These controls exercise canonical membership, support and codec admission.
They do not state a new theorem or change a frozen contract.
-/
open TyModel
structure Duplicate where
  a : Bool
  b : Bool
derive_modeled Duplicate (a := "x") (b := "x")
