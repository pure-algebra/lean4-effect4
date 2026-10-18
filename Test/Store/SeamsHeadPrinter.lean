import OCaml5.Lcnf.Gallina
import Lean

namespace Test.Store.SeamsHeadPrinter

/-- A value parameter must not be silently printed as a type parameter. -/
structure Indexed (count : Nat) where
  value : Nat

/-- error: Gallina: type parameter count is not Type -/
#guard_msgs in
run_meta do
  let env ← Lean.getEnv
  let spec : OCaml5.Lcnf.Gallina.Spec :=
    {decls := [], types := [], knownTypes := [], abstractTypes := [],
     variableNamespaces := [], requires := []}
  discard <| OCaml5.Lcnf.Gallina.typeText env spec ``Indexed

end Test.Store.SeamsHeadPrinter
