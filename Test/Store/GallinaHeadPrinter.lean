import OCaml5.Lcnf.Gallina
import Lean

namespace Test.Store.GallinaHeadPrinter

/-- A value parameter must not be silently printed as a type parameter. The printer gathers its
refusals in its state (`OCaml5.Lcnf.Gallina.Refusal`, M4); this one is no refusal of a construct
but an error, raised before any is gathered, so the run starts from no refusal. -/
structure Indexed (count : Nat) where
  value : Nat

/-- error: Gallina: type parameter count is not Type -/
#guard_msgs in
run_meta do
  let env ← Lean.getEnv
  let spec : OCaml5.Lcnf.Gallina.Spec :=
    {decls := [], types := [], knownTypes := [], abstractTypes := [],
     variableNamespaces := [], requires := []}
  discard <| (OCaml5.Lcnf.Gallina.typeText env spec ``Indexed).run #[]

end Test.Store.GallinaHeadPrinter
