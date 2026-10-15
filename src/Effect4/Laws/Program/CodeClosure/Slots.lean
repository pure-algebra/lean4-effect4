import Effect4.Laws.Program.CodeClosure.Qualified.Slots
import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual callback closure retains source point assertions and captured environments.
Consumer: the Prefix callback instance and Timeout's attempt-source refinement.
Reach: existing native and stored names; these predicates establish no initialized history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

abbrev FinAt (point : Point → Prop) (_env : List Val → Prop) := @Qualified.FinAt point _env (Qualified.EnvironmentWrites _env)

abbrev OpAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.OpAt point env (Qualified.EnvironmentWrites env)

abbrev ProgAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.ProgAt point env (Qualified.EnvironmentWrites env)

abbrev StoreNameAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.StoreNameAt point env (Qualified.EnvironmentWrites env)

abbrev StoreActionAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.StoreActionAt point env (Qualified.EnvironmentWrites env)

abbrev StoreThunkAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.StoreThunkAt point env (Qualified.EnvironmentWrites env)

abbrev RegionAt (point : Point → Prop) (_env : List Val → Prop) := @Qualified.RegionAt point _env (Qualified.EnvironmentWrites _env)

abbrev NameAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.NameAt point env (Qualified.EnvironmentWrites env)

abbrev ThunkAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.ThunkAt point env (Qualified.EnvironmentWrites env)

abbrev CodeAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.CodeAt point env (Qualified.EnvironmentWrites env)

end Effect4.Program.CodeClosure.Slots
