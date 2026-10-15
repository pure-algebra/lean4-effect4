import Effect4.Laws.Program.CodeClosure.Qualified.Stored
import Effect4.Laws.Program.CodeClosure.Slots
import Effect4.Laws.Program.CompileInduction

/-!
# Source scope through stored program interpretation

Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: Prefix callbacks and Timeout's source refinement.
The laws interpret the existing synthetic program and finalizer names.
They retain foreign captures through every wrapper, without treating stored syntax as opaque.
The native history bridge consumes these laws for saved callbacks and finalizer execution.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

abbrev finProgram_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.finProgram_at point env (Qualified.EnvironmentWrites env)

abbrev progOf_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.progOf_at point env (Qualified.EnvironmentWrites env)

abbrev store_contA_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.store_contA_at point env (Qualified.EnvironmentWrites env)

abbrev store_contE_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.store_contE_at point env (Qualified.EnvironmentWrites env)

abbrev store_cancel_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.store_cancel_at point env (Qualified.EnvironmentWrites env)

abbrev completion_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.completion_at point env (Qualified.EnvironmentWrites env)

end Effect4.Program.CodeClosure.Slots
