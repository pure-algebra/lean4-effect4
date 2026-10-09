import Test.Program.PartitionedSemaphorePrograms
import Effect4.Emit
import TypeScript.Render

/-!
Finite checked emissions of the scalar callers.
Placement: readers of checked module emission and its read-back, R8;
finite controls of partitioned-semaphore-bookkeeping, R10.
TypeScript compilation and execution consume these exact emitted declarations separately.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.PartitionedSemaphoreFaces
open Effect4 Effect4.Program
open Test.Program.PartitionedSemaphorePrograms

def readsBack (c : Case) : Bool :=
  match Api.Author.program c.src with
  | .error _ => false
  | .ok built => match Api.emitModule "main" built.program built.table with
    | .error _ => false
    | .ok emitted => decide (Api.readModule emitted.module built.table = .ok built.program)

#guard cases.all readsBack
#guard ((Api.Author.program (attempt 5 1 2)).toOption.map (·.ty)) =
  some (EffTy.pure (.prod .bool (.tuple [.nat, .nat, .nat])))
-- Rendered bytes stay inside the guard, outside battery declarations.
#guard ((Api.Author.program (attempt 5 1 2)).toOption.bind fun built =>
  (Api.emitModule "main" built.program built.table).toOption.map fun emitted =>
    String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))).any
      fun text => (text.splitOn "Ref.modify(").length == 3

end Test.Program.PartitionedSemaphoreFaces
