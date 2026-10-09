import Test.Program.RefPrograms
import TypeScript.Render

/-! Finite checked emissions of the Ref callers. Placement: controls of read_print and
read_exact, R8, and ref-steps-agree, R10. Compiler and host checks consume these exact emissions.
No guard here establishes target typing or a host observation. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.RefFaces
open Effect4 Effect4.Program Effect4.Program.Authoring
open Test.Program.RefPrograms

def readsBack (c : Case) : Bool :=
  match Api.Author.program c.src with
  | .error _ => false
  | .ok b => match Api.emitModule "main" b.program b.table with
    | .error _ => false
    | .ok emission => decide (Api.readModule emission.module b.table = .ok b.program)

#guard cases.all readsBack
#guard ((Api.Author.program stringProgram).toOption.map (·.ty)) =
  some (EffTy.pure (.prod .string .string))
#guard ((Api.Author.program handleProgram).toOption.map (·.ty)) =
  some (EffTy.pure (.prod .bool .bool))
-- Rendered bytes stay inside this guard, outside the battery's declaration graph.
#guard ((Api.Author.program (numeric "modify")).toOption.bind fun b =>
  (Api.emitModule "main" b.program b.table).toOption.map fun emission =>
    String.join (emission.module.decls.map (TypeScript.Render.decl TypeScript.house0))).any
      fun text => (text.splitOn "Ref.modify(").length == 2

end Test.Program.RefFaces
