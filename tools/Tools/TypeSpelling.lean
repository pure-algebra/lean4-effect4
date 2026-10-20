import Effect4.Codegen.Types
import TypeScript.Render

/-!
# Tools.TypeSpelling — a type as a printed module spells it

The target lanes ask the one compiler about the spelling that a printed module ships: the type
printer `Codegen.Types.ofTy`, rendered flat by the pinned package at the house style
(`TypeScript.Render.type`), as the module writer renders a type (`moduleText`,
`tools/Compiler/Code/Module.lean`). The two producers of the lanes' questions read it,
`Tools.TyVectors` (the assignability pairs) and `Tools.RowTypes` (the rows' signatures).

`Ty.renderRaw` is no spelling of a shipped module. It prints the type as stored, and the printer
normalizes first: at `prod (union "a" "b") bool` the raw text is `readonly ["a" | "b", boolean]`
and the module's is `readonly ["a", boolean] | readonly ["b", boolean]`, the family of
`E4-PRINT-CE-001` (decisions row 392 (2), P3; the codegen review's CG-3).

A type with no printed form has no spelling. A module that states one is refused
(`PrintRefusal.typeSpelling`), so a lane asks nothing about it.
-/

namespace Tools.TypeSpelling

open Effect4.Program

/-- The shipped spelling of a type, or `none` where the type printer has no form for it. -/
def spelled (t : Ty) : Option String :=
  (Effect4.Codegen.Types.ofTy t).map (TypeScript.Render.type TypeScript.house0)

end Tools.TypeSpelling
