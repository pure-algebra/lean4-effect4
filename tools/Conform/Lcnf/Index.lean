import Lean

/-! An ordered imported module walk builds one lookup index of persisted mono declarations,
including compiler-created declarations with no kernel constant. It never recompiles code. -/
namespace Conform.Lcnf
open Lean Compiler LCNF
abbrev MonoIndex := Std.HashMap Name (Decl .pure)

def persistedMonoIndex (env : Environment) : MonoIndex := Id.run do
  let mut result := {}
  for i in [:env.header.moduleNames.size] do
    for decl in monoExt.getModuleEntries env i do
      result := result.insert decl.name decl
  return result

def MonoIndex.findIn? (index : MonoIndex) (env : Environment) (name : Name) : Option (Decl .pure) :=
  index[name]? <|> getDeclCore? env monoExt name
end Conform.Lcnf
