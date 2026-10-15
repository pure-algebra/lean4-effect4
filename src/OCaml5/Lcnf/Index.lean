import Lean

/-! # OCaml5.Lcnf.Index

An ordered imported module walk builds one lookup index of persisted mono declarations,
including compiler-created declarations with no kernel constant. It never recompiles code. The
route's translator and manifest read it, and so does the conformance tools' validity walk
(`Conform.Lcnf.Validity`). The module also holds the one constructor telescope that the type
generator and the conformance tools' source readers share. -/
namespace OCaml5.Lcnf
open Lean Meta Compiler LCNF
abbrev MonoIndex := Std.HashMap Name (Decl .pure)

def persistedMonoIndex (env : Environment) : MonoIndex := Id.run do
  let mut result := {}
  for i in [:env.header.moduleNames.size] do
    for decl in monoExt.getModuleEntries env i do
      result := result.insert decl.name decl
  return result

def MonoIndex.findIn? (index : MonoIndex) (env : Environment) (name : Name) : Option (Decl .pure) :=
  index[name]? <|> getDeclCore? env monoExt name
/-- One constructor telescope: its parameters and fields as free variables. -/
def withConstructor {α : Type} (name : Name)
    (read : ConstructorVal → Array Expr → MetaM α) : MetaM α := do
  let ci ← getConstInfoCtor name
  forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => read ci xs
end OCaml5.Lcnf
