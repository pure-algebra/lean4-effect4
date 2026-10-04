import Effect4.Program.Authoring

/-! Positional builders in the existing scope reader, for decisions rows 159 and 197.
The checked boundary retains exact arity and rejects an unavailable position. -/

namespace Effect4.Program.Authoring

/-- Resolve the items in order and retain an ordinary variadic atom application. -/
def tuple (items : List TermSrc) : TermSrc := app "tuple" items

/-- Resolve the target and retain the exact natural index as stored data. -/
def tupleAt (target : TermSrc) (index : Nat) : TermSrc := fun env path => do
  let value ← target env path
  .ok (.tupleAt value index)

end Effect4.Program.Authoring
