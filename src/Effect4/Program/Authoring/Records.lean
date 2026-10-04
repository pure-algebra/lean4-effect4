module

public import Effect4.Program.Authoring

/-! Record builders in the existing scope reader, for decisions row 195.
These functions resolve child names and reconstruct stored terms.
Formation and typing remain the ordinary checked boundaries. -/

@[expose] public section

namespace Effect4.Program.Authoring

/-- Retain the full declaration and elaborate each supplied value in order.
Absent optional fields remain in `fields`, without a supplied value entry. -/
def record (fields : List (String × Bool × Ty)) (present : List (String × TermSrc)) : TermSrc :=
  fun env path => do
    let values ← present.mapM (fun entry => entry.2 env path)
    .ok (.record fields (present.map Prod.fst) (termsOfList values))

/-- Read a required field after resolving the target in the current scope. -/
def field (target : TermSrc) (name : String) : TermSrc := fun env path => do
  let value ← target env path
  .ok (.field .required value name)

/-- Read own-field presence as an outer option, retaining its mode in the term. -/
def optionalField (target : TermSrc) (name : String) : TermSrc := fun env path => do
  let value ← target env path
  .ok (.field .optional value name)

/-- Resolve the target before the replacement and retain the named overwrite. -/
def recordSet (target : TermSrc) (name : String) (replacement : TermSrc) : TermSrc :=
  fun env path => do
    let value ← target env path
    let next ← replacement env path
    .ok (.recordSet value name next)

end Effect4.Program.Authoring
