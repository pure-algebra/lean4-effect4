import Effect4.Program.Authoring

/-! String-map builders in the existing scope reader, for decisions rows 166 and 197.
Each builder resolves names and applies the ordinary native atom.
The ordinary checker and map value semantics remain the owners of typing and evaluation. -/

namespace Effect4.Program.Authoring

/-- Construct an empty string map. -/
def mapEmpty : TermSrc := app "mapEmpty" []

/-- Read own-key presence as an outer option. -/
def mapGet (target key : TermSrc) : TermSrc := app "mapGet" [target, key]

/-- Insert a value without changing the input map. -/
def mapSet (target key value : TermSrc) : TermSrc := app "mapSet" [target, key, value]

/-- List keys in canonical UTF-8 order. -/
def mapKeys (target : TermSrc) : TermSrc := app "mapKeys" [target]

/-- List ordinary key-value pairs in canonical UTF-8 order. -/
def mapEntries (target : TermSrc) : TermSrc := app "mapEntries" [target]

/-- Construct a map from ordinary pairs, retaining the last value for each repeated key. -/
def mapFromEntries (entries : TermSrc) : TermSrc := app "mapFromEntries" [entries]

end Effect4.Program.Authoring
