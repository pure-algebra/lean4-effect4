import Effect4.Arch.Views

/-!
# StdLib.Entry

Owner: one export of the pinned Effect standard library, as store content.

An `Entry` is what the census instrument (`scripts/generate-stdlib-census.ps1`)
reads off the pinned install: the module, the exported name, the declaration
kind and its line; a `FilePin` is the SHA-256 of each file read. An entry's
path in the store is `[module, name]`, so a name in code resolves to its entry
directly, and its digest is the address of the canonical tuple.

The entry is also a schema (`entryDoc`), so the same record crosses to the app
face as data beside its schema.
-/

namespace Effect4.StdLib

open Effect4 Effect4.Schema Effect4.Store Effect4.Arch

/-- The declaration kinds the census recognises. -/
inductive ExportKind where
  | const
  | function
  | class_
  | interface
  | type
  | namespace_
deriving DecidableEq, Repr, Inhabited

def ExportKind.spelling : ExportKind → String
  | .const => "const"
  | .function => "function"
  | .class_ => "class"
  | .interface => "interface"
  | .type => "type"
  | .namespace_ => "namespace"

def ExportKind.all : List ExportKind :=
  [.const, .function, .class_, .interface, .type, .namespace_]

/-- One export of a pinned module. -/
structure Entry where
  module : String
  name : String
  kind : ExportKind
  line : Nat
deriving DecidableEq, Repr, Inhabited

/-- One pinned file. -/
structure FilePin where
  module : String
  file : String
  sha256 : String
deriving DecidableEq, Repr, Inhabited

namespace Entry

/-- Where an entry lives in the store. -/
def path (entry : Entry) : Path := [entry.module, entry.name]

def json (entry : Entry) : Json :=
  .obj
    [ ("module", .str entry.module)
    , ("name", .str entry.name)
    , ("kind", .str entry.kind.spelling)
    , ("line", Json.ofNat entry.line) ]

end Entry

instance : Canonical Entry :=
  ⟨fun entry => encode (entry.module, entry.name, entry.kind.spelling, entry.line)⟩

/-- The schema of an entry. -/
def entryDoc : Document :=
  { representation :=
      struct
        [ property "module" string
        , property "name" string
        , property "kind" (anyOf (literalString "const") (ExportKind.all.tail.map fun k => literalString k.spelling))
        , property "line" number ]
    references := [] }

def FilePin.json (pin : FilePin) : Json :=
  .obj [("module", .str pin.module), ("file", .str pin.file), ("sha256", .str pin.sha256)]

/-- The entries as a store: one content per export, named by its path. -/
def store (entries : List Entry) : Store Entry :=
  entries.foldl (fun s entry => (s.putAt entry.path entry).2) Store.empty

end Effect4.StdLib
