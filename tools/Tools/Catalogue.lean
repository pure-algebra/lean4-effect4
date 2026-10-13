import Effect4.Program.NativeAtom
import Effect4.Program.AtomInventory
import Effect4.Store.Domain.ProgramWire
import Tools.JsonBridge

/-!
# Tools.Catalogue — what an agent may write, read from the tables

An agent that writes a program as JSON needs three lists: the forms of the program's syntax,
the atoms an `app` may name, and the rows of its application. Each is read from the table that
defines it, so none drifts from the checker or the reader:

- **forms**: the program's shape document (`Canonical.shape`) and the sums it holds inline, each
  spelled as the JSON print spells it: a sum of field-free cases as one of its strings, a list
  sum (`listItem?`) as an array of its item, any other sum as its cases by `_tag` with their
  fields, as the reader takes them (`Canonical.ofJsonAnyOrder`).
- **atoms**: `NativeAtom.all`, each with its row (`NativeAtom.row`) and its typing scheme and
  citation (`NativeAtom.spec`).
- **rows**: the application's row table, by index: `external i` performs row `i`.

Types and rows print as the program's JSON prints them (`printJson`), so an agent copies a type
from here into a program unchanged.

**What it is not.** It decides nothing and names no law of its own. The forms describe the shape
the reader reads; the reader's exactness is `Canonical.ofJsonAnyOrder_exact`. Each atom's scheme
agrees with its row by `NativeAtom.atom_table_wf`.
-/

set_option autoImplicit false

namespace Tools.Catalogue

open Lean (Json toJson)
open Effect4.Program Effect4.Store
open Tools.JsonBridge (printJson)

/-- A shape as a short name: a primitive, a named definition, or a list, an option or a pair
of those. -/
def shapeText : Shape → String
  | .unit => "unit"
  | .bool => "bool"
  | .nat => "nat"
  | .string => "string"
  | .bytes => "bytes"
  | .digest => "digest"
  | .list item => s!"list {shapeText item}"
  | .option item => s!"option {shapeText item}"
  | .pair a b => s!"pair {shapeText a} {shapeText b}"
  | .struct name _ => name
  | .sum name _ => name
  | .ref kind => s!"ref {kind.name}"
  | .anyRef => "anyRef"
  | .named name => name

/-- A case's or a structure's fields: each JSON key with its shape. -/
def fieldsJson (fields : List (String × Shape)) : Json :=
  Json.arr (fields.map fun (key, shape) =>
    Json.mkObj [("key", .str key), ("shape", .str (shapeText shape))]).toArray

/-- One definition of the shape document, as the JSON print spells it: a sum whose cases carry no
field is one of its strings (`allNullary`), a list sum is an array of its item, any other sum is
an object with its case's `_tag` and fields, and a structure is an object of its fields. -/
def formJson (name : String) (shape : Shape) : Json :=
  match shape with
  | .sum _ cases =>
    if allNullary cases then
      Json.mkObj [("name", .str name), ("strings", Json.arr (cases.map fun c => Json.str c.1).toArray)]
    else match listItem? cases with
    | some item => Json.mkObj [("name", .str name), ("array", .str (shapeText item))]
    | none => Json.mkObj [("name", .str name), ("cases", Json.arr (cases.map fun (tag, _, fields) =>
        Json.mkObj [("_tag", .str tag), ("fields", fieldsJson fields)]).toArray)]
  | .struct _ fields => Json.mkObj [("name", .str name), ("fields", fieldsJson fields)]
  | other => Json.mkObj [("name", .str name), ("shape", .str (shapeText other))]

mutual
/-- The sums and structures a shape holds inline, outermost first: those the document's table
does not name, such as an operation or an observer mode. -/
def inlineForms : Shape → List (String × Shape)
  | .list item => inlineForms item
  | .option item => inlineForms item
  | .pair a b => inlineForms a ++ inlineForms b
  | .struct name fields => (name, .struct name fields) :: fieldForms fields
  | .sum name cases => (name, .sum name cases) :: caseForms cases
  | _ => []

/-- The inline forms of a list of fields. -/
def fieldForms : List (String × Shape) → List (String × Shape)
  | [] => []
  | (_, shape) :: rest => inlineForms shape ++ fieldForms rest

/-- The inline forms of a sum's cases. -/
def caseForms : List (String × Nat × List (String × Shape)) → List (String × Shape)
  | [] => []
  | (_, _, fields) :: rest => fieldForms fields ++ caseForms rest
end

/-- The program's forms: the root's shape, every definition of the document, and the sums and
structures held inline. The document binds a shared definition once for each carrier that
reaches it; a form that prints the same as an earlier one is given once. -/
def formsJson : Json :=
  let doc := Canonical.shape NativeEff
  let inner : Shape → List (String × Shape)
    | .sum _ cases => caseForms cases
    | .struct _ fields => fieldForms fields
    | shape => inlineForms shape
  let forms := (("root", doc.root) :: doc.defs.flatMap fun (name, shape) =>
    (name, shape) :: inner shape).map fun (name, shape) => formJson name shape
  Json.arr (forms.foldl (fun (kept : List Json) form =>
    if kept.contains form then kept else kept ++ [form]) []).toArray

/-- Types as the program's JSON prints them. -/
def tysJson (tys : List Ty) : Json := Json.arr (tys.map printJson).toArray

/-- A named rule's name and its parameter. -/
def customJson : NativeAtom.CustomScheme → Json
  | .project second => Json.mkObj [("rule", .str "project"), ("second", .bool second)]
  | .causeTest => Json.mkObj [("rule", .str "causeTest")]
  | .causeError => Json.mkObj [("rule", .str "causeError")]
  | .tuple => Json.mkObj [("rule", .str "tuple")]
  | .sameHandle => Json.mkObj [("rule", .str "sameHandle")]

/-- An atom's typing scheme (`NativeAtom.Scheme`). -/
def schemeJson : NativeAtom.Scheme → Json
  | .mono params answer =>
    Json.mkObj [("_tag", .str "mono"), ("params", tysJson params), ("answer", printJson answer)]
  | .variadic param answer =>
    Json.mkObj [("_tag", .str "variadic"), ("param", printJson param), ("answer", printJson answer)]
  | .poly params answer =>
    Json.mkObj [("_tag", .str "poly"), ("params", tysJson params), ("answer", printJson answer)]
  | .alts cases =>
    Json.mkObj [("_tag", .str "alts"), ("cases", Json.arr (cases.map fun (params, answer) =>
      Json.mkObj [("params", tysJson params), ("answer", printJson answer)]).toArray)]
  | .custom tag => Json.mkObj [("_tag", .str "custom"), ("rule", customJson tag)]

/-- One atom: its name on the wire, its arity (`null` when variadic), its scheme and its
citation. -/
def atomJson (atom : NativeAtom) : Json :=
  Json.mkObj [("name", .str atom.row.name),
    ("arity", match atom.row.arity with
      | some n => toJson n
      | none => .null),
    ("scheme", schemeJson atom.spec.scheme), ("cite", .str atom.spec.cite)]

/-- The application's rows by index. -/
def rowsJson (rows : RowTable) : Json :=
  Json.arr ((List.range rows.length).zip rows |>.map fun (i, row) =>
    Json.mkObj [("index", toJson i), ("row", printJson row)]).toArray

/-- **The catalogue** at an application's row table. -/
def catalogueJson (rows : RowTable) : Json :=
  Json.mkObj [("forms", formsJson), ("atoms", Json.arr (NativeAtom.all.map atomJson).toArray),
    ("rows", rowsJson rows)]

end Tools.Catalogue
