import Effect4.Program.TyFoldExtras
import Effect4.Schema.Template
import Effect4.Schema.Bridge

/-!
# The face table of `Ty`: one Schema template per constructor (decisions row 182 (a), slice C)

The Schema face of `Ty` (`Schema.Bridge.schema`) written once as data: each constructor's node of
rc.112's Schema IR, its children as references and its payload at the mark (`Schema.Template`), and
one generic fold that fills each node's row with its payload and its children's faces.

The table is a value of `TyTable`, which is generated from `Ty`'s declaration (`TyFoldExtras`). A
constructor appended to `Ty` is a missing field here, so the table does not elaborate until its row
is written. A row for no constructor, or a second row for one, does not elaborate either. Every
column is typed: the Schema column is checked Schema IR, not text. The agreement with the hand fold
is `Test/Program/TyTables.lean` (`schema_eq_face`). Moving `Schema.Bridge.schema` itself onto this
fold, through the generated structural expansion and its `eq_cata` connector, is the row's next step.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Schema.Template

/-- One constructor's faces: today, the Schema face. -/
structure FaceRow where
  /-- The constructor's node of rc.112's Schema IR, its children and payload as holes. -/
  schema : Representation

/-- An argument's string payload, where it is one. -/
def TyArgF.str? {R : Type} : TyArgF R → Option String
  | .str s => some s
  | _ => Option.none

/-- **The Schema face**: each node's row filled with its string payload and its children's faces,
in declaration order. -/
def TyTable.schemaFace (tbl : TyTable FaceRow) : TyAlgebra (fun _ => Representation) :=
  TyAlgebra.ofLayer fun c args =>
    fill (tbl.get c).schema (args.findSome? TyArgF.str?) (args.flatMap TyArgF.kids)

/-- The face table of `Ty`. -/
def tyFaces : TyTable FaceRow where
  never := ⟨Schema.never⟩
  unit := ⟨Schema.void⟩
  nat := ⟨.number none [Schema.Bridge.isIntCheck, Schema.Bridge.nonNegativeCheck]⟩
  int := ⟨.number none [Schema.Bridge.isIntCheck]⟩
  string := ⟨Schema.string⟩
  bool := ⟨Schema.boolean⟩
  handle := ⟨.declaration ⟨leafMark, .null⟩ none [] []⟩
  option := ⟨.declaration ⟨"effect/schema/Option", .null⟩ none [child 0] []⟩
  list := ⟨Schema.array (child 0)⟩
  prod := ⟨Schema.tuple [Schema.element (child 0), Schema.element (child 1)]⟩
  except := ⟨.declaration ⟨"effect/schema/Result", .null⟩ none [child 1, child 0] []⟩
  exitOf := ⟨.declaration ⟨"effect/schema/Exit", .null⟩ none
    [child 0, child 1, Schema.Bridge.defectRep] []⟩
  causeOf := ⟨.declaration ⟨"effect/schema/Cause", .null⟩ none [child 0, Schema.Bridge.defectRep] []⟩
  fiberOf := ⟨.declaration ⟨"effect/schema/Fiber", .null⟩ none [child 0, child 1] []⟩
  union := ⟨.union none [] [child 0, child 1] .anyOf⟩
  lit := ⟨Schema.literalString leafMark⟩
  refOf := ⟨.declaration ⟨"effect/schema/Ref", .null⟩ none [child 0] []⟩
  deferredOf := ⟨.declaration ⟨"effect/schema/Deferred", .null⟩ none [child 0, child 1] []⟩
  var := ⟨.declaration ⟨"effect/schema/TypeParameter", .null⟩ none [] []⟩
  unknown := ⟨.unknown none []⟩
  -- the data wave's forms, refused by name until the Schema commit lowers each (decisions row 162)
  record := ⟨Schema.Bridge.unlowered "record"⟩
  map := ⟨Schema.Bridge.unlowered "map"⟩
  tuple := ⟨Schema.Bridge.unlowered "tuple"⟩
  app := ⟨Schema.Bridge.unlowered "app"⟩
  null := ⟨Schema.Bridge.unlowered "null"⟩
  undefined := ⟨Schema.Bridge.unlowered "undefined"⟩
  number := ⟨Schema.Bridge.unlowered "number"⟩
  bytes := ⟨Schema.Bridge.unlowered "bytes"⟩

end Effect4.Program
