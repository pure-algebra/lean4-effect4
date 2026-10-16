import Effect4.Program.TyHead
import Effect4.Program.AdmitIn
import Effect4.Program.SigApp
import Effect4.Program.Typing.TermRefusal
import Effect4.Program.Authoring

/-!
# Battery: declared types read by shape, folded at a written field, and admitted at a reply

The readers under a declaration table (`Program/TyHead.lean`, `Program/AdmitIn.lean`; the plan
`docs/research/2026-10-16-usability-scope/wiring-plan.md`) at three tables: a declared record, a
recursive tree, and a declared name for `nat`. Each line is a finite evaluation, or a control
that shows why the table is read (decisions row 301). The laws are
`Laws/Program/TyHead.lean` and `Laws/Program/AdmitIn.lean`.
-/

set_option autoImplicit false

namespace Test.Program.DeclaredTypes

open Effect4 Effect4.Program Effect4.Machine

/-- A declared record: `Todo = {done: boolean, id: number, title: string}`. -/
def todoBody : Ty := .record [("done", false, .bool), ("id", false, .nat), ("title", false, .string)]

/-- The table that declares `Todo`. -/
def todoDecls : TyDecls := [("Todo", todoBody)]

/-- A recursive tree: `Tree = {_tag: "leaf"} | {_tag: "node", children: Tree[], label: string}`. -/
def treeDecls : TyDecls :=
  [("Tree", .union (.record [("_tag", false, .lit "leaf")])
    (.record [("_tag", false, .lit "node"), ("children", false, .list (.handle "Tree")),
      ("label", false, .string)]))]

/-- A declared name for a natural: `Id = number`. -/
def idDecls : TyDecls := [("Id", .nat)]

/-- An unguarded table: `A = A | number`. -/
def loopDecls : TyDecls := [("A", .union (.handle "A") .nat)]

/-- A to-do value. -/
def todo : Val := (Record.build ["done", "id", "title"] [.bool false, .nat 1, .str "milk"]).getD .unit

/-- A leaf and a node that holds it. -/
def leaf : Val := (Record.build ["_tag"] [.str "leaf"]).getD .unit
def node : Val :=
  (Record.build ["_tag", "children", "label"] [.str "node", .list [leaf], .str "root"]).getD .unit

/-- A node whose child is no tree. -/
def badNode : Val :=
  (Record.build ["_tag", "children", "label"] [.str "node", .list [.nat 3], .str "root"]).getD .unit

/-! ## The checker's readers -/

-- finite evaluation: a field read through a declared name answers the field's declared type.
#guard Record.fieldTypeIn todoDecls false (.handle "Todo") "title" == some .string
-- control: the table-free read refuses it, since a declared name reads as a handle there.
#guard Record.fieldType false (.handle "Todo") "title" == none
-- finite evaluation: a field that one member lacks is refused at the union, as the lifted rule
-- refuses it: the leaf has no children.
#guard Record.fieldTypeIn treeDecls false (.handle "Tree") "children" == none
-- finite evaluation: the tag dispatch on a recursive type, and the node arm's children, which
-- keep the declared name inside.
#guard ((Record.tagArmsIn treeDecls "node" (.handle "Tree")).bind fun arms =>
  Record.fieldTypeIn treeDecls false arms.1 "children") == some (.list (.handle "Tree"))
-- control: the table-free dispatch refuses the declared name.
#guard Record.tagArms "node" (.handle "Tree") == none
-- finite evaluation: an unguarded name adds no member when its unfolding returns to it.
#guard Ty.membersIn loopDecls (.handle "A") == [.nat]

/-! ## The fold of a written field -/

-- finite evaluation: a field written at `Todo` takes a member of the body.
#guard (Record.checkIn todoDecls [("v", false, .handle "Todo")] ["v"] [todoBody]).isSome
-- control: the order alone refuses it: the name is nominal.
#guard (Record.check [("v", false, .handle "Todo")] ["v"] [todoBody]).isNone
-- control: a record that lacks a field is not folded.
#guard (Record.checkIn todoDecls [("v", false, .handle "Todo")] ["v"]
  [.record [("id", false, .nat)]]).isNone
-- finite evaluation: a node folds into `Tree` when its children are already trees.
#guard (Record.checkIn treeDecls [("v", false, .handle "Tree")] ["v"]
  [.record [("_tag", false, .lit "node"), ("children", false, .list (.handle "Tree")),
    ("label", false, .string)]]).isSome

/-! ## The term typer under the application's table (`SigApp.signatureIn`) -/

/-- An application that declares `Todo` and `Tree`. -/
def app : SigApp := { types := todoDecls ++ treeDecls }

/-- A record whose one field is written at `Todo`, holding the term `value`. -/
def asTodo (value : Term) : Term :=
  .record [("v", false, .handle "Todo")] ["v"] (Authoring.termsOfList [value])

-- finite evaluation: the typer reads a field through a declared name.
#guard termTy app.signatureIn [.handle "Todo"] (.field .required (.var 0) "title") == some .string
-- control: the table-free signature refuses the same read.
#guard termTy app.signature [.handle "Todo"] (.field .required (.var 0) "title") == none
-- finite evaluation: a field written at `Todo` folds a value of its body, and reading it back
-- gives the name.
#guard termTy app.signatureIn [todoBody] (.field .required (asTodo (.var 0)) "v") ==
  some (.handle "Todo")
-- control: the table-free signature refuses the fold: the name is nominal there.
#guard termTy app.signature [todoBody] (.field .required (asTodo (.var 0)) "v") == none
-- finite evaluation: the refusal of a field that `Todo` lacks is located at the record.
#guard (TermRefusal.diagnose app.signatureIn [.handle "Todo"]
  (.field .required (.var 0) "owner")).isSome

/-! ## Reply admission at a declared column -/

-- finite evaluation: a record answer at a declared column is data, kept as it is.
#guard externalValueIn todoDecls (.handle "Todo") [] todo == some ([], todo)
-- control: the table-free conversion refuses it.
#guard externalValue (.handle "Todo") [] todo == none
-- finite evaluation: a tree answer is admitted, and a node with a bad child is refused.
#guard externalValueIn treeDecls (.handle "Tree") [] node == some ([], node)
#guard externalValueIn treeDecls (.handle "Tree") [] badNode == none
-- finite evaluation: a natural at a declared name for `nat` is data, not an allocation request.
#guard externalValueIn idDecls (.handle "Id") [] (.nat 0) == some ([], .nat 0)
-- control: the table-free conversion mints a host handle named `Id` for it (decisions row 401 (3)).
#guard externalValue (.handle "Id") [] (.nat 0) == some (["Id"], Value.external 0)
-- finite evaluation: at a handle the table does not declare, a natural is still an allocation.
#guard externalValueIn idDecls (.handle "Conn") [] (.nat 0) == some (["Conn"], Value.external 0)
-- finite evaluation: the classifier allocates only at the undeclared name.
#guard (allocatesIn idDecls (.handle "Id"), allocatesIn idDecls (.handle "Conn")) == (false, true)

end Test.Program.DeclaredTypes
