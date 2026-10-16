import Effect4.Program.TyHead
import Effect4.Program.AdmitIn
import Effect4.Program.SigApp
import Effect4.Program.Typing.TermRefusal
import Effect4.Program.Authoring
import Effect4.Program.Decision
import Effect4.Program.Authoring.Declare
import Effect4.Api.AuthorIn

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
    (.record [("_tag", false, .lit "node"), ("children", false, .list (.app "Tree" [])),
      ("label", false, .string)]))]

/-- A declared name for a natural: `Id = number`. -/
def idDecls : TyDecls := [("Id", .nat)]

/-- An unguarded table: `A = A | number`. -/
def loopDecls : TyDecls := [("A", .union (.app "A" []) .nat)]

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
#guard Record.fieldTypeIn todoDecls false (.app "Todo" []) "title" == some .string
-- control: the table-free read refuses it, since a declared name is opaque there.
#guard Record.fieldType false (.app "Todo" []) "title" == none
-- finite evaluation: a field that one member lacks is refused at the union, as the lifted rule
-- refuses it: the leaf has no children.
#guard Record.fieldTypeIn treeDecls false (.app "Tree" []) "children" == none
-- finite evaluation: the tag dispatch on a recursive type, and the node arm's children, which
-- keep the declared name inside.
#guard ((Record.tagArmsIn treeDecls "node" (.app "Tree" [])).bind fun arms =>
  Record.fieldTypeIn treeDecls false arms.1 "children") == some (.list (.app "Tree" []))
-- control: the table-free dispatch refuses the declared name.
#guard Record.tagArms "node" (.app "Tree" []) == none
-- finite evaluation: an unguarded name adds no member when its unfolding returns to it.
#guard Ty.membersIn loopDecls (.app "A" []) == [.nat]

/-! ## The fold of a written field -/

-- finite evaluation: a field written at `Todo` takes a member of the body.
#guard (Record.checkIn todoDecls [("v", false, .app "Todo" [])] ["v"] [todoBody]).isSome
-- control: the order alone refuses it: the name is nominal.
#guard (Record.check [("v", false, .app "Todo" [])] ["v"] [todoBody]).isNone
-- control: a record that lacks a field is not folded.
#guard (Record.checkIn todoDecls [("v", false, .app "Todo" [])] ["v"]
  [.record [("id", false, .nat)]]).isNone
-- finite evaluation: a node folds into `Tree` when its children are already trees.
#guard (Record.checkIn treeDecls [("v", false, .app "Tree" [])] ["v"]
  [.record [("_tag", false, .lit "node"), ("children", false, .list (.app "Tree" [])),
    ("label", false, .string)]]).isSome

/-! ## The term typer under the application's table (`SigApp.signatureIn`) -/

/-- An application that declares `Todo` and `Tree`. -/
def app : SigApp := { types := todoDecls ++ treeDecls }

/-- A record whose one field is written at `Todo`, holding the term `value`. -/
def asTodo (value : Term) : Term :=
  .record [("v", false, .app "Todo" [])] ["v"] (Authoring.termsOfList [value])

-- finite evaluation: the typer reads a field through a declared name.
#guard termTy app.signatureIn [.app "Todo" []] (.field .required (.var 0) "title") == some .string
-- control: the table-free signature refuses the same read.
#guard termTy app.signature [.app "Todo" []] (.field .required (.var 0) "title") == none
-- finite evaluation: a field written at `Todo` folds a value of its body, and reading it back
-- gives the name.
#guard termTy app.signatureIn [todoBody] (.field .required (asTodo (.var 0)) "v") ==
  some (.app "Todo" [])
-- control: the table-free signature refuses the fold: the name is nominal there.
#guard termTy app.signature [todoBody] (.field .required (asTodo (.var 0)) "v") == none
-- finite evaluation: the refusal of a field that `Todo` lacks is located at the record.
#guard (TermRefusal.diagnose app.signatureIn [.app "Todo" []]
  (.field .required (.var 0) "owner")).isSome

/-! ## The select rule's arms under the table (`Decision.armsIn`) -/

-- finite evaluation: a record-tag decision on a recursive type binds the node arm, whose
-- children keep the declared name.
#guard ((Decision.armsIn treeDecls (.recordTag "node") (.app "Tree" [])).bind fun arms =>
  arms.1.head?.bind fun node => Record.fieldTypeIn treeDecls false node "children") ==
  some (.list (.app "Tree" []))
-- control: the table-free decision refuses the declared name.
#guard Decision.arms (.recordTag "node") (.app "Tree" []) == none
-- finite evaluation: an option decision reads a declared name for an option.
#guard Decision.armsIn [("Maybe", .option .nat)] .option (.app "Maybe" []) == some ([], [.nat])
-- control: the table-free decision refuses it.
#guard Decision.arms .option (.app "Maybe" []) == none

/-! ## Reply admission at a declared column -/

-- finite evaluation: a record answer at a declared column is data, kept as it is.
#guard externalValueIn todoDecls (.app "Todo" []) [] todo == some ([], todo)
-- control: the table-free conversion refuses it.
#guard externalValue (.app "Todo" []) [] todo == none
-- finite evaluation: a tree answer is admitted, and a node with a bad child is refused.
#guard externalValueIn treeDecls (.app "Tree" []) [] node == some ([], node)
#guard externalValueIn treeDecls (.app "Tree" []) [] badNode == none
-- finite evaluation: a natural at a declared name for `nat` is data, not an allocation request.
#guard externalValueIn idDecls (.app "Id" []) [] (.nat 0) == some ([], .nat 0)
-- finite evaluation: the machine's own conversion mints no handle at a declared column, with no
-- table: a declared name is `app n []`, never `handle n` (decisions row 406 (1)).
#guard externalValue (.app "Id" []) [] (.nat 0) == none
-- finite evaluation: at a host handle, a natural is still an allocation, under any table.
#guard externalValueIn idDecls (.handle "Conn") [] (.nat 0) == some (["Conn"], Value.external 0)
-- finite evaluation: the machine's allocation test reads the spelling alone.
#guard (allocates (.app "Id" []), allocates (.handle "Conn")) == (false, true)

/-! ## A module built under its named types (`Api.Author.buildIn`) -/

open Effect4.Program.Authoring

eff_rows Repo error .never cite "the declared-types battery" where
  get(.nat) : .app "Todo" []

/-- A program that reads a declared record's field from a host row's answer. -/
def readTitle : Src NativeOp :=
  bindWith (Repo.get (nat 1)) fun todo => succeed (field todo "title")

/-- The module: the row, the table that declares `Todo`, and the program. -/
def titleModule : Module NativeOp := { rows := Repo.rows, types := todoDecls, main := readTitle }

-- finite evaluation: the module builds under its named types, at the field's type.
#guard (match Api.Author.buildIn titleModule with
  | .ok b => b.ty.answer == .string
  | .error _ => false)
-- control: the table-free build refuses it, since the field read meets an opaque name there.
#guard (match Api.Author.build titleModule with
  | .ok _ => false
  | .error _ => true)

/-- A program that reads a field the declared record lacks. -/
def readOwner : Src NativeOp :=
  bindWith (Repo.get (nat 1)) fun todo => succeed (field todo "owner")

-- finite evaluation: the build under the named types refuses a field that `Todo` lacks, as a
-- typing refusal with its location.
#guard (match Api.Author.buildIn { titleModule with main := readOwner } with
  | .error (.typing _) => true
  | _ => false)

/-- A module with no named type. -/
def plainModule : Module NativeOp := { main := succeed (nat 1) }

-- finite evaluation: a module with no named type builds under `buildIn` at `build`'s type.
#guard (match Api.Author.buildIn plainModule, Api.Author.build plainModule with
  | .ok b, .ok c => decide (b.ty = c.ty)
  | _, _ => false)

end Test.Program.DeclaredTypes
