import Test.Dogfood.Scenario
import Test.Dogfood.P2HandlerLayers

/-!
# The to-do application, first slice: its programs build and run under a scripted host

The owner named the application on 2026-10-07: a to-do list over SQL with an API that updates
it, as the one program that exercises the whole loop. This file is the first slice. It holds the
data, the repository's four rows, the API's four programs, and finite runs under a scripted host.

* **Data.** `Todo = { id, title, done }`. A missing to-do is a tagged record, `NotFound { id }`.
  An empty title and a failure of the repository are pairs of a tag and a message: a class
  whose one field is its message has that spelling (decisions row 120).
* **Rows.** The repository is four host rows: `insert`, `all`, `setDone` and `delete`. The query
  and the decoding of a row stand in the host, as in `Test/Dogfood/P2HandlerLayers.lean`.
* **Programs.** `add`, `list`, `complete` and `remove`, each written over the rows.
* **Tested: each program builds**, at the type that the guards state.
* **Tested: finite runs.** Each run is one script on the Lean machine. An empty title asks the
  repository nothing. A missing to-do fails with its id. A failure of the repository escapes.

No line is a theorem, and no claim is assembled yet. Which theorems the application carries,
and how a program carries them as data, is a design of its own: the owner asked for it with
care, on 2026-10-07. The scenario's record, its lowered runs and its place in
`Test/Dogfood/Scenario/Faces.lean` come after that design.

One finding stands in no guard yet. The module printer refuses an export name that begins with
`a` (`PrintRefusal.unsafeName`), so the program `add` prints as a module under another name
alone, and `Api.printModule` answers `none` with no reason.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (recordVal built?)

/-! ## 1. The data and the rows -/

/-- `Todo = { id: number, title: string, done: boolean }`. -/
def todoFields : List (String × Bool × Ty) :=
  [("id", false, .nat), ("title", false, .string), ("done", false, .bool)]
def todoTy : Ty := .record todoFields

/-- `NotFound { id }`: a tagged record, one class in the TypeScript face. -/
def notFoundFields : List (String × Bool × Ty) :=
  [("_tag", false, .lit "NotFound"), ("id", false, .nat)]
def notFoundTy : Ty := .record notFoundFields

/-- A failure of the repository: the pair of the tag and a message. -/
def sqlErrTy : Ty := .prod (.lit "SqlError") .string

/-- An empty title: the pair of the tag and its one message. -/
def emptyTitleTy : Ty := .prod (.lit "EmptyTitle") (.lit "a title is required")

/-- `INSERT … RETURNING *`: the stored to-do. -/
def insert : RowDef := Row.host "TodoRepo.insert" .string todoTy sqlErrTy "the to-do scenario"
/-- `SELECT *`: every to-do. -/
def all : RowDef := Row.host "TodoRepo.all" .unit (.list todoTy) sqlErrTy "the to-do scenario"
/-- `UPDATE … SET done … RETURNING *`: the updated to-do, or nothing. -/
def setDone : RowDef :=
  Row.host "TodoRepo.setDone" (.prod .nat .bool) (.option todoTy) sqlErrTy "the to-do scenario"
/-- `DELETE`: whether a row went. -/
def delete : RowDef := Row.host "TodoRepo.delete" .nat .bool sqlErrTy "the to-do scenario"

/-! ## 2. The API -/

/-- `new NotFound({ id })`. -/
def notFound (id : TermSrc) : TermSrc :=
  record notFoundFields [("_tag", str "NotFound"), ("id", id)]

/-- `add(title)`: an empty title fails and asks the repository nothing. -/
def add (title : TermSrc) : Src NativeOp :=
  ifElse (app "eq" [title, str ""])
    (fail (app "pair" [str "EmptyTitle", str "a title is required"]))
    (Row.call insert title)

/-- `list()`: every to-do. -/
def list : Src NativeOp := Row.call all unit

/-- `complete(id)`: the to-do, marked done; a missing one fails with its id. -/
def complete (id : TermSrc) : Src NativeOp :=
  bindName "updated" (Row.call setDone (app "pair" [id, bool true])) fun updated =>
    selectOption "todo" updated (fail (notFound id)) (succeed (var "todo"))

/-- `remove(id)`: a missing to-do fails with its id. -/
def remove (id : TermSrc) : Src NativeOp :=
  bindName "removed" (Row.call delete id) fun removed =>
    ifElse removed (succeed unit) (fail (notFound id))

/-- One request of the API as a module, over the repository's four rows. -/
def request (main : Src NativeOp) : Module NativeOp :=
  { rows := [insert, all, setDone, delete], main }

/-! ## 3. Each program builds -/

#guard verdict (request (add (str "milk"))) = "built"
#guard verdict (request list) = "built"
#guard verdict (request (complete (nat 1))) = "built"
#guard verdict (request (remove (nat 1))) = "built"

/-- The answer and the error of a built request. -/
def typeOf? (main : Src NativeOp) : Option (Ty × Ty) :=
  (built? (request main)).map fun b => (b.ty.answer, b.ty.error)

-- tested: `add` answers a to-do. Its error is the repository's or the empty title
#guard typeOf? (add (str "milk")) =
  some (todoTy.normalize, (Ty.union emptyTitleTy sqlErrTy).normalize)
-- tested: `list` answers the to-dos, and only the repository fails
#guard typeOf? list = some ((Ty.list todoTy).normalize, sqlErrTy)
-- tested: `complete` answers a to-do. Its error is the repository's or the missing to-do
#guard typeOf? (complete (nat 1)) =
  some (todoTy.normalize, (Ty.union notFoundTy sqlErrTy).normalize)
-- tested: `remove` answers nothing, with the same error
#guard typeOf? (remove (nat 1)) = some (.unit, (Ty.union notFoundTy sqlErrTy).normalize)

/-! ## 4. Finite runs under a scripted host -/

/-- A to-do value, its fields in canonical order. -/
def todo (id : Nat) (title : String) (done : Bool) : Val :=
  recordVal ["id", "title", "done"] [.nat id, .str title, .bool done]

/-- The failure of a missing to-do, as the machine holds it: the tagged record's payload. -/
def missing (id : Nat) : Option ExitV :=
  some (.failure (Cause.fail (errOf (recordVal ["_tag", "id"] [.str "NotFound", .nat id]))))

/-- A built request, opened under the scenario's name, and played on a script. -/
def played (main : Src NativeOp) (moves : List Move) : Option Run :=
  (built? (request main)).map fun b => Scenario.play (Run.open b "todo") moves

/-- The exit of a played request, and the requests that the host held on a row. -/
def seen (main : Src NativeOp) (moves : List Move) (row : String) : Option (Option ExitV × List Val) :=
  (played main moves).map fun s => (s.exit, requestsOn s row)

-- tested: `add` hands the title to the repository and answers the stored to-do
#guard seen (add (str "milk"))
    (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))])
    "TodoRepo.insert" =
  some (some (.success (todo 1 "milk" false)), [.str "milk"])

-- tested: an empty title fails, and the repository is asked nothing. The script offers an
-- answer that the program must not use
#guard seen (add (str ""))
    (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))])
    "TodoRepo.insert" =
  some (some (.failure (Cause.fail (.tagged "EmptyTitle" "a title is required"))), [])

-- tested: `complete` asks for the id with `true`, and answers the updated to-do
#guard seen (complete (nat 1))
    (script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true)))])
    "TodoRepo.setDone" =
  some (some (.success (todo 1 "milk" true)), [.list [.nat 1, .bool true]])

-- tested: a failure of the repository escapes `complete` unchanged
#guard (seen (complete (nat 1))
    (script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" "locked")])
    "TodoRepo.setDone").map (·.1) =
  some (some (.failure (Cause.fail (.tagged "SqlError" "locked"))))

-- tested: a missing to-do fails `complete` with its id, as a tagged record
#guard seen (complete (nat 7))
    (script [[.start], answer (.row "TodoRepo.setDone") (ok .none)])
    "TodoRepo.setDone" =
  some (missing 7, [.list [.nat 7, .bool true]])

-- tested: `remove` answers nothing where a row went, and fails with the id where none did
#guard seen (remove (nat 7))
    (script [[.start], answer (.row "TodoRepo.delete") (ok (.bool true))])
    "TodoRepo.delete" =
  some (some (.success .unit), [.nat 7])
#guard seen (remove (nat 7))
    (script [[.start], answer (.row "TodoRepo.delete") (ok (.bool false))])
    "TodoRepo.delete" =
  some (missing 7, [.nat 7])

-- tested: `list` answers what the repository holds
#guard seen list
    (script [[.start], answer (.row "TodoRepo.all") (ok (.list [todo 1 "milk" true, todo 2 "tea" false]))])
    "TodoRepo.all" =
  some (some (.success (.list [todo 1 "milk" true, todo 2 "tea" false])), [.unit])

/-! ## 5. The faces -/

-- tested: each program prints as Effect TypeScript against its own row table, and the printed
-- text is in the readable domain
#guard [add (str "milk"), list, complete (nat 1), remove (nat 1)].all fun main =>
  (built? (request main)).map printedOf == some (true, true)

end Test.Dogfood.Scenario.Todo
