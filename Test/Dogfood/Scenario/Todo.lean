import Test.Dogfood.Scenario
import Test.Dogfood.P2HandlerLayers
import Effect4.Program.Authoring.Declare
import Effect4.Program.Authoring.Atoms
import Effect4.Program.Authoring.Sugar

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

One finding stands in no guard yet. The module printer refuses `add` as an export name
because a module imports the atom `add`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (eq pair)
open Test.Dogfood.P2HandlerLayers (recordVal built?)

/-! ## 1. The data and the rows -/

eff_record Todo where id : .nat, title : .string, done : .bool
eff_failure NotFound where id : .nat
eff_failure SqlError message
eff_failure EmptyTitle message

/-- The error that `add` raises, as the checker types it: the message is a literal type. -/
def emptyTitleTy : Ty := .prod (.lit "EmptyTitle") (.lit "a title is required")

eff_rows TodoRepo error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool

/-! ## 2. The API -/

/-- `add(title)`: an empty title fails and asks the repository nothing. -/
def add (title : TermSrc) : Src NativeOp := eff do
  if eq title (str "") then
    EmptyTitle.raise (str "a title is required")
  else
    TodoRepo.insert title

/-- `list()`: every to-do. -/
def list : Src NativeOp := TodoRepo.all unit

/-- `complete(id)`: the to-do, marked done; a missing one fails with its id. -/
def complete (id : TermSrc) : Src NativeOp := eff do
  let updated ← TodoRepo.setDone (pair id (bool true))
  selectOptionWith updated (NotFound.raise id) fun todo => succeed todo

/-- `remove(id)`: a missing to-do fails with its id. -/
def remove (id : TermSrc) : Src NativeOp := eff do
  let removed ← TodoRepo.delete id
  if removed then succeed unit else NotFound.raise id

/-- One request of the API as a module, over the repository's four rows. -/
def request (main : Src NativeOp) : Module NativeOp :=
  { rows := TodoRepo.rows, main }

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
  some (Todo.ty.normalize, (Ty.union emptyTitleTy SqlError.ty).normalize)
-- tested: `list` answers the to-dos, and only the repository fails
#guard typeOf? list = some ((Ty.list Todo.ty).normalize, SqlError.ty)
-- tested: `complete` answers a to-do. Its error is the repository's or the missing to-do
#guard typeOf? (complete (nat 1)) =
  some (Todo.ty.normalize, (Ty.union NotFound.ty SqlError.ty).normalize)
-- tested: `remove` answers nothing, with the same error
#guard typeOf? (remove (nat 1)) = some (.unit, (Ty.union NotFound.ty SqlError.ty).normalize)

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
