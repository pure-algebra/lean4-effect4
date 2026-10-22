import Effect4.Author
import Effect4.Program.Authoring.Application

/-!
# A to-do list over a repository service, with an API that adds, lists, completes and removes

The data is one record, `Todo`, and three failures. The repository is a service of four host
rows. The API is four programs over the rows, and the application holds them as its entries. Two
rows declare a protocol: what an answer promises about its request.
-/

set_option autoImplicit false

namespace Examples.Todo

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (eq pair)

/-! ## The data -/

eff_record Todo where id : .nat, title : .string, done : .bool
eff_failure NotFound where id : .nat
eff_failure SqlError message
eff_failure EmptyTitle message

/-! ## The repository

The repository is the service of `todoRepoKey`, and each row is one of its methods. The host
answers the rows, so the machine never reads the service's value. -/

/-- The repository's service key. -/
def todoRepoKey : ServiceKey := ⟨⟨30⟩, ⟨6⟩⟩

eff_rows TodoRepo key todoRepoKey error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool

/-! ## The API -/

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

/-! ## The protocols

A protocol reads the request at level 0 and the answer at level 1. -/

/-- `insert(title)`: the stored to-do has the title, and it is not done. -/
def insertProtocol : RowProtocol :=
  { post := .app "and"
      (termsOfList [.app "eq" (termsOfList [.field .required (.var 1) "title", .var 0]),
        .app "not" (termsOfList [.field .required (.var 1) "done"])]) }

/-- A to-do that stands for "none" where a term needs a value of the record. -/
def noTodo : Term :=
  .record Todo.fields ["id", "title", "done"]
    (termsOfList [.lit (.nat 0), .lit (.str ""), .lit (.bool false)])

/-- `setDone(id, done)`: an answered to-do has the id and the flag of the request. -/
def setDoneProtocol : RowProtocol :=
  { post := .app "or"
      (termsOfList [.app "not" (termsOfList [.app "isSome" (termsOfList [.var 1])]),
        .app "and"
          (termsOfList
            [.app "eq" (termsOfList
              [.field .required (.app "getOrElse" (termsOfList [.var 1, noTodo])) "id",
               .app "fst" (termsOfList [.var 0])]),
             .app "eq" (termsOfList
              [.field .required (.app "getOrElse" (termsOfList [.var 1, noTodo])) "done",
               .app "snd" (termsOfList [.var 0])])])]) }

/-- The declared protocols of the repository's rows, by spelling. -/
def protocols : RowProtocols :=
  [("TodoRepo.insert", insertProtocol), ("TodoRepo.setDone", setDoneProtocol)]

/-! ## The application -/

/-- The to-do application: the repository's four rows, their protocols, and the API's four
programs, each an entry at its parameters. -/
def application : Application NativeOp :=
  { name := "todo"
    rows := TodoRepo.rows
    protocols := protocols
    entries :=
      [ { name := "add", params := [("title", .string)], body := add (var "title") }
      , { name := "list", body := list }
      , { name := "complete", params := [("id", .nat)], body := complete (var "id") }
      , { name := "remove", params := [("id", .nat)], body := remove (var "id") } ] }

end Examples.Todo
