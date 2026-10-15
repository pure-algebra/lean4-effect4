import Test.Dogfood.Scenario.Data
import Test.Dogfood.P2HandlerLayers.Data
import Effect4.Program.Authoring.Application
import Effect4.Library.Ref.Cache

/-! Data shared by the scenario battery and fixture writers. -/

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

/-- The repository's service key (decisions row 378 (19), slice E3): the namespace `TodoRepo`
is the service of this key, and each of its rows is a method of it, so each row's requirement
column names the key. The name `30` is free (`Env.firstFreeName` is `4`). The code `6` is the
built-in code whose carrier is `unit` (`nativeServiceTypes`), so admission finds a carrier for
the key (`SigApp.serviceTy`): the machine never reads the service's value, because the host
answers the rows. -/
def todoRepoKey : ServiceKey := ⟨⟨30⟩, ⟨6⟩⟩

eff_rows TodoRepo key todoRepoKey error SqlError.ty cite "the to-do scenario" where
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

/-! ### The application

The four programs as one application (`Application`,
`src/Effect4/Program/Authoring/Application.lean`; the claims packet's slice APP). Each entry's
body is the program above, at its parameter read by `var`. A request of the API is an entry at
its arguments, built through the application's module. -/

/-- `insert(title)`: the stored to-do has the title, and it is not done. The promise reads the
request at level 0 and the answer at level 1 (`RowProtocol`,
`src/Effect4/Program/RowProtocol.lean`). -/
def insertProtocol : RowProtocol :=
  { post := .app "and"
      (termsOfList [.app "eq" (termsOfList [.field .required (.var 1) "title", .var 0]),
        .app "not" (termsOfList [.field .required (.var 1) "done"])]) }

/-- A to-do that stands for "none" where a term needs a value of the record. -/
def noTodo : Term :=
  .record Todo.fields ["id", "title", "done"]
    (termsOfList [.lit (.nat 0), .lit (.str ""), .lit (.bool false)])

/-- Two Booleans are the same. The atom `eq` has no type at two Booleans (a control in section
6), so the term is written with `and`, `or` and `not`. -/
def sameFlag (a b : Term) : Term :=
  .app "or" (termsOfList [.app "and" (termsOfList [a, b]),
    .app "and" (termsOfList [.app "not" (termsOfList [a]), .app "not" (termsOfList [b])])])

/-- `setDone(id, done)`: an answered to-do has the id and the flag of the request. -/
def setDoneProtocol : RowProtocol :=
  { post := .app "or"
      (termsOfList [.app "not" (termsOfList [.app "isSome" (termsOfList [.var 1])]),
        .app "and"
          (termsOfList
            [.app "eq" (termsOfList
              [.field .required (.app "getOrElse" (termsOfList [.var 1, noTodo])) "id",
               .app "fst" (termsOfList [.var 0])]),
             sameFlag (.field .required (.app "getOrElse" (termsOfList [.var 1, noTodo])) "done")
               (.app "snd" (termsOfList [.var 0]))])]) }

/-- The declared protocols of the repository's rows, by spelling. -/
def protocols : RowProtocols :=
  [("TodoRepo.insert", insertProtocol), ("TodoRepo.setDone", setDoneProtocol)]

/-- The to-do application: the repository's four rows, their protocols, and the API's four
programs. -/
def application : Application NativeOp :=
  { name := "todo"
    rows := TodoRepo.rows
    protocols := protocols
    entries :=
      [ { name := "add", params := [("title", .string)], body := add (var "title") }
      , { name := "list", body := list }
      , { name := "complete", params := [("id", .nat)], body := complete (var "id") }
      , { name := "remove", params := [("id", .nat)], body := remove (var "id") } ] }

/-- One entry at its arguments, built through the application's module. -/
def builtAt (name : String) (args : List TermSrc) : Option Api.Built :=
  (application.entry? name).bind fun e => built? (application.moduleOf e args)

/-! ## 4. Finite runs under a scripted host -/

/-- A to-do value, its fields in canonical order. -/
def todo (id : Nat) (title : String) (done : Bool) : Val :=
  recordVal ["id", "title", "done"] [.nat id, .str title, .bool done]

/-! ## 7. The reference model of the repository

The claims packet's reference model (§3.6): a host as a function, written in Lean, that states
what the four rows do. It moved here from `Test/Api/SessionMeaning.lean`, which reads it, so the
application has one model. -/

/-- The repository's state: the next id and the to-dos. -/
abbrev Repo := Nat × List (Nat × String × Bool)

/-- A stored to-do as a value. -/
def todoOf (entry : Nat × String × Bool) : Val := todo entry.1 entry.2.1 entry.2.2

/-- An in-memory repository as a host function, row by row: the reference model. -/
def repository : Run.Reactor Repo := fun row sent state =>
  if row.spelling == "TodoRepo.insert" then
    match sent with
    | .str title =>
      some (ok (todo state.1 title false), (state.1 + 1, state.2 ++ [(state.1, title, false)]))
    | _ => none
  else if row.spelling == "TodoRepo.all" then
    some (ok (.list (state.2.map todoOf)), state)
  else if row.spelling == "TodoRepo.setDone" then
    match sent with
    | .list [.nat id, .bool done] =>
      match state.2.find? (·.1 == id) with
      | some entry =>
        some (ok (.some (todo id entry.2.1 done)),
          (state.1, state.2.map fun e => if e.1 == id then (e.1, e.2.1, done) else e))
      | none => some (ok .none, state)
    | _ => none
  else if row.spelling == "TodoRepo.delete" then
    match sent with
    | .nat id => some (ok (.bool (state.2.any (·.1 == id))), (state.1, state.2.filter (·.1 != id)))
    | _ => none
  else none

end Test.Dogfood.Scenario.Todo
