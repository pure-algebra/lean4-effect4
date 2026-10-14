import Test.Dogfood.Scenario
import Test.Dogfood.P2HandlerLayers
import Effect4.Author
import Effect4.Program.Authoring.Application
import Effect4.Codegen.RowServices
import Effect4.Library.Ref.Cache

/-!
# The to-do application: its programs build and run under a scripted host

The owner named the application on 2026-10-07: a to-do list over SQL with an API that updates
it, as the one program that exercises the whole loop. This file holds the data, the repository's
four rows, the API's four programs, the application that holds them, and finite runs under a
scripted host.

* **Data.** `Todo = { id, title, done }`. A missing to-do is a tagged record, `NotFound { id }`.
  An empty title and a failure of the repository are pairs of a tag and a message: a class
  whose one field is its message has that spelling (decisions row 120).
* **Rows.** The repository is four host rows: `insert`, `all`, `setDone` and `delete`. The query
  and the decoding of a row stand in the host, as in `Test/Dogfood/P2HandlerLayers.lean`. Each
  row requires the repository's key, so the namespace is an Effect service (section 8).
* **Programs.** `add`, `list`, `complete` and `remove`, each written over the rows.
* **The application.** `application` holds the four programs as entries with typed parameters
  (`src/Effect4/Program/Authoring/Application.lean`, decisions row 336 (9)).
* **Tested: each program builds**, at the type that the guards state.
* **Tested: finite runs.** Each run is one script on the Lean machine. An empty title asks the
  repository nothing. A missing to-do fails with its id. A failure of the repository escapes.

No line here is a theorem. The application's call trees stand in
`Test/Dogfood/Scenario/Todo/Tree.lean`, and its claims and their record in
`Test/Dogfood/Scenario/Todo/Claims.lean`, the shape of the claims packet
(`docs/research/2026-10-07-packet-application-claims.md`).

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

/-- One request of the API as a module, over the repository's four rows. -/
def request (main : Src NativeOp) : Module NativeOp :=
  { rows := TodoRepo.rows, main }

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

/-- `list`'s method reads through the banked cache: `get` at the cache's cell, with the entry's
program, `TodoRepo.all()`, as its loader (decisions row 378 (8)). -/
def readingThrough (body : Src NativeOp) : Src NativeOp :=
  Def.invokeWith "listCacheGet" [var "cache"] [fun _ => body]

/-- A write's method empties the cache after the entry's program succeeds: an application that
holds the cache invalidates it after each write (decisions row 378 (23)). A failure skips it. -/
def invalidatingAfter (body : Src NativeOp) : Src NativeOp :=
  bindWith body fun answer =>
    andThen (Def.invoke "listCacheInvalidate" [var "cache"]) (succeed answer)

/-- **The banked Ref cache, imposed on the to-do's service** (decisions row 378 (8)): the bank's
block at the to-do's types (`Ref.Cache.block`; `Test/Dogfood/Bank.lean` records its digest). Its
cell is the service's state `cache`, made once by `listCacheMake`. `list` reads through it, and
`add`, `complete` and `remove` invalidate it after a successful write. The entries do not change. -/
def listCache : Application.Imposed NativeOp where
  block := Effect4.Ref.Cache.block Todo.ty SqlError.ty
  state := "cache"
  stateTy := Effect4.Ref.Cache.cellTy Todo.ty
  make := "listCacheMake"
  around := [("list", readingThrough), ("add", invalidatingAfter),
    ("complete", invalidatingAfter), ("remove", invalidatingAfter)]

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

/-- The answer and the error of an entry's open program, at its parameters' types. -/
def openTy (name : String) : Option (Ty × Ty) :=
  (application.entry? name).bind fun e =>
    (application.openProgram e).toOption.bind fun program =>
      (effTy (nativeSignature application.table) (e.params.map (·.2)) program).map fun t =>
        (t.answer, t.error)

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
-- reader: the checker's requirement row carries the repository's key at each request, since a
-- row call requires its row's requirement column (`checkRow`, `Program/Typing/Rules.lean`)
#guard [add (str "milk"), list, complete (nat 1), remove (nat 1)].all fun main =>
  (built? (request main)).map (·.requires) == some [todoRepoKey]

-- finite evaluation: each entry builds at an argument through the application, at the type of
-- the request above
#guard [("add", [str "milk"], add (str "milk")), ("list", [], list),
    ("complete", [nat 1], complete (nat 1)), ("remove", [nat 1], remove (nat 1))].all fun entry =>
  (builtAt entry.1 entry.2.1).map (fun b => (b.ty.answer, b.ty.error)) = typeOf? entry.2.2 &&
    (builtAt entry.1 entry.2.1).isSome
-- finite evaluation: each entry's open program has that type at its parameters' types
#guard openTy "add" = some (Todo.ty.normalize, (Ty.union emptyTitleTy SqlError.ty).normalize)
#guard openTy "list" = some ((Ty.list Todo.ty).normalize, SqlError.ty)
#guard openTy "complete" = some (Todo.ty.normalize, (Ty.union NotFound.ty SqlError.ty).normalize)
#guard openTy "remove" = some (.unit, (Ty.union NotFound.ty SqlError.ty).normalize)
-- control: with no argument the parameter is unbound, and the build refuses the entry; the open
-- program of a body that reads a name its entry does not declare is refused at that read
#guard (builtAt "complete" []).isNone
#guard ((application.entry? "complete").map fun e =>
    (application.openProgram { e with params := [] }).toOption.isNone) = some true

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

/-! ## 6. The protocols of the rows

The application declares a protocol of two rows (`protocols`, the claims packet's slice
PROTOCOL). Each line is a finite evaluation or a control (decisions row 301). -/

-- control: the atom `eq` has no type at two Booleans, and it has one at two strings
#guard termTy (nativeSignature application.table) [.bool, .bool]
    (.app "eq" (termsOfList [.var 0, .var 1])) = none
#guard termTy (nativeSignature application.table) [.string, .string]
    (.app "eq" (termsOfList [.var 0, .var 1])) = some .bool
-- finite evaluation: the application's protocols are formed: each names a row, and its terms are
-- typed there
#guard application.protocolsFormed
-- control: a protocol of a row that the application does not hold, and a promise that is no
-- Boolean
#guard !({ application with protocols := [("TodoRepo.find", {})] } :
  Application NativeOp).protocolsFormed
#guard !({ application with protocols := [("TodoRepo.insert", { post := .var 0 })] } :
  Application NativeOp).protocolsFormed
-- finite evaluation: answers that keep the promises; control: three that break them (another id,
-- a to-do that is not done, another title)
#guard insertProtocol.keeps (.str "milk") (todo 1 "milk" false) &&
  setDoneProtocol.keeps (.list [.nat 1, .bool true]) (.some (todo 1 "milk" true)) &&
  setDoneProtocol.keeps (.list [.nat 1, .bool true]) .none
#guard !setDoneProtocol.keeps (.list [.nat 1, .bool true]) (.some (todo 2 "milk" true)) &&
  !setDoneProtocol.keeps (.list [.nat 1, .bool true]) (.some (todo 1 "milk" false)) &&
  !insertProtocol.keeps (.str "milk") (todo 1 "tea" false)

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

/-! ## 8. The repository as an Effect service (decisions row 378 (19), slice E3)

The repository's rows require its key, so the namespace `TodoRepo` is one service and each row
is a method of it (`rowServices`, `src/Effect4/Codegen/RowServices.lean`). A module declares the
key and the namespace, the key with one accessor for each method (`rowServiceDecls`). Each line
is a finite evaluation or a control (decisions row 301). -/

-- finite evaluation: one service, `TodoRepo` of the key, with its four methods in written order
#guard (rowServices application.table).map (fun s => (s.ns, s.key, s.methods.map (·.1))) ==
  [("TodoRepo", todoRepoKey, ["insert", "all", "setDone", "delete"])]
-- finite evaluation: the module declares the key and the namespace with its accessors
#guard (rowServiceDecls (nativeSignature application.table) application.table).toOption.map
    (·.map fun decl => (decl.name, decl.exported)) ==
  some [("TodoRepoKey", true), ("TodoRepo", true)]
-- control: a method named as a member of the key (`use`) would shadow it, and is refused by its
-- row's spelling
#guard rowServiceDecls (nativeSignature application.table) (application.table ++
    [{ (Row.host "TodoRepo.use" .unit .unit).row with requires := [todoRepoKey] }]) matches
  .error (.unsafeName "TodoRepo.use")
-- control: a row of the namespace that requires no key, and a row that requires the key with no
-- namespace in its spelling, are refused by their spellings
#guard rowServiceDecls (nativeSignature application.table)
    (application.table ++ [(Row.host "TodoRepo.find" .nat .bool).row]) matches
  .error (.unsafeName "TodoRepo.find")
#guard rowServiceDecls (nativeSignature application.table)
    (application.table ++ [{ (Row.host "find" .nat .bool).row with requires := [todoRepoKey] }])
  matches .error (.unsafeName "find")

end Test.Dogfood.Scenario.Todo
