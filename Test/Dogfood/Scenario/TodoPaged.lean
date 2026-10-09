import Effect4
import Effect4.Library.Words
import Effect4.Library.Stream.Ops
import Effect4.Program.Stream
import Test.Dogfood.Stage
import Test.Dogfood.Scenario
import Test.Dogfood.Scenario.Todo
import Test.Dogfood.P2HandlerLayers

/-!
# The to-do application, second slice: `list` as a paged stream

Decisions row 309. The repository gains a cursor over its to-dos: three host rows.
`listPaged` is `runCollect` of the stream, and `completeAll` is `runForEach` with
`setDone` in its body. Both build, answer under a scripted host, and print/read back.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.TodoPaged

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules (nilT)
open Effect4.Program.Stream (pulledTy chunkVal endVal)
open Effect4.Stream (Source Source.host runCollect runForEach drain runWith)
open Test.Dogfood.Scenario.Todo (Todo.ty SqlError.ty todo)
open Test.Dogfood.Scenario.Todo.TodoRepo.row (insert all setDone delete)
open Test.Dogfood.P2HandlerLayers (recordVal built?)
open Test.Dogfood (verdict printedOf)
open Test.Dogfood.Scenario (script answer ok failed Move Sel requestsOn refusals live)

/-- The repository's cursor over its to-dos: an external handle. -/
def cursorTarget : String := "TodoRepo.Cursor"

/-- `SELECT … ` as a stream: the cursor's handle. -/
def openList : RowDef :=
  Row.host "TodoRepo.openList" .unit (.handle cursorTarget) SqlError.ty "the to-do scenario"
/-- The next page of the cursor, or its end. -/
def nextPage : RowDef :=
  Row.host "TodoRepo.nextPage" (.handle cursorTarget) (pulledTy Todo.ty .unit) SqlError.ty
    "the to-do scenario"
/-- The cursor's release. -/
def closeList : RowDef :=
  Row.host "TodoRepo.closeList" (.handle cursorTarget) .unit .never "the to-do scenario"

/-- The repository's to-dos as a stream. -/
def todos : Source := Source.host Todo.ty .unit openList nextPage closeList unit

/-- `list()`, paged: every to-do, in the repository's order. -/
def listPaged : Src NativeOp := runCollect todos

/-- `completeAll()`: each to-do of the stream marked done, in order. -/
def completeAll : Src NativeOp :=
  runForEach todos fun t => Row.call setDone (app "pair" [field t "id", bool true])

/-- One request of the API as a module, over the repository's seven rows. -/
def request (main : Src NativeOp) : Module NativeOp :=
  { rows := [insert, all, setDone, delete, openList, nextPage, closeList], main }

#guard verdict (request listPaged) = "built"
#guard verdict (request completeAll) = "built"

def typeOf? (main : Src NativeOp) : Option (Ty × Ty) :=
  (built? (request main)).map fun b => (b.ty.answer, b.ty.error)

-- tested: the paged `list` answers the to-dos, and only the repository fails: the end of the
-- stream is no member of the error column
#guard typeOf? listPaged = some ((Ty.list Todo.ty).normalize, SqlError.ty)
#guard typeOf? completeAll = some (.unit, SqlError.ty)

/-! ## 4. Finite runs under a scripted host -/

def opens : Sel := .row "TodoRepo.openList"
def pulls : Sel := .row "TodoRepo.nextPage"
def closes : Sel := .row "TodoRepo.closeList"

/-- The host opens the cursor: the next allocation index. -/
def opening : List Move := answer opens (ok (.nat 0))
def page (items : List Val) : List Move := answer pulls (ok (chunkVal items))
def ending : List Move := answer pulls (ok (endVal .unit))
def closing : List Move := answer closes (ok .unit)

def played (main : Src NativeOp) (moves : List Move) : Option Run :=
  (built? (request main)).map fun b => Test.Dogfood.Scenario.play (Run.open b "todo-paged") moves

/-- The observation of the second slice. -/
structure Observation where
  /-- The root's exit. -/
  outcome : Option ExitV
  /-- How many times the host held each of the cursor's three rows. -/
  opened : Nat
  pulled : Nat
  closed : Nat
  /-- The requests that the host held on `TodoRepo.setDone`, in order. -/
  completed : List Val
  /-- The rows of the calls that the machine waits on. -/
  waiting : List String
  /-- The refused rows. -/
  refusals : List (String × Api.HostSession.Refusal)
deriving DecidableEq

def observe (s : Run) : Observation :=
  { outcome := s.exit
    opened := (requestsOn s "TodoRepo.openList").length
    pulled := (requestsOn s "TodoRepo.nextPage").length
    closed := (requestsOn s "TodoRepo.closeList").length
    completed := requestsOn s "TodoRepo.setDone"
    waiting := (live s).map (·.row)
    refusals := refusals s }

def shows (main : Src NativeOp) (moves : List Move) (expected : Observation) : Bool :=
  (played main moves).map observe == some expected

def t1 : Val := todo 1 "milk" false
def t2 : Val := todo 2 "tea" false
def t3 : Val := todo 3 "rye" true

/-- Two pages, the end, and the close. -/
def twoPages : List Move :=
  script [[.start], opening, page [t1, t2], page [t3], ending, closing]

-- green: every element is delivered once, in order; the stream is closed once; the end is a
-- success
#guard shows listPaged twoPages
  ⟨some (.success (.list [t1, t2, t3])), 1, 3, 1, [], [], []⟩
-- green: an empty stream is the empty list, and it is closed once
#guard shows listPaged (script [[.start], opening, ending, closing])
  ⟨some (.success (.list [])), 1, 1, 1, [], [], []⟩
-- green: a failure of a pull is a failure of the root, and the stream is still closed once
#guard shows listPaged
    (script [[.start], opening, page [t1], answer pulls (failed "SqlError" "locked"), closing])
  ⟨some (.failure (Cause.fail (.tagged "SqlError" "locked"))), 1, 2, 1, [], [], []⟩
-- green: a failure of the open is a failure of the root, and nothing is closed
#guard shows listPaged (script [[.start], answer opens (failed "SqlError" "down")])
  ⟨some (.failure (Cause.fail (.tagged "SqlError" "down"))), 1, 0, 0, [], [], []⟩
-- control: before the host answers the close, the root has no exit, and the machine waits on
-- the close alone: the close is part of the run
#guard shows listPaged (script [[.start], opening, page [t1, t2], page [t3], ending])
  ⟨none, 1, 3, 0, [], ["TodoRepo.closeList"], []⟩
-- control: after the end the program pulls no more: an offered page is not taken
#guard shows listPaged (script [[.start], opening, ending, page [t1], closing])
  ⟨some (.success (.list [])), 1, 1, 1, [], [], [("submit", .noCall), ("apply", .noCall)]⟩
-- control: the session refuses an answer that is no chunk and no end
#guard shows listPaged (script [[.start], opening, answer pulls (ok (.list [.str "Done", .unit]))])
  ⟨none, 1, 1, 0, [], ["TodoRepo.nextPage"], [("submit", .envelope), ("apply", .noCall)]⟩

/-- `completeAll` on two pages: each to-do is completed once, in order, before the next pull. -/
def completing : List Move :=
  script [[.start], opening, page [t1, t2],
    answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true))),
    answer (.row "TodoRepo.setDone") (ok (.some (todo 2 "tea" true))),
    page [t3],
    answer (.row "TodoRepo.setDone") (ok (.some (todo 3 "rye" true))),
    ending, closing]

#guard shows completeAll completing
  ⟨some (.success .unit), 1, 3, 1,
    [.list [.nat 1, .bool true], .list [.nat 2, .bool true], .list [.nat 3, .bool true]], [], []⟩
-- control: a failure of the body's row stops the stream, and the stream is closed once
#guard shows completeAll
    (script [[.start], opening, page [t1, t2],
      answer (.row "TodoRepo.setDone") (failed "SqlError" "locked"), closing])
  ⟨some (.failure (Cause.fail (.tagged "SqlError" "locked"))), 1, 1, 1,
    [.list [.nat 1, .bool true]], [], []⟩

/-! ### Red controls: each fault fails its own property -/

/-- A consumer that opens with no scope: nothing registers the close. -/
def leaky (src : Source) : Src NativeOp :=
  bindWith src.opened fun h =>
    bindWith (drain src (.list src.elem) nilT h fun acc chunk => succeed (app "append" [acc, chunk]))
      fun last => succeed (app "fst" [last])

-- red (closed once): the leaky consumer answers the same list and never closes
#guard shows (leaky todos) (script [[.start], opening, page [t1, t2], page [t3], ending])
  ⟨some (.success (.list [t1, t2, t3])), 1, 3, 0, [], [], []⟩

/-- A consumer whose step keeps the last chunk alone. -/
def forgetful (src : Source) : Src NativeOp :=
  bindWith (runWith src (.list src.elem) nilT fun _ chunk => succeed chunk)
    fun last => succeed (app "fst" [last])

-- red (delivered once): the forgetful consumer loses the first page
#guard shows (forgetful todos) twoPages
  ⟨some (.success (.list [t3])), 1, 3, 1, [], [], []⟩

/-! ## 5. The faces -/

#guard [listPaged, completeAll].map (fun main => (built? (request main)).map printedOf) =
  [some (true, true), some (true, true)]

end Test.Dogfood.Scenario.TodoPaged
