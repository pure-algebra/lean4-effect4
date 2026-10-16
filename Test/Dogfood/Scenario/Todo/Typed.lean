import Test.Dogfood.Scenario.Todo.Data
import Effect4.Run.Method
import Effect4.Schema.Modeled.Derive

/-!
# The to-do repository as a typed host (the interop plan's P1)

The repository's four rows answered by a record of Lean functions over a derived `Todo`
(`Effect4.Run.Reactor.method`): each request read by its type's exact embedding, each answer
written by the answer's. `model` is the reference model (`repository`, `Data.lean`) written over
`Todo`, and the battery holds it to `repository`'s answers. Each method may fail with the
rows' error (`Run.Reactor.fallible`); `broken` fails `insert`, and the battery holds it to an
untyped host that writes the same failure. Lowered by the LCNF route, `Host` is a
record of OCaml functions over the lowered `todo`, so a provider written in OCaml is a value of
it (`ocaml/engine/test/todo/`, `test_todo.ml`'s T10 and T11).

This module reaches no law module: the lowered host run imports it.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Todo.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Schema
open Test.Dogfood.Scenario.Todo (Repo repository)

/-- A to-do, as the repository's rows carry it: the record `Todo.ty` of `Data.lean`. -/
structure Todo where
  id : Nat
  title : String
  done : Bool
  deriving Modeled, DecidableEq, Repr

/-- The tag of the repository's failure: a one-constructor enum, whose code is `lit "SqlError"`. -/
inductive SqlTag where
  | SqlError
  deriving Modeled, DecidableEq, Repr

/-- The repository's failure, the rows' error column `SqlError.ty` (`eff_failure SqlError
message`): its tag and its message. -/
abbrev SqlError := SqlTag × String

/-- **The repository's interface**: one function per row of `TodoRepo`, over typed requests and
answers, threading the host's state. Each may fail with the rows' error, `SqlError`. -/
structure Host (σ : Type) where
  insert : String → σ → Except SqlError Todo × σ
  all : Unit → σ → Except SqlError (List Todo) × σ
  setDone : Nat × Bool → σ → Except SqlError (Option Todo) × σ
  delete : Nat → σ → Except SqlError Bool × σ

/-- The host as a reactor: each row answered by its method. -/
def Host.reactor {σ : Type} (h : Host σ) : Run.Reactor σ :=
  Run.Reactor.first [
    .fallible "TodoRepo.insert" h.insert, .fallible "TodoRepo.all" h.all,
    .fallible "TodoRepo.setDone" h.setDone, .fallible "TodoRepo.delete" h.delete]

/-- A stored to-do as a `Todo`. -/
def todoOf (entry : Nat × String × Bool) : Todo := ⟨entry.1, entry.2.1, entry.2.2⟩

/-- **The reference model, typed**: what `repository` states, over `Todo`. -/
def model : Host Repo where
  insert title state :=
    (.ok ⟨state.1, title, false⟩, (state.1 + 1, state.2 ++ [(state.1, title, false)]))
  all _ state := (.ok (state.2.map todoOf), state)
  setDone request state :=
    match state.2.find? (·.1 == request.1) with
    | some entry =>
      (.ok (some ⟨request.1, entry.2.1, request.2⟩),
        (state.1, state.2.map fun e => if e.1 == request.1 then (e.1, e.2.1, request.2) else e))
    | none => (.ok none, state)
  delete id state := (.ok (state.2.any (·.1 == id)), (state.1, state.2.filter (·.1 != id)))

/-- A broken repository: `insert` fails with the rows' error, and every other row answers as
`model` does. -/
def broken : Host Repo := { model with insert := fun _ state => (.error (.SqlError, "disk full"), state) }

/-- `broken`, written untyped: the failure as the tagged pair an untyped host writes
(`Test.Dogfood.Scenario.failed`). -/
def brokenUntyped : Run.Reactor Repo := fun row sent state =>
  if row.spelling == "TodoRepo.insert" then
    if sent matches .str _ then some (Test.Dogfood.Scenario.failed "SqlError" "disk full", state)
    else none
  else repository row sent state

/-! ## The battery: the typed model answers as `repository` does

Each line is a finite evaluation (decisions row 301). -/

/-- The repository's four rows. -/
def rows : RowTable := TodoRepo.rows.map (·.row)

/-- A state with two to-dos, the second done. -/
def twoTodos : Repo := (3, [(1, "milk", false), (2, "eggs", true)])

/-- Each request of the battery: a row's position, the request, and the state it meets. -/
def requests : List (Nat × Val × Repo) := [
  (0, .str "bread", twoTodos), (0, .str "", (1, [])),
  (1, .unit, twoTodos), (1, .unit, (1, [])),
  (2, .list [.nat 1, .bool true], twoTodos), (2, .list [.nat 9, .bool true], twoTodos),
  (3, .nat 2, twoTodos), (3, .nat 9, twoTodos)]

-- finite evaluation: on every request, the typed model answers as `repository` does.
#guard requests.all fun (i, request, state) =>
  match rows[i]? with
  | some row => model.reactor row request state == repository row request state
  | none => false
-- finite evaluation: the broken typed host fails as the untyped one does, the failure crossing as
-- the tagged pair, and answers every other row as it does.
#guard requests.all fun (i, request, state) =>
  match rows[i]? with
  | some row => broken.reactor row request state == brokenUntyped row request state
  | none => false
-- control: the broken host's insert answers otherwise than the model's, so the comparison above
-- reads the failure.
#guard (rows[0]?.map fun row => broken.reactor row (.str "bread") twoTodos !=
  model.reactor row (.str "bread") twoTodos) == some true
-- finite evaluation: the failure's code is the rows' error column `SqlError.ty`.
#guard Modeled.ty (α := SqlError) == Test.Dogfood.Scenario.Todo.SqlError.ty
-- control: a request that does not read is declined, as `repository` declines it.
#guard (rows[0]?.map fun row => (model.reactor row (.nat 3) twoTodos).isNone &&
  (repository row (.nat 3) twoTodos).isNone) == some true
-- finite evaluation: the derived `Todo`'s code is the row's record type `Todo.ty`.
#guard Modeled.ty (α := Todo) == Ty.normalize Test.Dogfood.Scenario.Todo.Todo.ty

end Test.Dogfood.Scenario.Todo.Typed
