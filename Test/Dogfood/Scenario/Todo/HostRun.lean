import Test.Dogfood.Scenario.Todo.Runs
import Tools.RunRecord

/-!
# The to-do's host run of one built request, the LCNF route's roots (LC-6)

A built request driven by `Run.runWith` under a host that answers as a repository does and records
each call: the reference repository (`repository`) and the one that forgets a write
(`forgetful`), the face's red control. `serveBuiltVal` and `serveBuiltForgetfulVal` give the whole
result as one value. The LCNF route lowers them into `ocaml/engine/test/todo/todo_gen.ml`
(`ocaml/gen/roots.json`), and the lane there compares each request's result with Lean's, byte for
byte (`Test/Dogfood/Scenario/Todo/HostLane.lean` writes its fixture).

This module and its imports reach no law module, so a change of the law graph re-cuts neither
the lowered artifact nor its fixture. `Test/Dogfood/Scenario/Todo/Host.lean` builds requests
from entries and holds the battery.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Todo.Host

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.Todo (repository forgetful Repo)
open Tools.RunChecks (Call)

/-- The external row position of a row of the table: the index `externalRow` reads it back at. -/
def externalIndex (table : RowTable) (row : Row) : Nat :=
  ((List.range table.length).find? fun i => decide (externalRow table i = some row)).getD 0

/-- A host that answers as `inner` does and records each call it answers: the row's external
position, the request and the completion. -/
def recording {σ : Type} (table : RowTable) (inner : Run.Reactor σ) :
    Run.Reactor (σ × List Call) := fun row request state =>
  (inner row request state.1).map fun (answer, next) =>
    (answer, (next, state.2 ++ [⟨externalIndex table row, request, answer⟩]))

/-- One built request over the reference repository: the run from the built program, with the
reactor fixed, so the route sees a known callback. `serve` reaches it through the build. -/
def serveBuilt (built : Api.Built) (state : Repo) : (List Call × Option ExitV) × Repo :=
  let (run, next, calls) := Run.runWith built (recording built.table repository) (state, [])
  ((calls, run.exit), next)

/-- One built request over the repository that forgets a write: the face's red control. -/
def serveBuiltForgetful (built : Api.Built) (state : Repo) : (List Call × Option ExitV) × Repo :=
  let (run, next, calls) :=
    Run.runWith built (recording built.table Test.Dogfood.Scenario.Todo.forgetful) (state, [])
  ((calls, run.exit), next)

/-! ## The lane's roots: one request's result as one value

The OCaml lane `ocaml/engine/test/todo/` runs these two, lowered, and compares the canonical bytes
of their value with Lean's (`Test.Dogfood.Scenario.Todo.HostLane`). -/

/-- A host's answer as a value: an exit's image (`exitImage`), or a cell's index, each behind its
constructor's position. -/
def answerVal : Api.HostSession.Answer → Val
  | .ofExit exit => .list [.nat 0, exitImage.toVal exit]
  | .ofRefGet cell => .list [.nat 1, .nat cell.index]

/-- The repository's state as a value: the next id, then each to-do's id, title and flag. -/
def repoVal (state : Repo) : Val :=
  .list [.nat state.1,
    .list (state.2.map fun entry => .list [.nat entry.1, .str entry.2.1, .bool entry.2.2])]

/-- One request's result as one value: each call (its row, request and answer), the root's exit,
and the repository's next state. -/
def resultVal (result : (List Call × Option ExitV) × Repo) : Val :=
  .list [.list (result.1.1.map fun call => .list [.nat call.row, call.request, answerVal call.completion]),
    (match result.1.2 with
      | some exit => .some (exitImage.toVal exit)
      | none => .none),
    repoVal result.2]

/-- `serveBuilt`'s result as one value. -/
def serveBuiltVal (built : Api.Built) (state : Repo) : Val := resultVal (serveBuilt built state)

/-- `serveBuiltForgetful`'s result as one value. -/
def serveBuiltForgetfulVal (built : Api.Built) (state : Repo) : Val :=
  resultVal (serveBuiltForgetful built state)

end Test.Dogfood.Scenario.Todo.Host
