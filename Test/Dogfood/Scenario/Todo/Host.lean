import Test.Dogfood.Scenario.Todo.Claims
import Test.Dogfood.Scenario.Todo.Cached
import Tools.RunChecks

/-!
# The to-do application's host run, as the LCNF route lowers it (LC-6)

One request of the to-do application: the cached service consumer built at the request's entry
and literal arguments (`consumerBuiltAt`), driven by `Run.runWith` with a host that answers as a
reference repository does and records each call. The LCNF route translates `serve` and
`serveForgetful` into `ocaml/apps/todo/todo_gen.ml`, so the OCaml face builds and runs each
request with code made from these definitions. `apps/todo/Check.lean` checks the records it
writes, as it checks the TypeScript face's.

`serveForgetful` answers as `forgetful` does (`Test/Dogfood/Scenario/Todo/Claims.lean`): its runs
conform, and they do not agree with the model. That is the face's red control.

Each line below is a finite evaluation or a control (decisions row 301).
-/

namespace Test.Dogfood.Scenario.Todo.Host

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.Todo (repository Repo)
open Test.Dogfood.Scenario.Todo.Cached (consumerBuiltAt)
open Tools.RunChecks (Call literal)

/-- The external row position of a row of the table: the index `externalRow` reads it back at. -/
def externalIndex (table : RowTable) (row : Row) : Nat :=
  ((List.range table.length).find? fun i => decide (externalRow table i = some row)).getD 0

/-- A host that answers as `inner` does and records each call it answers: the row's external
position, the request and the completion. -/
def recording {σ : Type} (table : RowTable) (inner : Run.Reactor σ) :
    Run.Reactor (σ × List Call) := fun row request state =>
  (inner row request state.1).map fun (answer, next) =>
    (answer, (next, state.2 ++ [⟨externalIndex table row, request, answer⟩]))

/-- One request's run under `host`: each answered call, the root's exit, and the host's next
state. `none` where the entry does not build at the arguments. -/
def serveWith (host : Run.Reactor Repo) (entry : String) (args : List Val) (state : Repo) :
    Option ((List Call × Option ExitV) × Repo) := do
  let lits ← args.mapM literal
  let built ← consumerBuiltAt entry (lits.map Authoring.lit)
  let (run, next, calls) := Run.runWith built (recording built.table host) (state, [])
  return ((calls, run.exit), next)

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

/-- One request over the reference repository. -/
def serve (entry : String) (args : List Val) (state : Repo) :
    Option ((List Call × Option ExitV) × Repo) :=
  serveWith repository entry args state

/-- One request over the repository that forgets a write: the face's red control. -/
def serveForgetful (entry : String) (args : List Val) (state : Repo) :
    Option ((List Call × Option ExitV) × Repo) :=
  serveWith Test.Dogfood.Scenario.Todo.forgetful entry args state

-- finite evaluation: an add from the empty store answers through one call and finishes.
#guard ((serve "add" [.str "milk"] (1, [])).map fun r => (r.1.1.length, r.1.2.isSome, r.2.1)) ==
  some (1, true, 2)
-- finite evaluation: the built form answers as `serve` does.
#guard ((consumerBuiltAt "add" [Authoring.lit (.str "milk")]).map fun b =>
  ((serveBuilt b (1, [])).1.1.length, (serveBuilt b (1, [])).2.1)) == some (1, 2)
-- control: an unknown entry builds nothing.
#guard (serve "missing" [] (1, [])).isNone

end Test.Dogfood.Scenario.Todo.Host
