import Test.Dogfood.Scenario.Todo.HostRun
import Test.Dogfood.Scenario.Todo.Scenario
import Test.Dogfood.Scenario.Todo.Cached
import Tools.RunRecord

/-!
# The to-do application's host run, from an entry (LC-6)

One request of the to-do application: the cached service consumer built at the request's entry
and literal arguments (`consumerBuiltAt`), then run as `Test/Dogfood/Scenario/Todo/HostRun.lean`
runs a built request. The LCNF route lowers that module's roots, and the lane
`ocaml/engine/test/todo/` compares their results with Lean's, byte for byte.

`serveForgetful` answers as `forgetful` does (`Test/Dogfood/Scenario/Todo/Scenario.lean`): its runs
conform, and they do not agree with the model. That is the face's red control.

Each line below is a finite evaluation or a control (decisions row 301).
-/

namespace Test.Dogfood.Scenario.Todo.Host

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.Todo (repository Repo)
open Test.Dogfood.Scenario.Todo.Cached (consumerBuiltAt)
open Tools.RunChecks (Call literal)

/-- One request's run under `host`: each answered call, the root's exit, and the host's next
state. `none` where the entry does not build at the arguments. -/
def serveWith (host : Run.Reactor Repo) (entry : String) (args : List Val) (state : Repo) :
    Option ((List Call × Option ExitV) × Repo) := do
  let lits ← args.mapM literal
  let built ← consumerBuiltAt entry (lits.map Authoring.lit)
  let (run, next, calls) := Run.runWith built (recording built.table host) (state, [])
  return ((calls, run.exit), next)

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
