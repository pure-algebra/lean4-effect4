import Effect4.Author
import Effect4.Run.Live
import Tools.Code.Module
import Tools.Query

/-!
# The agent-ergonomics probe, Lean half: the three programs through the authoring lifts

A finite probe, not a battery. Run it with
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-13-agent-ergonomics-probe/Probe.lean`.
Each `#eval` prints one line: the built type, the printed TypeScript, a run's exit compared with
a guessed value, or a located refusal. `ExitV`, `EffTy`, `TypeReason` and `TypeScript.Expr` have
no `Repr`, so the probe renders through `Ty.render`, `Tools.Code.codeLines` and
`Tools.Query.refusalJson`, and it compares an exit with `==`.
-/

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

namespace AgentErgonomics

-- A row may not be named `open`, and a definition may not be named `show`: Lean keywords.
eff_rows Todos error .never cite "probe" where
  add(.string) : .list .string

eff_rows Db error .never cite "probe" where
  connect(.string) : .nat,
  disconnect(.nat) : .unit,
  query(.nat) : .string

/-- (a) add a to-do through the host row, answer the list's length -/
def addTodo : Src NativeOp := eff do
  let todos ← Todos.add (str "milk")
  succeed (app "length" [todos])

/-- (b) acquire a connection in a scope, release it by disconnecting -/
def useDb : Src NativeOp := scope (eff do
  let conn ← acquireWith (Db.connect (str "db")) fun c => Db.disconnect c
  Db.query conn)

/-- (c) fork two children, join both, add -/
def forkJoin : Src NativeOp := eff do
  let f1 ← fork (succeed (nat 1))
  let f2 ← fork (succeed (nat 2))
  let x ← join f1
  let y ← join f2
  succeed (app "add" [x, y])

/-- The build's type and printed module, or its located refusal. -/
def report (m : Module NativeOp) : String :=
  match Api.Author.build m with
  | .ok b => s!"ok {b.ty.answer.render} / {b.ty.error.render}\n" ++
      (match Tools.Code.codeLines 100 b.program b.table with
       | .ok ls => "\n".intercalate ls
       | .error why => s!"print refused: {why}")
  | .error (.scope r) => s!"scope refusal at {r.path}: {reprStr r.reason}"
  | .error (.typing r) => s!"typing refusal: {(Tools.Query.refusalJson r).compress}"
  | .error _ => "other refusal"

#eval IO.println (report { rows := Todos.rows, main := addTodo })
#eval IO.println (report { rows := Db.rows, main := useDb })
#eval IO.println (report { main := forkJoin })

-- (c) runs on the Lean machine with no host.
#eval (Api.Author.build { main := forkJoin }).toOption.map fun b => b.runSync == .success (.nat 3)

/-- An answer of a value. -/
def ok (value : Val) : Api.HostSession.Answer := .ofExit (.success value)

-- (b) runs through the host session's face, the host answering each of its three calls.
#eval (Api.Author.build { rows := Db.rows, main := useDb }).toOption.map fun b =>
  ((Live.open b "probe").feedAll
    [.start,
     .receive (.row "Db.connect") (ok (.nat 7)), .apply (.row "Db.connect"),
     .receive (.row "Db.query") (ok (.str "rows")), .apply (.row "Db.query"),
     .receive (.row "Db.disconnect") (ok .unit), .apply (.row "Db.disconnect"), .flush]).run.exit
    == some (.success (.str "rows"))

-- Refusals, as an agent meets them: a misspelled atom, an unbound name, an argument of the wrong
-- type, a request of the wrong type, a row the module does not declare.
#eval report { rows := Todos.rows, main := eff do
  let todos ← Todos.add (str "milk")
  succeed (app "lenght" [todos]) }
#eval report { rows := Todos.rows, main := eff do
  let _todos ← Todos.add (str "milk")
  succeed (app "length" [var "todo"]) }
#eval report { rows := Todos.rows, main := eff do
  let todos ← Todos.add (str "milk")
  succeed (app "add" [todos, nat 1]) }
#eval report { rows := Todos.rows, main := Todos.add (nat 3) }
#eval report { main := Todos.add (str "x") }

end AgentErgonomics
