import Effect4.Laws.Api.SessionRef
import Test.Dogfood.Scenario

set_option maxRecDepth 8192

/-!
# The reference machine at a row table: the battery of slice H5

Each line is a control or a finite evaluation that no theorem covers (decisions row 301).
`session_eq_ref` and the raw statement with no preloaded answer (`run_eq_ref_table_noPreload`)
are theorems since slice H6a (decisions row 314), so no line evaluates them. What stays: one red
control of the premise `funded` and one of the row table, and the finite evidence of the rest of
the planned goal `run_eq_ref_table`, the preloaded answers. The replay of the 31 runs of
`QueueWorkers` and the sweep of 813 tapes are cut: each repeated one of these controls, or
evaluated the theorems.
-/

namespace Test.Program.TableReference

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Sched
open Test.Dogfood.Scenario

abbrev Answer := Completion Val Err Defect FiberId Ann

/-- The reference machine's replay at a row table, with the arguments in the order of the table. -/
def ref (e : NativeEff) (table : RowTable) (fuel : Nat) (tape : List Api.Decision)
    (compileFuel : Nat) (answers : List Answer := []) : RReplay :=
  replayR e fuel tape compileFuel table answers

/-- The conclusion of `run_eq_ref_table` at one program, table, budget, tape and preloaded
answers. -/
def agreeRaw (e : NativeEff) (table : RowTable) (fuel : Nat) (tape : List Api.Decision)
    (answers : List Answer := []) (compileFuel : Nat := fuel) : Bool :=
  let frame := Api.replay e fuel tape answers table compileFuel
  let r := ref e table fuel tape compileFuel answers
  decide (frame.outcome = classify r) && decide (obs frame.machine = obsR r.machine)

/-- The same with the reference machine at the empty row table: the control. -/
def agreeEmpty (e : NativeEff) (table : RowTable) (fuel : Nat) (tape : List Api.Decision)
    (compileFuel : Nat := fuel) : Bool :=
  let frame := Api.replay e fuel tape [] table compileFuel
  let r := ref e [] fuel tape compileFuel
  decide (frame.outcome = classify r) && decide (obs frame.machine = obsR r.machine)

/-- A run: whether it is funded, the conclusion of `session_eq_ref` on it, the conclusion of
`run_eq_ref_table` at its own tape, and the latter with the reference machine at the empty row
table. -/
def sides (s : Run) : Bool × Bool × Bool × Bool :=
  let r := ref s.built.program s.built.table s.budget.fuel (Run.tapeOf s) s.budget.compileFuel
  (Run.funded s,
    decide (s.inspect.outcome = classify r) && decide (obs s.machine = obsR r.machine),
    agreeRaw s.built.program s.built.table s.budget.fuel (Run.tapeOf s) [] s.budget.compileFuel,
    agreeEmpty s.built.program s.built.table s.budget.fuel (Run.tapeOf s) s.budget.compileFuel)

/-! ## Raw programs -/

def wait : Row := (Row.host "H.wait" .nat .nat (.prod .string .string) "battery").row
def kvMake : Row := (Row.host "K.make" .unit NativeOp.kvTy (.prod .string .string) "battery").row
def kvUse : Row := (Row.host "K.use" NativeOp.kvTy .nat (.prod .string .string) "battery").row

def call (n : Term) : NativeEff := .perform (.external 0) n
def num (n : Nat) : Term := .lit (.nat n)
def reply (v : Nat) : List Move := answer (.row "H.wait") (ok (.nat v))

def raw (program : NativeEff) (table : RowTable) (moves : List Move)
    (budget : Effect4.Api.Budget := {}) : Option (Bool × Bool × Bool × Bool) :=
  ((Effect4.Api.Author.Internal.finishBuild program table []).toOption).map fun b =>
    sides (play (Run.open b "raw" budget) moves)

/-- Three calls in sequence: each request is the reply before it. -/
def chain : NativeEff := .bind (call (num 1)) (.bind (call (.var 0)) (call (.var 1)))
/-- Two handles acquired, then the second used. -/
def handled2 : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit))
    (.bind (.perform (.external 0) (.lit .unit)) (.perform (.external 1) (.var 1)))

-- control (`funded` in `session_eq_ref`): a command budget of 5 cuts the last step of three
-- calls. No row is refused, the session statement fails, and the raw statement holds
#guard raw chain [wait] (script [[.start], reply 5, reply 6, reply 7]) { fuel := 5, compileFuel := 1000 } =
  some (false, false, true, true)
-- control (the row table): at a handle row the reference machine at the empty row table does not
-- allocate, and it disagrees
#guard raw handled2 [kvMake, kvUse]
    (script [[.start], answer (.row "K.make") (ok (.nat 0)), answer (.row "K.make") (ok (.nat 1)),
      answer (.row "K.use") (ok (.nat 9))]) = some (true, true, true, false)

/-! ## Preloaded answers -/

-- finite evaluation: preloaded answers, taken at registration: answered, refused by its column,
-- too few, and at a handle row
#guard [ agreeRaw chain [wait] 200 [Api.evaluate, Api.flush]
           [.ofExit (.success (.nat 5)), .ofExit (.success (.nat 6)), .ofExit (.success (.nat 7))]
       , agreeRaw chain [wait] 200 [Api.evaluate, Api.flush]
           [.ofExit (.success (.nat 5)), .ofExit (.success (.str "x"))]
       , agreeRaw chain [wait] 200 [Api.evaluate, Api.flush] [.ofExit (.success (.nat 5))]
       , agreeRaw handled2 [kvMake, kvUse] 200 [Api.evaluate, Api.flush]
           [.ofExit (.success (.nat 0)), .ofExit (.success (.nat 1)), .ofExit (.success (.nat 9))] ].all id
-- control (`Test/contracts/machine-scheduler-core.contract.md`, "Table-aware agreement"): request
-- 7, reply 9, fuel 40. The frame machine finishes. The reference machine with no row table and no
-- preloaded answer stays at a frontier, and at the row table with the answer it agrees
#guard (Api.replay (call (num 7)) 40 [Api.evaluate, Api.flush] [.ofExit (.success (.nat 9))] [wait]).outcome
    = .finished &&
  classify (ref (call (num 7)) [] 40 [Api.evaluate, Api.flush] 40) = .frontier &&
  agreeRaw (call (num 7)) [wait] 40 [Api.evaluate, Api.flush] [.ofExit (.success (.nat 9))]

end Test.Program.TableReference
