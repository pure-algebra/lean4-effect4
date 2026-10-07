import Effect4.Laws.Api.SessionRef
import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.QueueWorkers

set_option maxRecDepth 8192

/-!
# The reference machine at a row table: the battery of slice H5

Each line is a finite evaluation of an open statement, or a
control. `run_eq_ref_table` is a planned goal: these lines are its finite evidence, and they
shrink in the slice that proves it.
-/

namespace Test.Program.TableReference

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Sched
open Test.Dogfood.Scenario
open Test.Dogfood.P2HandlerLayers (built?)

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

/-- Funded, both statements hold, and the reference machine at the empty row table agrees too. -/
def green : Bool × Bool × Bool × Bool := (true, true, true, true)

/-! ## Real programs -/

section todo
open Test.Dogfood.Scenario.Todo

def onTodo (main : Src NativeOp) (moves : List Move) : Option (Bool × Bool × Bool × Bool) :=
  (built? (request main)).map fun b => sides (play (Run.open b "todo") moves)

-- finite evaluation: the four to-do programs, answered, failed, and waiting
#guard [ onTodo (add (str "milk"))
           (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))])
       , onTodo (add (str ""))
           (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))])
       , onTodo (complete (nat 1))
           (script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" "locked")])
       , onTodo (remove (nat 7)) (script [[.start], answer (.row "TodoRepo.delete") (ok (.bool false))])
       , onTodo list
           (script [[.start], answer (.row "TodoRepo.all") (ok (.list [todo 1 "milk" true, todo 2 "tea" false]))])
       , onTodo list [.start] ].all (· = some green)

end todo

-- finite evaluation: each named run of the routing scenario
#guard Routing.runsAndControls.1.all fun run => sides run.played = green
-- finite evaluation: programs with fibers, a queue and timers. Each run that is funded meets both
-- statements. Control (`funded`): the two runs that a budget cuts fail the session statement, and
-- the raw statement holds on them
#guard QueueWorkers.runsAndControls.1.length = 31
#guard (QueueWorkers.runsAndControls.1.filterMap fun run =>
    if sides run.played = green then none else some (run.name, sides run.played)) =
  [("starved", (false, false, true, true)), ("dropped", (false, false, true, true))]

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
/-- A call, then a clock read. -/
def clocked : NativeEff := .bind (call (num 1)) (.perform .clockNow (.lit .unit))
/-- A cell, then a call. -/
def cellThenCall : NativeEff := .bind (.perform .refMake (num 7)) (call (num 1))
/-- Two handles acquired, then the second used. -/
def handled2 : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit))
    (.bind (.perform (.external 0) (.lit .unit)) (.perform (.external 1) (.var 1)))

-- finite evaluation: an interruption of the waiting root, a clock step and a delayed cell read
-- are in reach of both statements
#guard [ raw chain [wait] (script [[.start], [.cancel ⟨0⟩], [.flush]])
       , raw clocked [wait] (script [[.start], [.tick 5], reply 5])
       , raw cellThenCall [wait] (script [[.start], answer (.row "H.wait") (.ofRefGet ⟨0⟩)]) ].all
  (· = some green)
-- control (`funded` in `session_eq_ref`): a command budget of 5 cuts the last step of three
-- calls. No row is refused, the session statement fails, and the raw statement holds
#guard raw chain [wait] (script [[.start], reply 5, reply 6, reply 7]) { fuel := 5, compileFuel := 1000 } =
  some (false, false, true, true)
-- finite evaluation: a handle row. Control (the row table): the reference machine at the empty
-- row table does not allocate, and it disagrees
#guard raw handled2 [kvMake, kvUse]
    (script [[.start], answer (.row "K.make") (ok (.nat 0)), answer (.row "K.make") (ok (.nat 1)),
      answer (.row "K.use") (ok (.nat 9))]) = some (true, true, true, false)

/-! ## Raw decision tapes: answers that no session admits -/

/-- Eight answers: three values, three failures, two delayed cell reads. -/
def answersPool : List Answer :=
  [ .ofExit (.success (.nat 5)), .ofExit (.success (.str "x")), .ofExit (.success (.nat 0)),
    .ofExit (.failure (Cause.fail (.tagged "E" "m"))), .ofExit (.failure (Cause.die (Defect.user 3))),
    .ofExit (.failure (Cause.interrupt none)), .ofRefGet ⟨0⟩, .ofRefGet ⟨9⟩ ]

/-- A decision alphabet: flush, evaluate, a clock step, an interruption, and each answer of the
pool at two tokens and two fibers. -/
def decisions : List Api.Decision :=
  [Api.flush, Api.evaluate, .advance (ClockMillis.ofNat 5), .interruptFrom none .empty Api.root] ++
    (answersPool.flatMap fun a =>
      [RunDecision.answerAsync Api.root 0 a, .answerAsync Api.root 1 a, .answerAsync ⟨1⟩ 0 a])

/-- Every tape of at most `n` decisions. -/
def tapes : Nat → List (List Api.Decision)
  | 0 => [[]]
  | n + 1 => [] :: (decisions.flatMap fun d => (tapes n).map fun rest => d :: rest)

/-- After the root's evaluation, for every tape of at most `n` decisions: the count where the
frame machine and the reference machine disagree, the same count with the reference machine at
the empty row table, and the count of tapes. -/
def disagreements (e : NativeEff) (table : RowTable) (n : Nat) (fuel : Nat := 200) : Nat × Nat × Nat :=
  let all := (tapes n).map fun tape => Api.evaluate :: tape
  ((all.filter fun tape => !agreeRaw e table fuel tape).length,
   (all.filter fun tape => !agreeEmpty e table fuel tape).length, all.length)

-- finite evaluation: 813 tapes over an alphabet of 28 decisions, on data rows and on handle rows.
-- Control (the row table): at handle rows the reference machine at the empty row table disagrees
#guard disagreements chain [wait] 2 = (0, 0, 813)
#guard disagreements handled2 [kvMake, kvUse] 2 = (0, 52, 813)

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
