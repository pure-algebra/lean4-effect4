import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Api.HostDrive
import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Routing

set_option maxRecDepth 8192

/-!
# The meaning under a run's tape: the battery of slices H7 and H8

`denoteRows_eq_session` is a theorem (slice H8). A line here is one of two things:

* a finite evaluation that real runs meet its premises, so that the theorem covers them;
* a control: for each premise, a run where it fails and the two sides differ.
-/

namespace Test.Api.SessionMeaning

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Denote
open Effect4.Run (appliedExits hostDriven funded atRest)
open Test.Dogfood.Scenario
open Test.Dogfood.P2HandlerLayers (built?)

/-- One run: the fragment, the three premises of `denoteRows_eq_session` on the run, and whether
its two sides are equal. -/
def sides (s : Run) : Bool × Bool × Bool × Bool × Bool :=
  (StraightRows s.built.table s.built.program, funded s, atRest s, hostDriven s,
    decide (meaningRows s.built.table s.built.program [] Stores.empty (appliedExits s) =
      s.exit.map fun ex => ((ex, s.machine.state), [])))

/-- The fragment and the three premises of `denoteRows_eq_session` on one run. -/
def premises (s : Run) : Bool × Bool × Bool × Bool :=
  (StraightRows s.built.table s.built.program, funded s, atRest s, hostDriven s)

/-- Every premise holds. -/
def green : Bool × Bool × Bool × Bool := (true, true, true, true)

/-! ## Real programs -/

section todo
open Test.Dogfood.Scenario.Todo

def onTodo (main : Src NativeOp) (moves : List Move) : Option (Bool × Bool × Bool × Bool) :=
  (built? (request main)).map fun b => premises (play (Run.open b "todo") moves)

-- finite evaluation: the runs of the four to-do programs meet the premises. The last three runs
-- end at the frontier: no reply, a reply that is not applied, and a reply outside the answer
-- column, which the session refuses
#guard [ onTodo (add (str "milk"))
           (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))])
       , onTodo (add (str ""))
           (script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))])
       , onTodo (complete (nat 1))
           (script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true)))])
       , onTodo (complete (nat 1))
           (script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" "locked")])
       , onTodo (complete (nat 7)) (script [[.start], answer (.row "TodoRepo.setDone") (ok .none)])
       , onTodo (remove (nat 7)) (script [[.start], answer (.row "TodoRepo.delete") (ok (.bool false))])
       , onTodo list
           (script [[.start], answer (.row "TodoRepo.all") (ok (.list [todo 1 "milk" true, todo 2 "tea" false]))])
       , onTodo list [.start]
       , onTodo list [.start, .receive (.row "TodoRepo.all") (ok (.list []))]
       , onTodo list (script [[.start], answer (.row "TodoRepo.all") (ok (.nat 3))]) ].all
  (· = some green)

end todo

-- finite evaluation: the routing program, in the fragment by its `catchIf` nodes (decisions row
-- 310), meets the premises on each of its eleven named runs
#guard Routing.runsAndControls.1.length = 11
#guard Routing.runsAndControls.1.all fun run => premises run.played = green

/-! ## Raw programs: each constructor of the fragment with a call inside -/

/-- One host row: a number in, a number out, a tagged failure. -/
def wait : Row := (Row.host "H.wait" .nat .nat (.prod .string .string) "battery").row
/-- One host row that answers an external handle. -/
def kvMake : Row := (Row.host "K.make" .unit NativeOp.kvTy (.prod .string .string) "battery").row

def call (n : Term) : NativeEff := .perform (.external 0) n
def num (n : Nat) : Term := .lit (.nat n)
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def reply (v : Nat) : List Move := answer (.row "H.wait") (ok (.nat v))
def refuse : List Move := answer (.row "H.wait") (failed "E" "m")
def failing (cause : CauseV) : List Move := answer (.row "H.wait") (.ofExit (.failure cause))

def raw (program : NativeEff) (table : RowTable) (moves : List Move)
    (budget : Effect4.Api.Budget := {}) : Option (Bool × Bool × Bool × Bool × Bool) :=
  ((Effect4.Api.Author.Internal.finishBuild program table []).toOption).map fun b =>
    sides (play (Run.open b "raw" budget) moves)

def rawPremises (program : NativeEff) (table : RowTable) (moves : List Move)
    (budget : Effect4.Api.Budget := {}) : Option (Bool × Bool × Bool × Bool) :=
  ((Effect4.Api.Author.Internal.finishBuild program table []).toOption).map fun b =>
    premises (play (Run.open b "raw" budget) moves)

/-- Three calls in sequence: each request is the reply before it. -/
def chain : NativeEff := .bind (call (num 1)) (.bind (call (.var 0)) (call (.var 1)))
def fin : NativeEff := .onExit (call (num 1)) (call (num 2))
def caught : NativeEff := .catchCause (call (num 1)) (call (num 2))
def matched : NativeEff := .matchCause (call (num 1)) (call (.var 0)) (call (num 9))
def exited : NativeEff := .exit (call (num 1))
def suspended : NativeEff := .suspend (.bind (call (num 1)) (.sync (.var 0)))
/-- A cell made, a call, the reply written to the cell, the cell read. -/
def celled : NativeEff :=
  .bind (.perform .refMake (num 0))
    (.bind (call (num 1))
      (.bind (.perform .refSet (pairT (.var 0) (.var 1))) (.perform .refGet (.var 0))))
/-- A call, then a clock read. -/
def clocked : NativeEff := .bind (call (num 1)) (.perform .clockNow (.lit .unit))

-- finite evaluation: runs of a success and a typed failure through each constructor, and a
-- frontier, meet the premises
#guard [ rawPremises chain [wait] (script [[.start], reply 5, reply 6, reply 7])
       , rawPremises chain [wait] (script [[.start], reply 5, refuse, reply 7])
       , rawPremises chain [wait] (script [[.start], reply 5, reply 6])
       , rawPremises fin [wait] (script [[.start], reply 5, refuse])
       , rawPremises fin [wait] (script [[.start], refuse, reply 6])
       , rawPremises caught [wait] (script [[.start], refuse, reply 6])
       , rawPremises matched [wait] (script [[.start], refuse, reply 6])
       , rawPremises exited [wait] (script [[.start], refuse])
       , rawPremises suspended [wait] (script [[.start], reply 5])
       , rawPremises celled [wait] (script [[.start], reply 5])
       , rawPremises clocked [wait] (script [[.start], reply 5]) ].all (· = some green)
-- finite evaluation: runs of a reply that fails with no typed error (a defect, an interruption,
-- an empty cause and a mixed cause), through each constructor that reads a failure, meet the
-- premises
#guard [ Cause.die (Defect.user 3), Cause.interrupt none, Cause.empty,
         Cause.combine (Cause.fail (.tagged "E" "m")) (Cause.interrupt (some ⟨0⟩)) ].all fun cause =>
  [ rawPremises chain [wait] (script [[.start], reply 5, failing cause, reply 7])
  , rawPremises fin [wait] (script [[.start], failing cause, reply 6])
  , rawPremises fin [wait] (script [[.start], reply 5, failing cause])
  , rawPremises caught [wait] (script [[.start], failing cause, reply 6])
  , rawPremises matched [wait] (script [[.start], failing cause, reply 6])
  , rawPremises exited [wait] (script [[.start], failing cause]) ].all (· = some green)

/-! ## Controls: for each premise, a run where it fails and the two sides differ -/

-- control (`hostDriven`): an interruption of the root while it waits
#guard raw chain [wait] (script [[.start], [.cancel ⟨0⟩], [.flush]]) =
  some (true, true, true, false, false)
-- control (`hostDriven`): a clock step before a clock read
#guard raw clocked [wait] (script [[.start], [.tick 5], reply 5]) =
  some (true, true, true, false, false)
-- control (`hostDriven`): a delayed cell read as the reply
#guard raw (.bind (.perform .refMake (num 7)) (call (num 1))) [wait]
    (script [[.start], answer (.row "H.wait") (.ofRefGet ⟨0⟩)]) =
  some (true, true, true, false, false)
-- control (`funded`): a command budget of 5 cuts the last step of three calls. The run is at
-- rest and no row is refused. 6 is the least command budget at which the run is funded
#guard raw chain [wait] (script [[.start], reply 5, reply 6, reply 7]) { fuel := 5, compileFuel := 1000 } =
  some (true, false, true, true, false)
#guard ((List.range 41).find? fun fuel =>
    rawPremises chain [wait] (script [[.start], reply 5, reply 6, reply 7])
      { fuel := fuel, compileFuel := 1000 } = some green) = some 6
-- control (`atRest`): a run that has not started, on a program with no call
#guard raw (.succeed (num 1)) [wait] [] = some (true, true, false, true, false)
-- control (`dataRow`): a row that answers a handle. The reply allocates, and the tree does not
#guard raw (.bind (.perform (.external 0) (.lit .unit)) (.succeed (num 1))) [kvMake]
    (script [[.start], answer (.row "K.make") (ok (.nat 0))]) =
  some (false, true, true, true, false)

-- finite evaluation: a compile budget below the program's depth leaves the run spinning at the
-- compile's frontier, which never settles. The run is neither funded nor at rest, so the theorem
-- takes no premise on the compile budget
#guard Effect4.Program.Sched.depthRows chain = 3
#guard [1, 2].all fun cf => raw chain [wait] (script [[.start], reply 5, reply 6, reply 7])
    { fuel := 1000, compileFuel := cf } = some (true, false, false, true, true)
#guard raw chain [wait] (script [[.start], reply 5, reply 6, reply 7])
    { fuel := 1000, compileFuel := 3 } = some (true, true, true, true, true)

-- finite evaluation (the premise reads the tape): a delayed cell read that the session receives
-- and never applies hands the machine nothing. The run is host-driven
#guard rawPremises (.bind (.perform .refMake (num 7)) (call (num 1))) [wait]
    [.start, .receive (.row "H.wait") (.ofRefGet ⟨0⟩)] = some green

/-! ## A host as a handler: an in-memory repository -/

section repository
open Test.Dogfood.Scenario.Todo

/-- A host function as a handler of the row signature, with the session's reply check on its
answer: an answer outside the row's columns is no answer. -/
def reactorHandler {σ : Type} (table : RowTable) (r : Run.Reactor σ) :
    Effects.Handler (RowSig table) (StateT σ Option) where
  handle op := fun state =>
    match externalRow table op.1.val with
    | none => none
    | some row =>
      match r row op.2 state with
      | some (.ofExit ex, next) =>
        if externalAdmits table op.1.val (.ofExit ex) [] then some (ex, next) else none
      | _ => none

/-- The repository's state: the next id and the to-dos. -/
abbrev Repo := Nat × List (Nat × String × Bool)

def todoOf (entry : Nat × String × Bool) : Val := todo entry.1 entry.2.1 entry.2.2

/-- An in-memory repository as a host function, row by row. -/
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

/-- Whether two results are one: the exit, the stores and the repository's state. The
comparison is by component: instance search does not reach the whole type at default limits. -/
def same (a b : Option ((ExitV × Stores) × Repo)) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => decide (x.1.1 = y.1.1) && decide (x.1.2 = y.1.2) && decide (x.2 = y.2)
  | _, _ => false

/-- The drive of a to-do program under the repository, against its meaning under the repository
as a handler: whether they are one, the exit, and the repository's state. -/
def driven (main : Src NativeOp) (state : Repo) : Option (Bool × Option ExitV × Repo) :=
  (built? (request main)).map fun b =>
    let run : Run × Repo := Run.runWith b repository state "todo"
    (same (meaningUnder (reactorHandler b.table repository) b.program [] Stores.empty state)
        (run.1.exit.map fun ex => ((ex, run.1.machine.state), run.2)),
      run.1.exit, run.2)

-- finite evaluation: the drive and the meaning are one on each program, from two states
#guard [driven (add (str "milk")) (1, []), driven (add (str "")) (1, []), driven list (1, []),
    driven list (3, [(1, "milk", false), (2, "tea", true)]),
    driven (complete (nat 1)) (3, [(1, "milk", false), (2, "tea", true)]),
    driven (complete (nat 7)) (3, [(1, "milk", false)]),
    driven (remove (nat 2)) (3, [(1, "milk", false), (2, "tea", true)]),
    driven (remove (nat 7)) (3, [(1, "milk", false)])].all fun r => (r.map (·.1)) = some true
-- finite evaluation of a fact under a host: after `add`, `list` answers the new to-do
#guard ((driven (add (str "milk")) (1, [])).bind fun added =>
    (driven list added.2.2).map fun listed => listed.2.1) =
  some (some (.success (.list [todo 1 "milk" false])))

/-- The premises of `denoteRows_eq_session_host` (H9) on a driven run: H8's four, the root
exited, and the repository's answers along the run's tape (`hostAnsweredCheck`, sound for
`HostAnswered`), from the start state to the run's end state. -/
def hostPremises (main : Src NativeOp) (state : Repo) : Option (Bool × Bool × Bool × Bool × Bool × Bool) :=
  (built? (request main)).map fun b =>
    let run : Run × Repo := Run.runWith b repository state "todo"
    let base := premises run.1
    (base.1, base.2.1, base.2.2.1, base.2.2.2, run.1.exit.isSome,
      Run.hostAnsweredCheck b.table (Run.reactorHost b.table repository) b.program run.1.budget.fuel
        (tapeOf run.1) (Api.load b.program run.1.budget.compileFuel) state == some run.2)

-- finite evaluation: each driven run meets the premises of H9 under the repository host, so
-- `denoteRows_eq_session_host` covers it: the host's run of the call tree is the run's exit
#guard [hostPremises (add (str "milk")) (1, []), hostPremises (add (str "")) (1, []),
    hostPremises list (1, []), hostPremises list (3, [(1, "milk", false), (2, "tea", true)]),
    hostPremises (complete (nat 1)) (3, [(1, "milk", false), (2, "tea", true)]),
    hostPremises (complete (nat 7)) (3, [(1, "milk", false)]),
    hostPremises (remove (nat 2)) (3, [(1, "milk", false), (2, "tea", true)]),
    hostPremises (remove (nat 7)) (3, [(1, "milk", false)])].all
  (· = some (true, true, true, true, true, true))

-- control: from another start state, the run's answers are not the host's answers there
#guard ((built? (request (add (str "milk")))).map fun b =>
    let run : Run × Repo := Run.runWith b repository (1, []) "todo"
    Run.hostAnsweredCheck b.table (Run.reactorHost b.table repository) b.program run.1.budget.fuel
      (tapeOf run.1) (Api.load b.program run.1.budget.compileFuel) (5, [])) = some none

/-- A drive under the repository behind its rows' types (`Run.Reactor.guardRows`): the
premises of `runWith_guarded_denotes` (the fragment, funded, at rest, the root exited), and
whether the guarded drive ends as the unguarded one, at the exit and the repository's state. -/
def guardedPremises (reactor : Run.Reactor Repo) (main : Src NativeOp) (state : Repo) :
    Option (Bool × Bool × Bool × Bool × Bool) :=
  (built? (request main)).map fun b =>
    let run : Run × Repo := Run.runWith b reactor state "todo"
    let guarded : Run × Repo := Run.runWith b reactor.guardRows state "todo"
    (StraightRows b.table b.program, funded guarded.1, atRest guarded.1, guarded.1.exit.isSome,
      decide (guarded.1.exit = run.1.exit) && decide (guarded.2 = run.2))

-- finite evaluation: behind its rows' types the repository drives each run as before, and the
-- run meets the premises of `runWith_guarded_denotes`, which needs no envelope premise
#guard [guardedPremises repository (add (str "milk")) (1, []),
    guardedPremises repository list (3, [(1, "milk", false), (2, "tea", true)]),
    guardedPremises repository (complete (nat 1)) (3, [(1, "milk", false), (2, "tea", true)]),
    guardedPremises repository (remove (nat 7)) (3, [(1, "milk", false)])].all
  (· = some (true, true, true, true, true))

/-- The repository with its listing answered by a string, outside the row's answer column. -/
def mislisting : Run.Reactor Repo := fun row sent state =>
  if row.spelling == "TodoRepo.all" then some (ok (.str "oops"), state) else repository row sent state

-- control: the guard refuses the answer outside the row's columns, so the guarded drive leaves
-- the call waiting and the root has no exit, where the theorem says nothing
#guard (guardedPremises mislisting list (1, [])).map (fun p => p.2.2.2.1) = some false

/-- A session recorded and replayed through `Effects`' hosts. The repository, read as a host
and recording each exit it gives (`Comodel.record`), drives the run (`Run.Reactor.ofHost`). The
reply tape of that recording (`tapeHost`) then drives it again. The premises of
`runWith_host_denotes` on the recorded run (distinct keys and the fragment, funded and at rest,
the root exited); whether the recorded run ends as the plain drive; and whether the replay ends
at the same exit with the tape spent. -/
def recordReplay (main : Src NativeOp) (state : Repo) :
    Option (Bool × Bool × Bool × Bool × Bool × Bool) :=
  (built? (request main)).map fun b =>
    let plain : Run × Repo := Run.runWith b repository state "todo"
    let recorder := (Run.reactorHost b.table repository).record fun _ ex => ex
    let recorded := Run.runWith b (Run.Reactor.ofHost b.table recorder).guardRows (state, []) "todo"
    let replayed :=
      Run.runWith b (Run.Reactor.ofHost b.table (tapeHost b.table)).guardRows recorded.2.2 "todo"
    (decide ((b.table.map rowKey).Nodup) && StraightRows b.table b.program,
      funded recorded.1 && atRest recorded.1,
      decide (recorded.1.exit = plain.1.exit) && decide (recorded.2.1 = plain.2),
      recorded.1.exit.isSome,
      decide (replayed.1.exit = recorded.1.exit),
      replayed.2.isEmpty)

-- finite evaluation: a recorded session drives each run as the repository does and meets the
-- premises of `runWith_host_denotes`; its transcript, replayed as a tape, drives the run again
-- to the same exit and is spent
#guard [recordReplay (add (str "milk")) (1, []),
    recordReplay list (3, [(1, "milk", false), (2, "tea", true)]),
    recordReplay (complete (nat 1)) (3, [(1, "milk", false), (2, "tea", true)]),
    recordReplay (remove (nat 7)) (3, [(1, "milk", false)])].all
  (· = some (true, true, true, true, true, true))

-- control: a transcript short of its last exit leaves the replay's last call waiting
#guard ((built? (request list)).map fun b =>
    let recorder := (Run.reactorHost b.table repository).record fun _ ex => ex
    let recorded :=
      Run.runWith b (Run.Reactor.ofHost b.table recorder).guardRows ((3, [(1, "milk", false)]), []) "todo"
    (Run.runWith b (Run.Reactor.ofHost b.table (tapeHost b.table)).guardRows
      recorded.2.2.dropLast "todo").1.exit) = some none

/-- A locked database: a typed failure that the rows' error column admits. -/
def lockedExit : ExitV :=
  match failed "SqlError" "locked" with
  | .ofExit ex => ex
  | _ => .success .unit

/-- A flaky repository: every other call fails as locked, starting with the first. -/
def flaky (table : RowTable) : Effects.Comodel (RowSig table) (Repo × Bool) where
  answer op state :=
    if state.2 then some (lockedExit, (state.1, false))
    else ((Run.reactorHost table repository).answer op state.1).map fun result =>
      (result.1, (result.2, true))

/-- A drive of a to-do program by a host read as a reactor behind the rows' types: the premises
of `runWith_host_denotes` (distinct keys and the fragment, funded and at rest), and the exit. -/
def hostDrive (host : (table : RowTable) → Effects.Comodel (RowSig table) (Repo × Bool))
    (main : Src NativeOp) (state : Repo) : Option (Bool × Bool × Option ExitV) :=
  (built? (request main)).map fun b =>
    let run := Run.runWith b (Run.Reactor.ofHost b.table (host b.table)).guardRows (state, true)
      "todo"
    (decide ((b.table.map rowKey).Nodup) && StraightRows b.table b.program,
      funded run.1 && atRest run.1, run.1.exit)

/-- The exit of the plain drive under the repository. -/
def plainExit (main : Src NativeOp) (state : Repo) : Option (Option ExitV) :=
  (built? (request main)).map fun b => (Run.runWith b repository state "todo").1.exit

-- finite evaluation: behind the retry layer the flaky repository drives each run to the plain
-- exit, and the run meets the premises of `runWith_layer_denotes` that a run can show
#guard [(add (str "milk"), ((1, []) : Repo)), (list, (3, [(1, "milk", false), (2, "tea", true)])),
    (complete (nat 1), (3, [(1, "milk", false), (2, "tea", true)])),
    (remove (nat 7), (3, [(1, "milk", false)]))].all fun (main, state) =>
  (hostDrive (fun table => (flaky table).through (Run.retry table)) main state).map
      (fun result => (result.1, result.2.1, decide (some result.2.2 = plainExit main state))) =
    some (true, true, true)

-- control: without the retry the first call fails as locked, and the run's exit differs
#guard ((hostDrive flaky (add (str "milk")) (1, [])).map fun result =>
    decide (some result.2.2 = plainExit (add (str "milk")) (1, []))) = some false

end repository

end Test.Api.SessionMeaning
