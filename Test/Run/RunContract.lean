import Effect4.Laws.Run
import Test.Api.RunnerContract

/-!
# Run contract: the two examples of the run-API scout, written against `Run`

Scout A's §5 examples (`docs/research/2026-09-17-host-session-api-scout-A.md`), each run
through `Run` instead of the hand-written session steps they are written as today:

* **A service call.** The program of `Test/Api/HostSessionContract.lean` — two host calls in
  sequence — answered by a host that echoes the request. The pin: the rows the drive chose
  are exactly the journal `Test/Api/RunnerContract.lean` writes by hand, plus the flush that
  ends it, and nothing in this file names a call id, a guard token or a reply.
* **A fork and an await.** The program of `Test/Api/KeyedHostContract.lean` — two children
  forked, each parked on a host call, both awaited. The battery there writes the child fiber
  numbers and the guard tokens by hand; here neither appears.

The program is still built as an `Eff` tree with its certificate written out: the authoring
sugar is the Author seat's, and `Api.Built` is where the two seats meet.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.Run.RunContract

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key)

/-! ## A service call -/

/-- The host of both examples: whatever was asked for comes back as the answer. It is the
Scalar profile's own rule (`Program/Profile.lean`, `Scalar.outcome?`). -/
def echo : Run.Reactor Unit := fun _ request st => some (.ofExit (.success request), st)

/-- Two host calls in sequence, with the table and the certificate of
`Test/Api/HostSessionContract.lean`. -/
def twice : Api.Built :=
  { table := Test.Api.HostSessionContract.table
    program := Test.Api.HostSessionContract.program
    admitted := Test.Api.HostSessionContract.admitted
    rowNames := [("Host.wait", 0)] }

/-- The run the host drove, opened under the name the hand-written battery uses. -/
def driven : Run := (Run.runWith twice echo () (id := "session-A")).1

-- The rows the drive chose are the journal the hand-written battery spells out, and the
-- flush that ends the drive.
#guard driven.journal = Test.Api.RunnerContract.journal ++ Rows.flush
#guard driven.phases =
  [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied, .progressed]
#guard driven.exit = some (.success (.nat 3))
#guard driven.observe.state = .terminated
#guard driven.observe.outcome = .finished
#guard driven.observe.applied = 2
#guard driven.observe.awaiting = []
#guard driven.observe.pending = []
#guard driven.observe.reasons = []

-- The run replays from its own journal, with no host.
#guard ((Run.open twice "session-A").play driven.journal).exit = driven.exit
#guard ((Run.open twice "session-A").play driven.journal).observe = driven.observe

-- Opened, the run has done nothing; started, it is parked on the first call.
#guard (Run.open twice "session-A").outstanding = []
#guard ((Run.open twice "session-A").play Rows.start).outstanding =
  [⟨Api.root, 0, .external 0, .nat 2⟩]
#guard ((Run.open twice "session-A").play Rows.start).freshCall =
  some ⟨Api.root, 0, .external 0, .nat 2⟩

-- The claim a row carries is built from the machine, not written by the caller.
#guard Api.HostSession.Call.at ((Run.open twice "session-A").play Rows.start) ⟨Api.root, 0⟩ =
  some Test.Api.HostSessionContract.call0
#guard Api.HostSession.Call.at (Run.open twice "session-A") ⟨Api.root, 0⟩ = none
#guard Rows.answer (Run.open twice "session-A") ⟨Api.root, 0⟩ (.ofExit (.success (.nat 2))) = []

-- Without a host, the ordinary run parks on the first call and says so.
#guard (Run.runPure twice).exit = none
#guard (Run.runPure twice).phases = [.progressed, .progressed]
#guard (Run.runPure twice).observe.state = .awaitingAsync
#guard (Run.runPure twice).observe.awaiting = [⟨Api.root, 0, .external 0, .nat 2⟩]
#guard (Run.runPure twice).observe.reasons = [.awaitHost ⟨Api.root, 0⟩]

/-! ## A fork and an await -/

def opts : Supervision.ForkOptions :=
  { daemon := false, startImmediately := true, maskMode := .inherit }

/-- Two children, each parked on a host call, both awaited: the program of
`Test/Api/KeyedHostContract.lean`. -/
def pairProgram : Api.Program :=
  .bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 2))) opts))
    (.bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 3))) opts))
      (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))

def pairAdmitted : Api.AdmittedProgram pairProgram Test.Api.HostSessionContract.table where
  ty := ⟨.exitOf .nat (.prod .string .string), .never, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  internalFreeTable := by decide
  intFreeProgram := by decide
  intFreeType := by decide
  columnsTable := by decide +kernel
  columnsType := by decide +kernel

def pairUp : Api.Built :=
  { table := Test.Api.HostSessionContract.table
    program := pairProgram
    admitted := pairAdmitted
    rowNames := [("Host.wait", 0)] }

def forked : Run := (Run.runWith pairUp echo () (id := "multi")).1

-- The exit the hand-written battery pins, reached without naming a fiber or a token here.
#guard forked.exit = some (.success (Val.exitOk (.nat 3)))
#guard forked.phases =
  [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied, .progressed]
#guard forked.observe.state = .terminated
#guard forked.observe.applied = 2
#guard ((Run.open pairUp "multi").play forked.journal).exit = forked.exit

-- Both children are parked before either is answered, and the drive takes the first.
#guard ((Run.open pairUp "multi").play Rows.start).outstanding.map (fun a => (a.fiber, a.token)) =
  [(⟨1⟩, 0), (⟨2⟩, 1)]
#guard ((Run.open pairUp "multi").play Rows.start).freshCall.map (fun a => (a.fiber, a.token)) =
  some (⟨1⟩, 0)

-- Answering by key instead: the two receipts commute, which is `reply_commute`.
def started : Run := (Run.open pairUp "multi").play Rows.start
def byKey : Run :=
  (started.answer ⟨⟨2⟩, 1⟩ (.ofExit (.success (.nat 3)))).answer ⟨⟨1⟩, 0⟩
    (.ofExit (.success (.nat 2)))
#guard byKey.phases = [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied]
#guard (byKey.play Rows.flush).exit = some (.success (Val.exitOk (.nat 3)))

/-! ## The clock is the tape -/

-- The rows of a clocked run are the test clock's tape, written as control rows.
#guard Rows.tape (Api.TestClock.tape [5, 7]) =
  Rows.start ++ Rows.clock 5 ++ Rows.clock 7 ++ Rows.flush
#guard (Run.runClock twice [5]).journal = Rows.tape [Api.evaluate, .advance 5, Api.flush]
#guard (Run.runClock twice []).journal = (Run.runPure twice).journal

/-! ## Journaled controls agree with machine replay

Fixtures for `play_controls_eq_replay`: the convenience APIs keep the
same frame machine, including the nonempty table, independent budgets and pre-existing phases.
-/

example (s : Run) :
    (s.play (Rows.tape [])).machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel [] s.machine) := by
  apply Run.play_controls_eq_replay
  simp only [Rows.tape, List.map_nil, Run.play_nil, List.length_nil, List.replicate_zero,
    List.append_nil]

-- Ordinary and clock-driven runs on a nonempty table agree even while waiting for a host.
example : (Run.runPure twice).machine =
    (Api.run twice.program 1000 [] twice.table 1000).machine := by
  exact Run.runPure_eq_run twice "run" {} (by decide +kernel)

example : (Run.runClock twice [5]).machine =
    (Api.TestClock.run twice.program 1000 [5] [] twice.table 1000).machine := by
  exact Run.runClock_eq_run twice [5] "run" {} (by decide +kernel)

-- The child sleeps and returns a value; the parent awaits it. Compile and command budgets
-- deliberately differ, so neither connector may silently identify the two budgets.
def timedProgram : Api.Program :=
  .bind (.withFiber (.fork
    (.bind (.perform .sleep (.lit (.nat 5))) (.succeed (.lit (.nat 17)))) opts))
    (.awaitFiber (.var 0) .awaitValue)

def timedAdmitted : Api.AdmittedProgram timedProgram [] where
  ty := ⟨.exitOf .nat .never, .never, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  internalFreeTable := by decide
  intFreeProgram := by decide
  intFreeType := by decide
  columnsTable := by decide +kernel
  columnsType := by decide +kernel

def timed : Api.Built :=
  { table := [], program := timedProgram, admitted := timedAdmitted }

def clockBudget : Api.Budget := { compileFuel := 40, fuel := 1000 }

#guard (Run.runClock timed [4] (budget := clockBudget)).exit = none
#guard (Run.runClock timed [4, 1] (budget := clockBudget)).exit =
  some (.success (.exitOk (.nat 17)))
#guard (Run.runClock timed [4, 1] (budget := clockBudget)).phases =
  [.progressed, .progressed, .progressed, .progressed]

example : (Run.runClock timed [4, 1] (budget := clockBudget)).machine =
    (Api.TestClock.run timed.program clockBudget.fuel [4, 1] [] [] clockBudget.compileFuel).machine := by
  exact Run.runClock_eq_run timed [4, 1] "run" clockBudget (by decide +kernel)

-- Only the added phases must progress: an earlier refusal does not poison later controls.
def refusedHistory : Run :=
  (Run.open twice "prior-refusal").control (.answerAsync Api.root 0 (.ofExit (.success (.nat 2))))

#guard refusedHistory.phases = [.refused .directAnswer]
#guard (refusedHistory.play (Rows.tape [Api.evaluate, Api.flush])).phases =
  [.refused .directAnswer, .progressed, .progressed]

example : (refusedHistory.play (Rows.tape [Api.evaluate, Api.flush])).machine =
    Run.machineOf (Run.replayFrom refusedHistory.built.program refusedHistory.built.table
      refusedHistory.budget.fuel [Api.evaluate, Api.flush] refusedHistory.machine) := by
  exact Run.play_controls_eq_replay refusedHistory [Api.evaluate, Api.flush] (by decide +kernel)

-- Dropping the premise is false: the journal keeps playing after a fuel frontier, whereas
-- raw replay stops there. The later middleware control changes a machine field.
def noFuel : Run := Run.open twice "fuel-frontier" { compileFuel := 40, fuel := 0 }

#guard (noFuel.play (Rows.tape [Api.evaluate, .installMiddleware])).phases =
  [.frontier, .progressed]
#guard (noFuel.play (Rows.tape [Api.evaluate, .installMiddleware])).machine.middlewareInstalled
#guard !(Run.machineOf (Run.replayFrom noFuel.built.program noFuel.built.table
  noFuel.budget.fuel [Api.evaluate, .installMiddleware] noFuel.machine)).middlewareInstalled
#guard (noFuel.play (Rows.tape [Api.evaluate, .installMiddleware])).phases ≠
  noFuel.phases ++ List.replicate 2 Api.HostSession.Phase.progressed

/-! ## Recorded work and one opt-in control step -/

#guard (Run.open twice "work").work.runnable = [Api.root]
#guard (Run.open twice "work").nextControl = some Api.evaluate
#guard (Run.open twice "work").controlOnce.journal = Rows.start
#guard (Run.open twice "work").controlOnce.work.awaiting =
  (Run.open twice "work").controlOnce.outstanding
#guard (Run.open twice "work").controlOnce.nextControl = none

-- Yield parks the fiber while its dispatcher owns a queued resume. The new view exposes
-- this work without changing the existing protocol observation or frontier reasons.
def yieldingProgram : Api.Program := .bind (.yieldNow 0) (.succeed (.lit (.nat 23)))

def yieldingAdmitted : Api.AdmittedProgram yieldingProgram [] where
  ty := ⟨.nat, .never, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  internalFreeTable := by decide
  intFreeProgram := by decide
  intFreeType := by decide
  columnsTable := by decide +kernel
  columnsType := by decide +kernel

def yielding : Api.Built :=
  { table := [], program := yieldingProgram, admitted := yieldingAdmitted }

def yielded : Run := (Run.open yielding "yielded").controlOnce

#guard yielded.observe.state = .parked
#guard yielded.work.runnable = []
#guard yielded.observe.reasons = []
#guard yielded.work.queued = [Api.root]
#guard yielded.nextControl = some Api.flush
#guard yielded.controlOnce.exit = some (.success (.nat 23))
#guard yielded.controlOnce.journal = Rows.start ++ Rows.flush

-- An outstanding host call does not hide an independent queued child continuation.
def mixedWorkProgram : Api.Program :=
  .bind (.withFiber (.fork yieldingProgram opts))
    (.perform (.external 0) (.lit (.nat 2)))

def mixedWorkAdmitted : Api.AdmittedProgram mixedWorkProgram Test.Api.HostSessionContract.table where
  ty := ⟨.nat, .prod .string .string, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  internalFreeTable := by decide
  intFreeProgram := by decide
  intFreeType := by decide
  columnsTable := by decide +kernel
  columnsType := by decide +kernel

def mixedWorkBuilt : Api.Built :=
  { table := Test.Api.HostSessionContract.table, program := mixedWorkProgram,
    admitted := mixedWorkAdmitted }

def mixedWork : Run := (Run.open mixedWorkBuilt "mixed-work").controlOnce

#guard mixedWork.observe.state = .awaitingAsync
#guard !mixedWork.work.awaiting.isEmpty
#guard !mixedWork.work.queued.isEmpty
#guard mixedWork.nextControl = some Api.flush
#guard mixedWork.controlOnce.work.queued = []
#guard mixedWork.controlOnce.outstanding = mixedWork.outstanding

-- Inspection reports pending replies and timers. The internal planner does not apply
-- replies or advance time on the caller's behalf.
def pendingWork : Run :=
  ((Run.open twice "pending-work").controlOnce).receive ⟨Api.root, 0⟩ (.ofExit (.success (.nat 2)))

#guard pendingWork.work.pending = [⟨Api.root, 0⟩]
#guard pendingWork.nextControl = none
#guard pendingWork.controlOnce.journal = pendingWork.journal
#guard (Run.open timed "timer-work").controlOnce.work.timers = [(⟨1⟩, 5)]
#guard (Run.open timed "timer-work").controlOnce.nextControl = none

-- Choosing a control is not a progress certificate: zero command fuel records a frontier.
#guard noFuel.nextControl = some Api.evaluate
#guard noFuel.controlOnce.phases = [.frontier]

-- The empty-choice case on a stuck machine is deliberate even if other fields contain work.
def stoppedWork : Run :=
  let s := Run.open twice "stopped-work"
  { s with session := { s.session with machine :=
    { s.machine with stuck := some (.unknownFiber Api.root), armed := [Api.root] } } }

#guard stoppedWork.nextControl = none
#guard stoppedWork.controlOnce.journal = []

example (s : Run) (decision : Api.Decision) (chosen : s.nextControl = some decision) :
    s.controlOnce.journal = s.journal ++ [.control decision] :=
  Run.controlOnce_journal s decision chosen

/-! ## One completion per call

Once an answer has been applied the machine holds no call at that key, so a second answer
has no rows at all. -/

#guard Rows.answer driven ⟨Api.root, 0⟩ (.ofExit (.success (.nat 2))) = []
#guard Api.HostSession.Call.at driven ⟨Api.root, 0⟩ = none
#guard (driven.answer ⟨Api.root, 0⟩ (.ofExit (.success (.nat 2)))).journal = driven.journal

/-! ## The ceilings -/

/-- info: 'Effect4.Run.journal_replays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.journal_replays
/-- info: 'Effect4.Run.drive_eq_play' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.drive_eq_play
/-- info: 'Effect4.Run.drive_envelope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.drive_envelope
/-- info: 'Effect4.Run.answer_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.answer_accepted
/-- info: 'Effect4.Run.open_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.open_total
/-- info: 'Effect4.Run.bindCall_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.bindCall_at
/-- info: 'Effect4.Run.answer_once' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.answer_once
/-- info: 'Effect4.Run.runPure_eq_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.runPure_eq_run
/-- info: 'Effect4.Run.play_phases_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.play_phases_extend
/-- info: 'Effect4.Run.play_controls_eq_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.play_controls_eq_replay
/-- info: 'Effect4.Run.runClock_eq_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.runClock_eq_run
/-- info: 'Effect4.Run.nextControl_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.nextControl_spec
/-- info: 'Effect4.Run.nextControl_evaluate_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.nextControl_evaluate_mem
/-- info: 'Effect4.Run.controlOnce_journal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.controlOnce_journal
/-- info: 'Effect4.Run.admitProgram_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Run.admitProgram_certificate

#check @Effect4.Run.receive_rows
#check @Effect4.Run.answer_rows
#check @Effect4.Run.acceptReply_after_applied

end Test.Run.RunContract
