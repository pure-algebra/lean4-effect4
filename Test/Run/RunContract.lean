import Effect4.Run
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
  [(Api.root, 0, .external 0, .nat 2)]
#guard ((Run.open twice "session-A").play Rows.start).freshCall =
  some (Api.root, 0, .external 0, .nat 2)

-- The claim a row carries is built from the machine, not written by the caller.
#guard Api.HostSession.Call.at ((Run.open twice "session-A").play Rows.start) ⟨Api.root, 0⟩ =
  some Test.Api.HostSessionContract.call0
#guard Api.HostSession.Call.at (Run.open twice "session-A") ⟨Api.root, 0⟩ = none
#guard Rows.answer (Run.open twice "session-A") ⟨Api.root, 0⟩ (.ofExit (.success (.nat 2))) = []

-- Without a host, the ordinary run parks on the first call and says so.
#guard (Run.runPure twice).exit = none
#guard (Run.runPure twice).phases = [.progressed, .progressed]
#guard (Run.runPure twice).observe.state = .awaitingAsync
#guard (Run.runPure twice).observe.awaiting = [(Api.root, 0, .external 0, .nat 2)]
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
  intFreeProgram := by decide
  intFreeType := by decide

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
#guard ((Run.open pairUp "multi").play Rows.start).outstanding.map (fun a => (a.1, a.2.1)) =
  [(⟨1⟩, 0), (⟨2⟩, 1)]
#guard ((Run.open pairUp "multi").play Rows.start).freshCall.map (fun a => (a.1, a.2.1)) =
  some (⟨1⟩, 0)

-- Answering by key instead: the two receipts commute, which is `reply_commute`.
def started : Run := (Run.open pairUp "multi").play Rows.start
def byKey : Run :=
  (started.answer ⟨⟨2⟩, 1⟩ (.ofExit (.success (.nat 3)))).answer ⟨⟨1⟩, 0⟩
    (.ofExit (.success (.nat 2)))
#guard byKey.phases = [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied]
#guard (byKey.play Rows.flush).exit = some (.success (Val.exitOk (.nat 3)))

end Test.Run.RunContract
