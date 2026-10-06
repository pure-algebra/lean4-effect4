import Effect4.Run

/-!
# Run.Tape — what a tool reads off a run: the machine's view, and the decision of a row

A `Run` holds a checked session, and the session holds the machine (`src/Effect4/Run.lean`).
This module holds the readings of a run that a tool may call. Each is an executable definition
over the run API, and none needs a law.

* **The machine's view.** `MachineView` is the machine's part of an observation: what a replay
  of the machine alone can show. `machineViewOf` reads it from a machine, and `machineView`
  reads it from a run.
* **The decision of a row.** `decisionOf` reads the decision that a journal row gives the
  machine, on the run before the row. `replyDecision` is the answer decision of a stored reply.
  A `Position` holds one such decision, with the run after its row.
* **A receipt row.** `receiptRow` tells a row that holds a call or receives a reply. Such a
  row gives the machine no decision.
* **The fresh open, and rest.** `openedOf` is the run that a run started from. `atRest` tells
  a machine that names no runnable fiber and no armed owner.

The tape itself is not here. `tapeFrom` asks `Run.enoughFor` of each decision, through
`readsOn`, and the law graph defines that function (`src/Effect4/Laws/Run.lean`). The `Effect4`
root never imports the law graph. So `readsOn`, `tapeFrom`, `tapeOf` and `funded` stand in
`src/Effect4/Laws/Run/Tape.lean`, with the tape's laws.

The definitions came from the scenario support (`Test/Dogfood/Scenario.lean`), each with its
body unchanged (decisions row 284, point 5). This file is no `module` file: it imports
`Effect4.Run`, an importer of the specialization sites of decisions row 202.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## The machine's part of a run -/

/-- The machine's part of an observation: what a replay of the machine alone can show. The held
calls, the reply receipts, the retired calls and the stored replies are the session's, and no
part of them is here. -/
structure MachineView where
  /-- The root's exit, or `none` while it is live. -/
  rootExit : Option ExitV
  /-- The cells, in allocation order. -/
  cells : List Val
  /-- The calls the machine waits on. -/
  awaiting : List Await
  /-- The armed owners, in arming order. -/
  queued : List FiberId
  /-- The runnable fibers, in the machine's order. -/
  runnable : List FiberId
  /-- Each sleeping fiber with the clock reading it wakes at. -/
  timers : List (FiberId × ClockMillis)
deriving DecidableEq

/-- The machine's part of an observation, read from a machine. -/
def machineViewOf (m : Api.Machine) : MachineView :=
  { rootExit := (m.fiber? Api.root).bind RunFiber.exit
    cells := m.state.refs
    awaiting := awaits m
    queued := m.armed
    runnable := Api.runnableFibers m
    timers := m.state.timers.wake.waiters.map fun w => (w.fiber, w.payload) }

/-- The machine's part of a run's observation. -/
def machineView (s : Run) : MachineView := machineViewOf s.machine

/-! ## The decision of a row -/

/-- One position of a machine tape: the decision that moved the machine, and the run after the
row that gave it. -/
structure Position where
  decision : Api.Decision
  after : Run

/-- The answer decision of a stored reply, at the reply's own key. It is the decision that the
session hands the machine when it applies the reply: the session's preflight finds the call by
the reply's key, never by the key of the slot (`preflight_replyDecision`,
`src/Effect4/Laws/Run/Tape.lean`). `storeReply` writes a reply only into the slot of its own
key. -/
def replyDecision (reply : Reply) : Api.Decision :=
  .answerAsync reply.key.fiber reply.key.token reply.completion

/-- The decision a row gives the machine, read on the run before the row. `none` for a row that
leaves the machine as it was: a held call, a reply receipt, a refused row. A reply application
gives the answer decision of the stored reply (`replyDecision`). -/
def decisionOf (s : Run) (c : Command) (phase : Phase) : Option Api.Decision :=
  match c, phase with
  | .control decision, .progressed => some decision
  | .apply key, .applied => (Api.HostSession.readReply s.session.pending key).map replyDecision
  | _, _ => none

/-- A row that holds a call or receives a reply. -/
def receiptRow : Command → Bool
  | .bind _ _ => true
  | .submit _ => true
  | _ => false

/-! ## The fresh open, and a machine at rest -/

/-- The run that a run started from: its own program, name, budgets and profile, opened fresh.
Playing a recorded run's journal from it reaches the run again (`Run.journal_replays`,
`src/Effect4/Laws/Run.lean`). -/
def openedOf (s : Run) : Run := Run.open s.built s.id s.budget s.profile

/-- **A machine at rest**: it names no runnable fiber and no armed owner. A host lets every
dispatcher run after each of its acts but the root's start, so a host reads a machine at rest
(`performable`, `harness/truth/session/Keyed.lean`).

Rest does not show that a run is funded. A budget may cut a step and leave its fiber runnable
with no task: that run is not at rest. A budget may also cut a step and leave no fiber runnable,
while the root has no exit: that run is at rest, and the commands that the step left are gone.
The battery `Test/Dogfood/Scenario/QueueWorkers.lean` holds one run of each kind, `starved` and
`dropped`. So a statement at rest takes `funded` (`src/Effect4/Laws/Run/Tape.lean`) beside
`atRest`. -/
def atRest (s : Run) : Bool := s.work.runnable.isEmpty && s.work.queued.isEmpty

end Effect4.Run
