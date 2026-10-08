import Effect4.Run.Basic

/-!
# Run.Tape — what a tool reads off a run: the machine's view, the raw replay, and the tape

A `Run` holds a checked session, and the session holds the machine (`src/Effect4/Run/Basic.lean`).
This module holds the readings of a run that a tool may call. Each is an executable definition
over the run API, under the `Effect4` root. So a tool that inspects a recorded run needs no
import of the law graph. The laws of these definitions stand there
(`src/Effect4/Laws/Run.lean`, `src/Effect4/Laws/Run/Rows.lean`, `src/Effect4/Laws/Run/Tape.lean`).

* **The machine's view.** `MachineView` is the machine's part of an observation: what a replay
  of the machine alone can show. `machineViewOf` reads it from a machine, and `machineView`
  reads it from a run.
* **The decision of a row.** `decisionOf` reads the decision that a journal row gives the
  machine, on the run before the row. `replyDecision` is the answer decision of a stored reply.
  A `Position` holds one such decision, with the run after its row.
* **A receipt row.** `receiptRow` tells a row that holds a call or receives a reply. Such a
  row gives the machine no decision.
* **The raw replay.** `replayFrom` replays a decision tape from a machine, at the program's own
  evaluator. `machineOf` reads the machine that a replay reached. `enoughFor` tells whether one
  decision had enough command fuel.
* **The tape.** `tapeFrom` reads the decisions that moved the machine off a journal: each
  control that progressed and each reply application. It stops at the first row that ends at a
  frontier, and at the first decision that the raw replay does not read past (`readsOn`).
  `tapeOf` is the tape of a run's own journal, read from the run's fresh open (`openedOf`).
* **A funded run, and rest.** `funded` tells a run whose tape leaves no row unread. `atRest`
  tells a machine that names no runnable fiber and no armed owner.

Each definition came here with its body unchanged (decisions row 284, point 5). `machineOf`,
`replayFrom` and `enoughFor` stood in `src/Effect4/Laws/Run.lean`, where their laws still
stand. The others stood in the scenario support (`Test/Dogfood/Scenario.lean`).

This file is no `module` file. It imports `Effect4.Run.Basic`, an importer of the specialization
sites of decisions row 202. `replayFrom` and `enoughFor` take the machine's functions at a
program's own interpreter, as those sites do.
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

/-! ## The raw replay of a decision tape

The laws of these three definitions stand in `src/Effect4/Laws/Run.lean`: `replay_machine`,
`machineOf_nil`, `replayFrom_cons`, `advance_step` and `play_controls_eq_replay`. -/

/-- The machine a replay reached, whichever way it ended. -/
def machineOf : NativeReplay → Api.Machine
  | .finished m => m
  | .frontier _ m => m
  | .stuck _ m => m

/-- A decision tape replayed from a machine, at the program's own evaluator. -/
def replayFrom (program : Api.Program) (table : RowTable) (fuel : Nat)
    (tape : List Api.Decision) (m : Api.Machine) : NativeReplay :=
  letI := evaluatorFor program table
  replayEval (interpOf program table) fuel tape m

/-- Whether one decision had enough command fuel, at the program's own evaluator. -/
def enoughFor (program : Api.Program) (table : RowTable) (fuel : Nat) (m : Api.Machine)
    (d : Api.Decision) : Bool :=
  letI := evaluatorFor program table
  (stepDecisionState (interpOf program table) fuel m d).2

/-! ## The tape of a journal

The laws of the tape stand in `src/Effect4/Laws/Run/Tape.lean`: `tape_replays`, the four laws of
the journal's cut, and `funded_replays`. -/

/-- Whether the raw replay takes this decision and reads on: the machine is live, and the step
has enough command fuel (`enoughFor`). -/
def readsOn (s : Run) (decision : Api.Decision) : Bool :=
  s.machine.stuck.isNone &&
    Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision

/-- The machine tape of rows played from a run: the positions, and the rows left unread. The
tape stops at the first row that ends at a frontier, and at the first decision the raw replay
does not read past. A frontier is never turned into a reply application: its rows stay unread. -/
def tapeFrom (s : Run) : List Command → List Position × List Command
  | [] => ([], [])
  | c :: rest =>
    let phase := (Api.Runner.result s.runner c).phase
    if phase == .frontier then ([], c :: rest)
    else
      match decisionOf s c phase with
      | none =>
        let tail := tapeFrom (s.step c) rest
        (tail.1, tail.2)
      | some decision =>
        if readsOn s decision then
          let tail := tapeFrom (s.step c) rest
          (⟨decision, s.step c⟩ :: tail.1, tail.2)
        else ([], c :: rest)

/-! ## The fresh open, a funded run, and a machine at rest -/

/-- The run that a run started from: its own program, name, budgets and profile, opened fresh.
Playing a recorded run's journal from it reaches the run again (`Run.journal_replays`,
`src/Effect4/Laws/Run.lean`). -/
def openedOf (s : Run) : Run := Run.open s.built s.id s.budget s.profile

/-- The decisions of a run's tape: the decisions that moved the machine, read off the run's own
journal from its fresh open. -/
def tapeOf (s : Run) : List Api.Decision := (tapeFrom (openedOf s) s.journal).1.map (·.decision)

/-- **A funded run: no task of the run was cut by its budget.** The tape of the run's own
journal, read from the run's fresh open, leaves no row unread. So the journal holds no stopped
row: no row ends at a frontier, and each decision is taken at a live machine with enough command
fuel (`tapeFrom`, `readsOn`).

The journal's verdicts alone do not decide it. A reply application has the verdict `applied` as
soon as its call's guard is gone, whatever fuel its step had left (`applyReply`,
`src/Effect4/Api/HostSession.lean`). Only a control reports its sufficiency, as `progressed` or
`frontier` (`advance`, in the same file). The tape asks `Run.enoughFor` of each decision, so it
stops at an applied reply application that the budget cut (`tapeFrom_stop`,
`src/Effect4/Laws/Run/Tape.lean`).

It is the budget premise of a law of a whole run. Decisions row 226 excludes a cut inside an
owned operation from the first profile. The proposed claim `embedded-budget-sufficient` (an open
part of R12) is to supply the premise from a program's own bound. Until then a statement over
runs takes it by this one name. `funded_replays`, in the same law module, says what the premise
gives. -/
def funded (s : Run) : Bool := (tapeFrom (openedOf s) s.journal).2.isEmpty

/-- **A machine at rest**: it names no runnable fiber and no armed owner. A host lets every
dispatcher run after each of its acts but the root's start, so a host reads a machine at rest
(`performable`, `harness/truth/session/Keyed.lean`).

Rest does not show that a run is funded. A budget may cut a step and leave its fiber runnable
with no task: that run is not at rest. A budget may also cut a step and leave no fiber runnable,
while the root has no exit: that run is at rest, and the commands that the step left are gone.
The battery `Test/Dogfood/Scenario/QueueWorkers.lean` holds one run of each kind, `starved` and
`dropped`. So a statement at rest takes `funded` beside `atRest`. -/
def atRest (s : Run) : Bool := s.work.runnable.isEmpty && s.work.queued.isEmpty

end Effect4.Run
