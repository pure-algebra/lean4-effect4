import Test.Dogfood.Scenario.TapeData
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout
import Test.Dogfood.Scenario.Todo.Claims
import Test.Audit.ScenarioGate

/-!
# Controls of the scenario machine tapes

Decisions row 254 asks that a scenario's observation be compared on the generated OCaml engine.
The engine holds no session: no stored reply, no retired call, no consumed call. So a scenario's
observation lands as two clauses. The session clause is the whole observation, checked in each
scenario's battery. The machine clause is `machineView` (`src/Effect4/Run/Tape.lean`): the
root's exit, the cells, the calls the machine waits on, the armed owners, the runnable fibers and
the timers.

`Test/Dogfood/Scenario/TapeData.lean` owns the fixture text and named runs. The writer imports that data module.
This module owns the journal-cut reader and its controls.
`Test/Dogfood/Scenario/Lowered.lean` binds the committed files to the generated text.

* **A lowered run.** `Lowered`: a built program opened for a run, and a script. Its machine tape
  is `tapeFrom` on the journal the script leaves. The tape holds each control that progressed and
  each reply application. A held call, a reply receipt and a refused row give no decision.
* **The fixture.** `text`: the program's canonical bytes, each row's canonical bytes, the budgets,
  then each decision with the machine view after it. A value is its canonical bytes in
  hexadecimal (`Val.encode`), and an exit is the value `reifyExitVal` gives it.
* **The runs.** `fixtures`: each fixture file's name, with the lowered runs of its scenario. A
  run with the name of a record's run is that named run: `taken` lists the names, and the lane
  writes no script of them. The lane's own runs are the two of `own`. An own run with the name
  of a record's run is refused (`findings`), so one name has one script on every lane.
* **The journal's cut.** `shown_views_opened`: at a fresh open, the raw replay of each prefix of
  a lowered run's tape shows the session machine's view at that position. It is the consumer of
  the laws of the journal's cut. The record `cuts` holds the controls of those laws, on
  two journals of the crew that stop at a row. Its gate, at the module's foot, plays them on the
  Lean machine.

To write the fixtures again after a change, follow the steps of `Test/Dogfood/README.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Lowered

open Effect4 Effect4.Machine Effect4.Program

/-! ## 4. The journal's cut on a lowered run

The laws of the journal's cut (`src/Effect4/Laws/Run/Tape.lean`) say what a prefix of a
journal gives: its completed prefix and each position of its tape replay raw. This section
holds their consumer and their controls.

* **The consumer.** `shown_views_opened`: the views that `Lowered.shown` computes, at a fresh
  open.
* **The record.** `cuts`: the consumer is its claim, and the position law is the clause that
  the claim's proof uses. The cut's replay law and the append law stand beside it with controls
  only. Each of the four has a green control and a red control.
* **The runs.** Two scripts of the workers record, opened again at a small command budget
  (`cutBudget`). One journal stops at a reply application that the raw replay does not read
  past, and the other at a frontier row.

The gate at the foot plays those two journals on the Lean machine, and it reads no fixture. -/

/-- **The raw replay shows the session machine at every position of a lowered run.** When a
lowered run opens its program fresh (`Run.open`), the views of the raw frame replay are the
session machine's views: the opened machine first, then the machine after each position of the
tape. The tape may leave rows unread: a stopped row adds a position to neither list. Reach: any
built program, name, budgets, profile and script. The fresh open is a premise, because
`Lowered.shown` replays each prefix from a new load (`Api.replay`). The proof uses the premise
once, for the opened machine (`Run.open_machine`). It does not establish `Shown.agrees`, which
also asks for a tape that reads every row. It says nothing of the replay's outcome words, of
`observedTableDifference`, of a session ledger or of a lowered engine: the engine's link stays
the finite comparison of `ocaml/engine/test/scenarios/test_scenarios.ml`. Concept
`translation-simulation`, R8: the replay view of `tape_replays`, at every position, for a tape
that may stop. It is `tapeFrom_position_replays` (`src/Effect4/Laws/Run/Tape.lean`) at each
position. Consumer: the lowered runs of `fixtures`, each of which opens its program fresh, and
the record `cuts` below. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem shown_views_opened (l : Lowered) (b : Api.Built) (id : String) (budget : Api.Budget)
    (profile : String) (fresh : l.opened = Run.open b id budget profile) :
    l.shown.raw.map (·.2) = l.shown.views := by
  have loaded : l.opened.machine =
      Api.load l.opened.built.program l.opened.budget.compileFuel := by
    rw [fresh]
    exact Run.open_machine b id budget profile
  have raw : ∀ taken : List Api.Decision,
      (Api.replay l.opened.built.program l.opened.budget.fuel taken l.opened.built.table
        l.opened.budget.compileFuel).machine =
      Run.machineOf (Run.replayFrom l.opened.built.program l.opened.built.table
        l.opened.budget.fuel taken l.opened.machine) := by
    intro taken
    rw [Run.replay_machine, loaded]
  have position : ∀ (i : Nat) (position : Position),
      (tapeFrom l.opened (Scenario.play l.opened l.moves).journal).1[i]? = some position →
      Run.machineOf (Run.replayFrom l.opened.built.program l.opened.built.table
        l.opened.budget.fuel
        (((tapeFrom l.opened (Scenario.play l.opened l.moves).journal).1.map (·.decision)).take
          (i + 1)) l.opened.machine) = position.after.machine := by
    intro i position found
    rw [← List.map_take]
    exact (tapeFrom_position_replays l.opened _ i position found).symm
  dsimp only [Lowered.shown]
  rw [List.map_map, List.map_map, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · exact congrArg machineViewOf ((raw _).trans (Run.machineOf_nil _ _ _ _))
  · apply List.ext_getElem
    · rw [List.length_map, List.length_range, List.length_map, List.length_map]
    · intro i inRange inTape
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      exact congrArg machineViewOf
        ((raw _).trans (position i _ (List.getElem?_eq_getElem _)))

/-! ### The runs and the controls

Each control is a finite probe: one journal on the Lean machine. A control compares
`machineView`, or a tape's decisions and its unread rows. -/

/-- The budgets of the cut's two runs. The command budget, 60, is small on purpose. On the crew
it covers the start, the flush and every reply application of the script `lowest` but the last.
It does not cover that last one, which closes the pool, or the cancellation of the root. So
each of the two journals stops at one row. When a change of the crew or of the machine moves
one of those costs past this budget, a green control fails by its shape test, and the budget is
pinned again. -/
def cutBudget : Api.Budget := { fuel := 60, compileFuel := 2000 }

/-- The cut's named runs: two scripts of the workers record, each opened again at the cut's
budget (`cutBudget`), under the record's own name and profile. The record writes no script.

* **`stopped`** plays the script `lowest`. Its journal stops at its last row, a reply
  application that the session applies and the raw replay does not read past: the stop of
  `tapeFrom_stop`. Five positions stand before that row.
* **`frontier`** plays the script `cancelled-root`. Its journal stops at its last row, the
  root's cancellation, which ends at a frontier: the stop of `tapeFrom_frontier`. Two positions
  and two held calls stand before that row. -/
def cutRuns : List NamedRun :=
  [("stopped", "lowest"), ("frontier", "cancelled-root")].filterMap fun (name, script) =>
    (Workers.scenario.run? script).map fun run =>
      ⟨name, Run.open run.opened.built run.opened.id cutBudget run.opened.profile, run.moves⟩

/-- The completed prefix of a journal read from a run: its rows before the tape's unread rows.
It is the prefix of `tapeFrom_cut`. -/
def completedPrefix (s : Run) (rows : List Api.Runner.Command) : List Api.Runner.Command :=
  rows.take (rows.length - (tapeFrom s rows).2.length)

/-- The view that the raw frame replay shows on the decisions of some positions, from a run's
own machine, at the run's table and budgets: the right side of `tapeFrom_cut_replays`. -/
def replayView (s : Run) (positions : List Position) : MachineView :=
  machineViewOf (Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
    (positions.map (·.decision)) s.machine))

/-- What a control reads of a tape's positions: each decision, with the machine's view after it.
A control never compares two positions whole, because a position holds a run. -/
def readings (positions : List Position) : List (Api.Decision × MachineView) :=
  positions.map fun position => (position.decision, machineView position.after)

/-- Whether a journal's cut shows what `tapeFrom_cut_replays` states, on the machine's view. The
journal is the completed prefix, then the unread rows. The tape of the prefix alone shows the
same positions and leaves no row unread. The machine after the prefix shows the raw replay of
the positions' decisions. -/
def cutShows (s : Run) (rows : List Api.Runner.Command) : Bool :=
  let tape := tapeFrom s rows
  let done := completedPrefix s rows
  let alone := tapeFrom s done
  done ++ tape.2 == rows && alone.2.isEmpty && readings alone.1 == readings tape.1 &&
    machineView (s.play done) == replayView s tape.1

/-- Whether each position of a journal's tape shows what `tapeFrom_position_replays` states, on
the machine's view. The machine after position `i` shows the raw replay of the first `i + 1`
decisions, from the machine of the run that the tape was read from. -/
def positionsShow (s : Run) (rows : List Api.Runner.Command) : Bool :=
  let positions := (tapeFrom s rows).1
  (List.range positions.length).all fun at_ =>
    (positions[at_]?).any fun position =>
      machineView position.after == replayView s (positions.take (at_ + 1))

/-- How the stopped row of a journal ends: the verdict of the first unread row, on the run after
the completed prefix. `none` for a tape that reads every row. -/
def stopOf (s : Run) (rows : List Api.Runner.Command) : Option Api.HostSession.Phase :=
  (tapeFrom s rows).2.head?.map fun row =>
    (Api.Runner.result (s.play (completedPrefix s rows)).runner row).phase

/-- The machine's view after the stopped row of a journal: the completed prefix and the first
unread row, played. No law of the journal's cut says what that machine is. -/
def stoppedView (s : Run) (rows : List Api.Runner.Command) : MachineView :=
  machineView (s.play (completedPrefix s rows ++ (tapeFrom s rows).2.take 1))

/-- Whether the tape of a journal in two parts shows what `tapeFrom_append` states, on the
positions' readings and the unread rows. -/
def appendShows (s : Run) (a b : List Api.Runner.Command) : Bool :=
  let whole := tapeFrom s (a ++ b)
  let first := tapeFrom s a
  let second := tapeFrom (s.play a) b
  if first.2.isEmpty then
    readings whole.1 == readings first.1 ++ readings second.1 && whole.2 == second.2
  else readings whole.1 == readings first.1 && whole.2 == first.2 ++ b

/-- The lowered run of a named run of the cut's record, under its quoted name. `none` for a name
that the record does not list. -/
def cutLowered (name : String) : Option Lowered :=
  (cutRuns.find? (·.name == name)).map fun run => ⟨"cuts/" ++ name, run.opened, run.moves⟩

/-- The controls of the journal's cut. A control of a journal reads its named run as the gate
plays it. It takes the opened run and the rows from that run alone: `openedOf`
(`src/Effect4/Run/Tape.lean`), and the run's journal. The two controls of the lowered run's
views read no run: `Lowered.shown` plays the script itself.

* **`views`.** On the journal `stopped` the raw replay shows the session machine at every
  position of the lowered run, and one row stays unread. The red control drops the fresh open:
  from a run that has started, the raw replay of a new load shows another opened machine.
* **`position`.** The journal `stopped` is read again from the run after its first two rows.
  Each position's machine shows the raw replay of the decisions up to it, from that run's own
  machine: the law asks for no fresh open. The red control replays one decision fewer, and it
  shows another machine at every position.
* **`cut`.** On each journal the completed prefix ends before the stopped row, and its machine
  shows the raw replay of the positions' decisions. The red controls take the stopped row's own
  machine for that replay's result: it shows another view.
* **`append`.** Split at each row, the tape of the journal `stopped` is the tape of its first
  part, then the tape of the rest. The red control reads on after the stopped row: a flush from
  that row's own machine would give a position, and the journal's tape holds none for it. -/
def cutControls : List Control :=
  [ -- the raw replay shows the session machine at every position of a lowered run
    green "views"
      "at every position of a tape that leaves a row unread, the raw replay shows the session machine"
      [] fun _ =>
        (cutLowered "stopped").any fun l =>
          let x := l.shown
          x.raw.map (·.2) == x.views && x.positions.length == 5 && x.left == 1 && !x.agrees
  , red "views"
      "from a run that has started, the raw replay of a new load shows another opened machine"
      [] fun _ =>
        (cutLowered "stopped").any fun l =>
          let x := Lowered.shown { l with opened := l.opened.play Rows.start }
          x.raw.map (·.2) != x.views
    -- the machine after a position is the raw replay of the decisions up to it
  , green "position"
      "read from a run that has started, each position replays raw from that run's own machine"
      ["stopped"] fun
      | [played] =>
        let s := (openedOf played).play (played.journal.take 2)
        let rows := played.journal.drop 2
        positionsShow s rows && (tapeFrom s rows).1.length == 3 && (tapeFrom s rows).2.length == 1
      | _ => false
  , red "position" "the raw replay of one decision fewer shows another machine, at every position"
      ["stopped"] fun
      | [played] =>
        let s := openedOf played
        let positions := (tapeFrom s played.journal).1
        positions.length == 5 &&
          (List.range positions.length).all fun at_ =>
            (positions[at_]?).any fun position =>
              machineView position.after != replayView s (positions.take at_)
      | _ => false
    -- the machine after the completed prefix is the raw replay of its tape
  , green "cut"
      "a journal that stops at an applied reply: the completed prefix ends before it and replays raw"
      ["stopped"] fun
      | [played] =>
        let s := openedOf played
        cutShows s played.journal && (tapeFrom s played.journal).1.length == 5 &&
          (completedPrefix s played.journal).length + 1 == played.journal.length &&
          stopOf s played.journal == some .applied
      | _ => false
  , green "cut"
      "a journal that stops at a frontier row: the completed prefix ends before it, after two held calls"
      ["frontier"] fun
      | [played] =>
        let s := openedOf played
        cutShows s played.journal && (tapeFrom s played.journal).1.length == 2 &&
          (completedPrefix s played.journal).length == 4 && played.journal.length == 5 &&
          stopOf s played.journal == some .frontier
      | _ => false
  , red "cut" "the stopped row's own machine is not the raw replay of the completed prefix's tape"
      ["stopped"] fun
      | [played] =>
        let s := openedOf played
        stoppedView s played.journal != replayView s (tapeFrom s played.journal).1
      | _ => false
  , red "cut" "the frontier row's own machine is not the raw replay of the completed prefix's tape"
      ["frontier"] fun
      | [played] =>
        let s := openedOf played
        stoppedView s played.journal != replayView s (tapeFrom s played.journal).1
      | _ => false
    -- the tape of a journal in two parts
  , green "append"
      "split at each row, a journal's tape is the tape of its first part, then of the rest"
      ["stopped"] fun
      | [played] =>
        (List.range (played.journal.length + 1)).all fun at_ =>
          appendShows (openedOf played) (played.journal.take at_) (played.journal.drop at_)
      | _ => false
  , red "append"
      "a flush after the stopped row is not read, though the stopped row's own machine would read it"
      ["stopped"] fun
      | [played] =>
        let s := openedOf played
        let flush : List Api.Runner.Command := [.control Api.flush]
        appendShows s played.journal flush &&
          (tapeFrom s (played.journal ++ flush)).1.length == (tapeFrom s played.journal).1.length &&
          (tapeFrom played flush).1.length == 1
      | _ => false ]

/-- The journal's cut as a scenario. Its claim is `shown_views_opened`, the views of a lowered
run at a fresh open. The claim stands as its own clause, `views`, and its proof uses the
position law, the clause `position`. The cut's replay law and the append law are associated
laws: the record claims no dependency of the claim on them. The program is the crew, and the
observation is the machine's view. -/
def cuts : Scenario :=
  { name := "cuts"
    program := ``Workers.crew
    observation := ``machineView
    claim := ``shown_views_opened
    clauses := [⟨"views", ``shown_views_opened⟩, ⟨"position", ``tapeFrom_position_replays⟩]
    laws := [⟨"cut", ``tapeFrom_cut_replays⟩, ⟨"append", ``tapeFrom_append⟩]
    runs := cutRuns
    controls := cutControls }

/-- Red control of the shape tests: the same record on the same two scripts at the workers' own
budgets, where no journal stops. The gate must refuse every control that reads a journal for
its stop. The green control of the append law still passes: that law holds at every split of
any journal. The two controls of the views read no named run, so they pass too. -/
def unstopped : Scenario :=
  { cuts with
    name := "cuts on journals that do not stop"
    runs := cutRuns.map fun run =>
      { run with
        opened := Run.open run.opened.built run.opened.id Workers.budget run.opened.profile } }

-- One run of the gate over both records. The green control is that no finding names `cuts`.
-- The red control names each control that a journal with no stopped row fails.
/--
error: cuts on journals that do not stop: the control "read from a run that has started, each position replays raw from that run's own machine" fails
cuts on journals that do not stop: the control "the raw replay of one decision fewer shows another machine, at every position" fails
cuts on journals that do not stop: the control "a journal that stops at an applied reply: the completed prefix ends before it and replays raw" fails
cuts on journals that do not stop: the control "a journal that stops at a frontier row: the completed prefix ends before it, after two held calls" fails
cuts on journals that do not stop: the control "the stopped row's own machine is not the raw replay of the completed prefix's tape" fails
cuts on journals that do not stop: the control "the frontier row's own machine is not the raw replay of the completed prefix's tape" fails
cuts on journals that do not stop: the control "a flush after the stopped row is not read, though the stopped row's own machine would read it" fails
-/
#guard_msgs (error) in
#scenario_gate cuts unstopped

end Test.Dogfood.Scenario.Lowered
