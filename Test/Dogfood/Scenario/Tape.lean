import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout

/-!
# The machine tapes of the scenarios, and the fixture text Lean writes for the engine

Decisions row 254 asks that a scenario's observation be compared on the generated OCaml engine.
The engine holds no session: no stored reply, no retired call, no consumed call. So a scenario's
observation lands as two clauses. The session clause is the whole observation, checked in each
scenario's battery. The machine clause is `machineView` (`Test/Dogfood/Scenario.lean`): the
root's exit, the cells, the calls the machine waits on, the armed owners, the runnable fibers and
the timers.

This module holds what Lean writes for the machine clause. Sections 1 to 3 have no control and
no gate, and no line of the module reads a committed fixture. So it builds whatever the
committed fixtures hold. The writer imports it. The battery
`Test/Dogfood/Scenario/Lowered.lean` binds the committed files to its text.

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
  the driver's laws of the journal's cut. The record `cuts` holds the controls of those laws, on
  two journals of the crew that stop at a row. Its gate, at the module's foot, plays them on the
  Lean machine.

To write the fixtures again after a change, follow the steps of `Test/Dogfood/README.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Lowered

open Effect4 Effect4.Machine Effect4.Program

/-! ## 1. A lowered run -/

/-- One lowered run: a name, a built program opened under its budgets, and a script. -/
structure Lowered where
  name : String
  opened : Run
  moves : List Move

/-- What one lowered run shows, computed once: the machine tape of the script's journal, the
session machine's view at each position, and the raw frame replay of each prefix of the tape. -/
structure Shown where
  /-- The tape's positions. -/
  positions : List Position
  /-- How many rows of the journal the tape left unread, at a frontier. -/
  left : Nat
  /-- The session machine's view at each position, the opened run first. -/
  views : List MachineView
  /-- The raw replay (`Api.replay`) of each prefix of the tape: how it ended, and its view. -/
  raw : List (Api.Outcome × MachineView)
  /-- Whether the empty table shows a difference on this run, in one projection: the machine's
  view of `machineViewOf`. It is `true` when, at some position, the raw replay with the empty
  table shows another view than the replay with the built table. The empty table is the table
  that the engine's production wrappers supply. Equal views do not show that the replay reads
  no row: `prepareExternalAnswer` (`src/Effect4/Program/Compile.lean`) consults a nonempty table
  for each successful reply, and an answer with no handle can come out the same. -/
  observedTableDifference : Bool

/-- A lowered run, played once. -/
def Lowered.shown (l : Lowered) : Shown :=
  let tape := tapeFrom l.opened (Scenario.play l.opened l.moves).journal
  let decisions := tape.1.map (·.decision)
  let built := l.opened.built
  let budget := l.opened.budget
  let prefixes := (List.range (decisions.length + 1)).map decisions.take
  let raw := prefixes.map fun taken =>
    let replayed := Api.replay built.program budget.fuel taken [] built.table budget.compileFuel
    (replayed.outcome, machineViewOf replayed.machine)
  let bare := prefixes.map fun taken =>
    machineViewOf (Api.replay built.program budget.fuel taken [] [] budget.compileFuel).machine
  { positions := tape.1
    left := tape.2.length
    views := machineView l.opened :: tape.1.map fun position => machineView position.after
    raw := raw
    observedTableDifference := bare != raw.map (·.2) }

/-- Whether the tape reads every row, and the raw replay of each prefix shows the session
machine's view at that position. -/
def Shown.agrees (x : Shown) : Bool := x.left == 0 && x.raw.map (·.2) == x.views

/-! ## 2. The fixture's text

The text is built, never read: appending and pushing stay under the axiom ceiling, where a fold
over a `String`'s characters does not. -/

/-- One hexadecimal digit. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Bytes in hexadecimal, two digits a byte. -/
def hex (bytes : List UInt8) : String :=
  bytes.foldl (fun text b => (text.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

/-- A list of items, comma-separated; `-` for none. -/
def items (texts : List String) : String := if texts.isEmpty then "-" else ",".intercalate texts

/-- A value: its canonical bytes. -/
def valText (v : Val) : String := hex (Effect4.Store.Val.encode v)

/-- A text: `s`, then its UTF-8 bytes. -/
def textOf (s : String) : String := "s" ++ hex s.toUTF8.data.toList

/-- A fiber's number. -/
def fiberText (fiber : FiberId) : String := toString fiber.value

/-- An exit: the value the machine reifies it as, or `-` for none. -/
def exitText : Option ExitV → String
  | none => "-"
  | some exit => valText (reifyExitVal exit)

/-- A call the machine waits on: fiber, guard token, row position, request. -/
def awaitText (a : Await) : String :=
  fiberText a.fiber ++ "." ++ toString a.token ++ "." ++
    (match a.op with | .external position => toString position | _ => "x") ++ "." ++
    valText a.request

/-- How a raw replay ended, as a word. -/
def outcomeText : Api.Outcome → String
  | .finished => "finished"
  | .frontier => "frontier"
  | .stuck _ => "stuck"

/-- One view line: the replay's outcome, then the six readings of `MachineView`. -/
def viewText (outcome : Api.Outcome) (view : MachineView) : String :=
  "view " ++ outcomeText outcome ++ " " ++ exitText view.rootExit ++ " " ++
    items (view.cells.map valText) ++ " " ++ items (view.awaiting.map awaitText) ++ " " ++
    items (view.queued.map fiberText) ++ " " ++ items (view.runnable.map fiberText) ++ " " ++
    items (view.timers.map fun timer => fiberText timer.1 ++ "@" ++ timer.2.toDecimal)

/-- The view lines of a run's fixture, as data: at each position the raw replay's outcome word
and the session machine's view. `Lowered.text` renders these lines, and the engine's test reads
them. -/
def Shown.lines (x : Shown) : List (String × MachineView) :=
  (x.raw.map fun entry => outcomeText entry.1).zip x.views

/-- Whether a decision of the tape counts. The tape is cut before its last decision that moves
the view: the last position whose view line is not the line before it. The raw replay of that
prefix must end at another line than the fixture's last. `false` for a tape in which no decision
moves the view: such a run fails, and it is not skipped. A script may end with decisions that
move nothing, as a second interruption of an exited fiber does. Those positions need no check
here: `agrees` compares each one. The engine's test takes the same cut from the same lines
(`ocaml/engine/test/scenarios/test_scenarios.ml`, S4). -/
def Shown.lastCounts (x : Shown) : Bool :=
  let lines := x.lines
  let moving := (List.range (lines.length - 1)).filter fun at_ => lines[at_]? != lines[at_ + 1]?
  match moving.getLast?, lines.getLast? with
  | some cut, some last =>
    match x.raw[cut]? with
    | some before => (outcomeText before.1, before.2) != last
    | none => false
  | _, _ => false

/-- One decision line. `none` for a decision the format does not carry: an interruption with
annotations, a delayed cell read, a failure that is not one tagged pair. -/
def decisionText : Api.Decision → Option String
  | .fire fiber => some ("fire " ++ fiberText fiber)
  | .flush => some "flush"
  | .evaluate fiber => some ("evaluate " ++ fiberText fiber)
  | .yieldVerdict fiber verdict =>
    some ("yield " ++ fiberText fiber ++ (if verdict then " 1" else " 0"))
  | .answerAsync fiber token (.ofExit (.success value)) =>
    some ("answer " ++ fiberText fiber ++ " " ++ toString token ++ " ok " ++ valText value)
  | .answerAsync fiber token (.ofExit (.failure cause)) =>
    match cause.reasons with
    | [.fail (.tagged tag message) annotations] =>
      if annotations.entries.isEmpty then
        some ("answer " ++ fiberText fiber ++ " " ++ toString token ++ " failed " ++
          textOf tag ++ " " ++ textOf message)
      else none
    | _ => none
  | .answerAsync _ _ (.ofRefGet _) => none
  | .interruptFrom interruptor annotations target =>
    if annotations.entries.isEmpty then
      some ("interrupt " ++ (match interruptor with | none => "-" | some fiber => fiberText fiber) ++
        " " ++ fiberText target)
    else none
  | .installMiddleware => some "middleware"
  | .advance millis => some ("advance " ++ millis.toDecimal)

/-- The text of one lowered run: its name, budgets, program and rows, then the line `table
differs` or `table same` (`Shown.observedTableDifference`), then the opened machine's view and
each decision with the view after it. The last line says whether the tape read every row, or how
many rows it left unread at a frontier. `none` for a decision the format does not carry. -/
def Lowered.text (l : Lowered) (x : Shown) : Option String := do
  let outcomes := x.raw.map (·.1)
  let opening ← (outcomes.zip x.views).head?
  let steps ← (x.positions.zip ((outcomes.zip x.views).drop 1)).mapM fun (position, after) => do
    let decision ← decisionText position.decision
    some ("step " ++ decision ++ "\n" ++ viewText after.1 after.2 ++ "\n")
  some ("run " ++ l.name ++ "\n" ++
    "fuel " ++ toString l.opened.budget.fuel ++ "\n" ++
    "compile " ++ toString l.opened.budget.compileFuel ++ "\n" ++
    "program " ++ hex (Api.bytesOf l.opened.built.program) ++ "\n" ++
    String.join (l.opened.built.table.map fun row =>
      "row " ++ hex (Effect4.Store.Canonical.encode row) ++ "\n") ++
    "table " ++ (if x.observedTableDifference then "differs" else "same") ++ "\n" ++
    viewText opening.1 opening.2 ++ "\n" ++
    String.join steps ++
    (if x.left == 0 then "end tape\n" else "end frontier " ++ toString x.left ++ "\n"))

/-- A fixture file: a header, then its runs. `none` when a run holds a decision the format does
not carry. -/
def fixture (runs : List (Lowered × Shown)) : Option String := do
  let texts ← runs.mapM fun run => run.1.text run.2
  some ("# GENERATED by Test/Dogfood/Scenario/Tape.lean; do not edit.\n" ++
    "# Write again: lake env lean --run ocaml/engine/test/scenarios/write.lean\n" ++
    String.join texts)

/-! ## 3. The runs -/

/-! The lane writes no script that a scenario's record lists. A lowered run with the name of a
record's run takes that run from the record: its opened program and its script. So a changed
script of a battery reaches the fixture, and one name has one script on every lane. The lane's
own runs are the two that no record lists, each written once in `own`. -/

/-- A named run of a scenario's record as a lowered run. Its name is the record's quoted name
(`Scenario.quote`), as on the host lane. -/
def ofRecord (scenario : Scenario) (run : NamedRun) : Lowered :=
  ⟨scenario.quote run, run.opened, run.moves⟩

/-- What the lane takes from the records: each fixture file, its scenario's record, and the names
of the runs in the file's order.

* **Workers.** The lowest-fiber schedule, both orders of the reply applications, and the
  cancellation followed to the root's exit.
* **Routing.** The three requests, and an infrastructure failure.
* **Atomic.** The scripted run to the root's exit, and the two hostile scripts. The shop has no
  host row, so its table is empty.
* **Timeout.** A reply before the timeout, the second attempt's reply after it, a late reply, a
  reply kept and never applied, a failure that does not retry, and four timeouts. A refused row
  gives no decision, so a late reply leaves no step on the tape. -/
def taken : List (String × Scenario × List String) :=
  [ ("workers.txt", Workers.scenario, ["lowest", "applied-1-2", "applied-2-1", "cancelled"])
  , ("routing.txt", Routing.scenario, ["200", "404", "401", "escape"])
  , ("atomic.txt", Atomic.scenario, ["finished", "interrupted", "stopped"])
  , ("timeout.txt", Timeout.scenario, ["before", "second", "late", "kept", "404", "four"]) ]

/-- The lane's own runs, each with its fixture file: the two scripts that no record lists.
`none` when a program does not build.

* **`workers/refused`**, on the crew: a duplicate reply receipt, a reply application, and the
  same application again as a raw row.
* **`handle/cache`**, on p1's own program, whose first host row answers a handle of the
  key-value store. The host answers the handle's number, and the session prepares the handle
  from the row table. It is the run on which the empty table shows another machine view. -/
def own : Option (List (String × Lowered)) := do
  let build := fun (m : Authoring.Module NativeOp) => (Effect4.Api.Author.build m).toOption
  let crew ← build (Workers.crew 2)
  let cache ← build P1HttpCache.program1
  some
    [ ("workers.txt", ⟨"workers/refused", Workers.opened crew,
        script [Workers.parked, Workers.takes, [.receive Workers.w1 (ok (.nat 1)),
          .apply Workers.w1, .row (.apply ⟨⟨1⟩, 1⟩)]]⟩)
    , ("timeout.txt", ⟨"handle/cache", Run.open cache "p1" Timeout.budget,
        script [[.start], answer (.row "Kv.make") (ok (.nat 0)), answer (.row "get") (ok .none),
          [.flush, .hold Timeout.http], answer Timeout.http (ok Timeout.body1),
          answer (.row "set") (ok .unit)]⟩) ]

/-- The names among these runs that a record gives one of its runs, as a lane quotes them. An
own run with such a name would give one name two scripts. -/
def clashesOf (runs : List Lowered) : List String :=
  let listed := taken.flatMap fun entry => entry.2.1.runs.map entry.2.1.quote
  (runs.map (·.name)).filter listed.contains

/-- What keeps the lane from its fixtures, each finding in a sentence, for a list of own runs.
Empty when the lane has its runs.

* A name that the lane takes, and that its record does not list.
* An own program that does not build.
* An own run that carries the name of a record's run: that name would have two scripts.
* An own run's name that stands twice among the own runs.
* An own run whose fixture file the lane does not write. -/
def findingsOf (mine : Option (List (String × Lowered))) : List String :=
  let missing := taken.flatMap fun entry =>
    entry.2.2.filterMap fun name =>
      if (entry.2.1.run? name).isSome then none
      else some ("the record of " ++ entry.2.1.name ++ " lists no run \"" ++ name ++ "\"")
  match mine with
  | none => missing ++ ["a program of the lane's own runs does not build"]
  | some runs =>
    let names := runs.map (·.2.name)
    missing ++
    (clashesOf (runs.map (·.2))).map (fun name =>
      "the name " ++ name ++ " carries two scripts: an own run of the lane and a run of a record") ++
    (names.eraseDups.filter fun name => names.count name != 1).map (fun name =>
      "the name " ++ name ++ " carries two scripts: two own runs of the lane") ++
    (runs.filter fun entry => !taken.any (·.1 == entry.1)).map fun entry =>
      "the own run " ++ entry.2.name ++ " names the fixture " ++ entry.1 ++ ", which the lane does not write"

/-- What keeps the lane from its fixtures. The writer prints each finding and writes nothing. -/
def findings : List String := findingsOf own

/-- Every fixture, for a list of own runs: its file under `ocaml/engine/test/scenarios/`, with
the runs that the lane takes from the file's record and then the own runs of that file. `none`
when `findingsOf` has a finding. -/
def fixturesOf (mine : Option (List (String × Lowered))) : Option (List (String × List Lowered)) :=
  if !(findingsOf mine).isEmpty then none
  else do
    let mine ← mine
    taken.mapM fun entry => do
      let runs ← entry.2.2.mapM fun name => (entry.2.1.run? name).map (ofRecord entry.2.1)
      some (entry.1, runs ++ (mine.filter (·.1 == entry.1)).map (·.2))

/-- Every fixture: its file, and its runs. `none` when `findings` is not empty. -/
def fixtures : Option (List (String × List Lowered)) := fixturesOf own

/-- Every fixture with each of its runs played once. -/
def shownFixtures : Option (List (String × List (Lowered × Shown))) :=
  fixtures.map fun all => all.map fun entry => (entry.1, entry.2.map fun l => (l, l.shown))

/-- The text of each fixture file, by its name. -/
def fixtureTexts : Option (List (String × String)) :=
  shownFixtures.bind fun all => all.mapM fun entry => (fixture entry.2).map fun text => (entry.1, text)

/-! ## 4. The journal's cut on a lowered run

The driver's laws of the journal's cut (`Test/Dogfood/Scenario.lean`) say what a prefix of a
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
that may stop. It is `tapeFrom_position_replays` (`Test/Dogfood/Scenario.lean`) at each
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
      (Api.replay l.opened.built.program l.opened.budget.fuel taken [] l.opened.built.table
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

/-- info: 'Test.Dogfood.Scenario.Lowered.shown_views_opened' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shown_views_opened

/--
info: Test.Dogfood.Scenario.Lowered.shown_views_opened: proved; nearest [Test.Dogfood.Scenario.tapeFrom_position_replays]; 0 lemmas, 27 definitions
Test.Dogfood.Scenario.tapeFrom_position_replays: proved; nearest [Test.Dogfood.Scenario.tape_replays]; 5 lemmas, 6 definitions
Test.Dogfood.Scenario.tape_replays: proved; nearest []; 11 lemmas, 6 definitions
next goals: 0
-/
#guard_msgs in
#plan_status shown_views_opened tapeFrom_position_replays tape_replays

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

/-- The run that a played run of the record started from: its own program, name, budgets and
profile, opened fresh. Playing the run's journal from it reaches the run again
(`Run.journal_replays`). -/
def openedOf (played : Run) : Run := Run.open played.built played.id played.budget played.profile

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
plays it. It takes the opened run and the rows from that run alone: `openedOf`, and the run's
journal. The two controls of the lowered run's views read no run: `Lowered.shown` plays the
script itself.

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
