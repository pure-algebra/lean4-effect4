import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Routing

/-!
# The machine tapes of the scenarios, and the fixture text Lean writes for the engine

Decisions row 254 asks that a scenario's observation be compared on the generated OCaml engine.
The engine holds no session: no stored reply, no retired call, no consumed call. So a scenario's
observation lands as two clauses. The session clause is the whole observation, checked in each
scenario's battery. The machine clause is `machineView` (`Test/Dogfood/Scenario.lean`): the
root's exit, the cells, the calls the machine waits on, the armed owners, the runnable fibers and
the timers.

This module holds what Lean writes for the machine clause. It has no control and no gate, so it
builds whatever the committed fixtures hold. The writer imports it. The battery
`Test/Dogfood/Scenario/Lowered.lean` binds the committed files to its text.

* **A lowered run.** `Lowered`: a built program opened for a run, and a script. Its machine tape
  is `tapeFrom` on the journal the script leaves. The tape holds each control that progressed and
  each reply application. A held call, a reply receipt and a refused row give no decision.
* **The fixture.** `text`: the program's canonical bytes, each row's canonical bytes, the budgets,
  then each decision with the machine view after it. A value is its canonical bytes in
  hexadecimal (`Val.encode`), and an exit is the value `reifyExitVal` gives it.
* **The runs.** `fixtures`: each fixture file's name, with the lowered runs of its scenario.

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

/-- Whether the raw replay of the tape without its last decision ends at another view than the
session machine's last. -/
def Shown.lastCounts (x : Shown) : Bool :=
  match x.views.reverse, x.raw.reverse with
  | last :: _, _ :: before :: _ => before.2 != last
  | _, _ => false

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

/-- The workers scenario's lowered runs: the lowest-fiber schedule, both orders of the reply
applications, and the cancellation followed to the root's exit. -/
def workersRuns (b : Api.Built) : List Lowered :=
  [ ⟨"workers/lowest", Workers.opened b, Workers.lowest⟩
  , ⟨"workers/applied-1-2", Workers.opened b,
      script [Workers.parked, Workers.takes, [.apply Workers.w1, .apply Workers.w2]]⟩
  , ⟨"workers/applied-2-1", Workers.opened b,
      script [Workers.parked, Workers.takes, [.apply Workers.w2, .apply Workers.w1]]⟩
  , ⟨"workers/cancelled", Workers.opened b,
      script [Workers.running, [.cancel ⟨2⟩], Workers.finish]⟩
  , ⟨"workers/refused", Workers.opened b,
      script [Workers.parked, Workers.takes, [.receive Workers.w1 (ok (.nat 1)), .apply Workers.w1,
        .row (.apply ⟨⟨1⟩, 1⟩)]]⟩ ]

/-- The routing scenario's lowered runs: the three requests, and an infrastructure failure. -/
def routingRuns (bob missing denied : Api.Built) : List Lowered :=
  [ ⟨"routing/200", Routing.opened bob, Routing.lookups 2⟩
  , ⟨"routing/404", Routing.opened missing, Routing.lookups 9⟩
  , ⟨"routing/401", Routing.opened denied, Routing.lookups 2⟩
  , ⟨"routing/escape", Routing.opened bob, Routing.failing "SqlError" "connection lost"⟩ ]

/-- Every fixture: its file under `ocaml/engine/test/scenarios/`, and its runs. `none` when a
program does not build. -/
def fixtures : Option (List (String × List Lowered)) := do
  let build := fun (m : Authoring.Module NativeOp) => (Effect4.Api.Author.build m).toOption
  let crew ← build (Workers.crew 2)
  let bob ← build (Routing.request "secret" 2 "2")
  let missing ← build (Routing.request "secret" 9 "9")
  let denied ← build (Routing.request "wrong" 2 "2")
  some [("workers.txt", workersRuns crew), ("routing.txt", routingRuns bob missing denied)]

/-- Every fixture with each of its runs played once. -/
def shownFixtures : Option (List (String × List (Lowered × Shown))) :=
  fixtures.map fun all => all.map fun entry => (entry.1, entry.2.map fun l => (l, l.shown))

/-- The text of each fixture file, by its name. -/
def fixtureTexts : Option (List (String × String)) :=
  shownFixtures.bind fun all => all.mapM fun entry => (fixture entry.2).map fun text => (entry.1, text)

end Test.Dogfood.Scenario.Lowered
