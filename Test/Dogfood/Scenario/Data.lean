import Effect4.Run
import Effect4.Author

/-! Shared scenario data. The proof contract stays in `Test.Dogfood.Scenario`. -/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## 1. The library's events

The events, the selectors and the readers that resolve a selector stand in the library
(`src/Effect4/Run/Event.lean`, slice DM1 of the session note). A row selector that names two live
calls is unresolved there (decisions row 326 (4)), so its move plays nothing. The command below
gives each name that the scenario tree uses an alias in this namespace. -/

export Effect4.Run (Seen Sel Event live rows bound seenOf held)

/-- A step of a script: the library's event. The scenarios and the host lane
(`harness/truth/session/Keyed.lean`) name it `Move`. -/
abbrev Move := Event

/-! ## 2. The driver -/

/-- One move played: its rows go into the run's journal, each with its verdict. It is the run that
`Run.feed` reaches (`Run.feed_fst`). -/
def step (s : Run) (move : Move) : Run := s.play (move.rows s)

/-- A script played, move by move. -/
def play (s : Run) (moves : List Move) : Run := moves.foldl step s

/-- A host answer that succeeds with a value. -/
def ok (value : Val) : Api.HostSession.Answer := .ofExit (.success value)

/-- A host answer that fails with a tag and a message, the pair spelling of DB-15. -/
def failed (tag message : String) : Api.HostSession.Answer :=
  .ofExit (.failure (Cause.fail (.tagged tag message)))

/-- A reply receipt, then its reply application: two moves, two verdicts. -/
def answer (call : Sel) (completion : Api.HostSession.Answer) : List Move :=
  [.receive call completion, .apply call]

/-- A script from its parts, in order. -/
def script (parts : List (List Move)) : List Move := parts.flatten

/-! ## 3. The session's part of an observation -/

/-- The call the host holds or held at a key. -/
def seenAt (s : Run) (key : Key) : Option Seen := (held s).find? (·.key == key)

/-- The accepted reply receipts, in order. -/
def receipts (s : Run) : List Seen :=
  (rows s).filterMap fun
    | (.submit reply, .preflight) => seenAt s reply.key
    | _ => none

/-- The reply applications the session applied, in order. -/
def applications (s : Run) : List Seen :=
  (rows s).filterMap fun
    | (.apply key, .applied) => seenAt s key
    | _ => none

/-- The kind of a row, as a word. -/
def kindOf : Command → String
  | .bind _ _ => "bind"
  | .submit _ => "submit"
  | .apply _ => "apply"
  | .control _ => "control"

/-- The refused rows, in order: the kind of each row and the session's reason. -/
def refusals (s : Run) : List (String × Api.HostSession.Refusal) :=
  (rows s).filterMap fun
    | (command, .refused why) => some (kindOf command, why)
    | _ => none

/-- Whether the session refused exactly these rows, in order. -/
def refused (s : Run) (expected : List (String × Api.HostSession.Refusal)) : Bool :=
  refusals s == expected

/-- The retired calls, in retirement order, each with whether a reply waited for it. -/
def retired (s : Run) : List (Seen × Bool) :=
  s.session.retired.filterMap fun call =>
    (seenOf s (call.bound.call, call.bound.token)).map fun seen => (seen, call.pending.isSome)

/-- The requests of the calls the host held on one row, in order. -/
def requestsOn (s : Run) (row : String) : List Val :=
  ((held s).filter (·.row == row)).map (·.request)

/-- The value a cell holds, by its allocation index: a program's log, read from the store. -/
def cell (s : Run) (index : Nat) : Option Val := s.machine.state.refs[index]?

export Effect4.Run (MachineView machineViewOf machineView Position openedOf atRest
  tapeFrom tapeOf funded)

/-! ## 5. A scenario's record -/

/-- One named run of a scenario: one script on one program. A scenario's record lists each one
once, and every consumer of a script takes it from that list: the host lane
(`harness/truth/session/Keyed.lean`) and the engine's lane (`Test/Dogfood/Scenario/TapeData.lean`).
A lane quotes a run as the scenario's name, a slash and the run's name (`Scenario.quote`). -/
structure NamedRun where
  /-- The run's name in its scenario. -/
  name : String
  /-- The built program, opened as its battery opens it: under its name and its budgets. -/
  opened : Run
  /-- The script. -/
  moves : List Move

/-- A named run, played: the run that its script reaches from the opened program. -/
def NamedRun.played (run : NamedRun) : Run := play run.opened run.moves

/-- The named scripts shared by a battery and its fixture writers. -/
structure RunSet where
  name : String
  runs : List NamedRun

/-- Look up one script by its name within the scenario. -/
def RunSet.run? (s : RunSet) (name : String) : Option NamedRun :=
  s.runs.find? (·.name == name)

/-- The name shared by every lane that performs this run. -/
def RunSet.quote (s : RunSet) (run : NamedRun) : String := s.name ++ "/" ++ run.name

/-- One control of an entry. A green control is a run that the entry allows. A red control is a
fault made on purpose, which the session must refuse or the observation must tell apart. A
control holds no script: it names the runs that its comparison reads. -/
structure Control where
  /-- The clause or the law this run controls, by its name. -/
  clause : String
  /-- `false` for a green control, `true` for a red control. -/
  isRed : Bool
  /-- What the run shows. -/
  name : String
  /-- The named runs that the comparison reads, by their names in the scenario's record, in the
  order the comparison takes them. Empty for a control that compares no script's run. -/
  reads : List String
  /-- Whether the runs show it: a comparison on the scenario's observation, decided by running.
  The gate plays each named run once and hands the comparison the runs that `reads` names, in
  that order. -/
  holds : List Run → Bool

/-- A green control of an entry. -/
def green (clause name : String) (reads : List String) (holds : List Run → Bool) : Control :=
  ⟨clause, false, name, reads, holds⟩

/-- A red control of an entry. -/
def red (clause name : String) (reads : List String) (holds : List Run → Bool) : Control :=
  ⟨clause, true, name, reads, holds⟩

/-- A scenario's record. The program, the observation and the claims are named as declarations,
so a name that no longer resolves fails where the record is written. -/
structure Scenario where
  /-- The scenario's name, as its row of `Test/Dogfood/README.md` quotes it. -/
  name : String
  /-- The program the scenario runs. -/
  program : Lean.Name
  /-- The one named observation every control compares. -/
  observation : Lean.Name
  /-- The named runs: each script of the scenario, once, on the program it runs on. A name
  stands once, and some control reads each run. The order is the order in which a lane performs
  the runs. -/
  runs : List NamedRun := []
  /-- The controls: for each clause and each law a green control and at least one red control. -/
  controls : List Control

/-- The named run of a record with this name. -/
def Scenario.run? (s : Scenario) (name : String) : Option NamedRun :=
  s.runs.find? (·.name == name)

/-- A run of a record as a lane quotes it: the scenario's name, a slash and the run's name. The
host lane and the engine's lane quote a run by this one function, so a name means one run on
both. -/
def Scenario.quote (s : Scenario) (run : NamedRun) : String := s.name ++ "/" ++ run.name

open Effect4.Program.Authoring

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. The name of the
cell's current value is minted, so a variable that the caller reads through `var` keeps its
reading inside the entry. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.updateWith log fun xs => app "append" [xs, app "cons" [x, app "nil" []]]

end Test.Dogfood.Scenario
