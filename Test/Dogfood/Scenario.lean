import Effect4.Run
import Effect4.Author
import Effect4.Laws.Author

/-!
# Test.Dogfood.Scenario — the shared driver of the scenarios, and a scenario's record

Decisions row 254 (owner, 2026-10-05) asks for dogfooding that tests the semantics where features
compose, with no check outside a placed theorem or planned goal. A scenario is one unit with six
parts (`Test/Dogfood/README.md`): a program, a script, one named observation, a claim, the controls
and the lowered runs. This module holds what the scenarios share.

* **The script alphabet.** A `Move` is one thing a host does: a control decision, holding a call
  (`hold`), a reply receipt (`receive`), a reply application (`apply`), or one raw row for a red
  control. A script is a `List Move`: first-order data.
* **The driver.** `play` turns each move into rows of the run's own journal (`Move.rows`) and plays
  them through `Run.play`. It adds no scheduler and no program representation. The run it reaches
  is the run its journal reaches (`replays`), so a replay resolves no selector and calls no fixture.
* **Selection by key.** A move names a call by its fiber or by its row (`Sel`). The driver resolves
  the name to the key of a live call, and `Api.HostSession.Call.at` builds the call's claim.
* **Reply receipt and reply application apart.** `receive` plays the rows of `Rows.receive`, or the
  one `submit` row when the host already holds the call. `apply` plays the one row `.apply key`.
  The driver never plays `Rows.answer`: after a reply receipt it would bind and submit again.
* **The readers.** `receipts`, `applications`, `refusals` and `retired` read the session's part of
  an observation from the journal, its verdicts and the session's ledger.
* **The machine's tape.** The tape, the machine's view and their laws are general facts of a
  run. They stand in the library, in the namespace `Effect4.Run`. `machineView` is the machine's
  part of an observation, and `tapeFrom` reads the decisions that moved the machine off a
  journal: each control that progressed and each reply application
  (`src/Effect4/Run/Tape.lean`). A lowered run replays the tape and compares that view
  (`tape_replays`, `src/Effect4/Laws/Run/Tape.lean`). A journal whose tape stops has a completed
  prefix, and that prefix and each position of the tape replay raw too (`tapeFrom_cut_replays`,
  `tapeFrom_position_replays`). Section 4 gives each name that the scenarios use an alias in
  this module's namespace.
* **The record.** A `Scenario` names its program, its observation and its claim as declarations.
  It lists the assembled clauses, which the claim's proof uses, and the associated laws, which
  have controls only. `#scenario_gate`, at the foot of a battery, refuses a name that does not
  resolve, a claim that is no theorem or has no placement, a clause that the claim's proof does
  not reach, an entry without its green control or its red control, and a control that fails.
* **The named runs.** A scenario's record lists each of its scripts once, as a `NamedRun`: a
  name, the built program opened for a run, and the script. A control holds no script. It names
  the runs that its comparison reads, and the gate plays each named run once. The gate refuses a
  named run that no control reads. The host lane (`harness/truth/session/Keyed.lean`) and the
  engine's lane (`Test/Dogfood/Scenario/Tape.lean`) take their scripts from the same list, so
  no script is written twice.

The laws of section 4 are the driver's contract, each with its placement (decisions row 207).
`replays` and `receipt_inert` name the driver's moves, and they stand here. The laws that name
no move hold for every run and every session, and they stand in the library
(`src/Effect4/Laws/Run/Rows.lean`, `src/Effect4/Laws/Run/Tape.lean`). A scenario cites each as a
clause, and adds the planned goals of its own program.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## 1. How a script names a call -/

/-- A call as the host sees it: the row's spelling, the request, and the key that selects it. -/
structure Seen where
  row : String
  request : Val
  key : Key
deriving DecidableEq

/-- How a script names a call. A fiber parks on one call at a time, so a fiber names one call. -/
inductive Sel
  /-- The call this fiber is parked on. -/
  | fiber (id : FiberId)
  /-- The first call on the row with this spelling, in the machine's order. -/
  | row (spelling : String)
deriving DecidableEq

/-- Whether a selector names a call. -/
def Sel.names (sel : Sel) (call : Seen) : Bool :=
  match sel with
  | .fiber id => call.key.fiber == id
  | .row spelling => call.row == spelling

/-- The calls the machine is waiting on, as the host sees them, in the machine's order. -/
def live (s : Run) : List Seen :=
  s.outstanding.filterMap fun await =>
    (s.rowOf await.op).map fun row => ⟨row.spelling, await.request, ⟨await.fiber, await.token⟩⟩

/-- A journal row with its verdict. -/
def rows (s : Run) : List (Command × Phase) := s.journal.zip s.phases

/-- The calls' claims that the host holds or held: the accepted `bind` rows, in order, each with
its guard token. -/
def bound (s : Run) : List (Call × Nat) :=
  (rows s).filterMap fun
    | (.bind call token, .bound) => some (call, token)
    | _ => none

/-- A held call's claim as the host sees it. -/
def seenOf (s : Run) (entry : Call × Nat) : Option Seen :=
  (s.rowOf entry.1.op).map fun row => ⟨row.spelling, entry.1.request, ⟨entry.1.fiber, entry.2⟩⟩

/-- The calls the host holds or held, in the order it got them. -/
def held (s : Run) : List Seen := (bound s).filterMap (seenOf s)

/-- The key a selector names: the live call it names. With no such live call it names the latest
call the host held, so a script can send a late reply for a call the machine dropped. -/
def Sel.key (sel : Sel) (s : Run) : Option Key :=
  match (live s).find? sel.names with
  | some call => some call.key
  | none => ((held s).reverse.find? sel.names).map (·.key)

/-! ## 2. The script alphabet and the driver -/

/-- One step of a script, by what the host does. -/
inductive Move
  /-- A control decision: evaluate, flush, a clock step, an interruption. -/
  | control (decision : Api.Decision)
  /-- The host gets the call and holds it: the session binds the call, with no reply. -/
  | hold (call : Sel)
  /-- The reply receipt: the session stores the host answer for the call. The machine does not
  run. -/
  | receive (call : Sel) (completion : Api.HostSession.Answer)
  /-- The reply application: the session applies the stored reply at the call's key. -/
  | apply (call : Sel)
  /-- One raw row, for a red control: a reply under another key, a row recorded earlier. -/
  | row (command : Command)
deriving DecidableEq

/-- The rows a move plays on a run. The claim of a live call comes from `Call.at`. A host answer
for a call the host holds or held is one `submit` row against that claim. A host answer for a live
call the host does not hold is the two rows of `Rows.receive`. -/
def Move.rows (s : Run) : Move → List Command
  | .control decision => [.control decision]
  | .hold call =>
    match (live s).find? call.names with
    | none => []
    | some seen =>
      match Call.at s seen.key with
      | none => []
      | some claim => [.bind claim seen.key.token]
  | .receive call completion =>
    match call.key s with
    | none => []
    | some key =>
      match (bound s).reverse.find? (fun entry => (⟨entry.1.fiber, entry.2⟩ : Key) == key) with
      | some entry => [.submit (Rows.reply s entry.1 key completion)]
      | none => Rows.receive s key completion
  | .apply call =>
    match call.key s with
    | none => []
    | some key => [.apply key]
  | .row command => [command]

/-- One move played: its rows go into the run's journal, each with its verdict. -/
def step (s : Run) (move : Move) : Run := s.play (move.rows s)

/-- A script played, move by move. -/
def play (s : Run) (moves : List Move) : Run := moves.foldl step s

/-- A host answer that succeeds with a value. -/
def ok (value : Val) : Api.HostSession.Answer := .ofExit (.success value)

/-- A host answer that fails with a tag and a message, the pair spelling of DB-15. -/
def failed (tag message : String) : Api.HostSession.Answer :=
  .ofExit (.failure (Cause.fail (.tagged tag message)))

/-- The root evaluated: the move that starts a run. -/
def Move.start : Move := .control Api.evaluate

/-- Every armed dispatcher drained. -/
def Move.flush : Move := .control Api.flush

/-- The logical clock advanced by `millis`. -/
def Move.tick (millis : Nat) : Move := .control (Api.TestClock.adjust (ClockMillis.ofNat millis))

/-- The host cancels a fiber: `interruptUnsafe` with no interruptor. -/
def Move.cancel (fiber : FiberId) : Move := .control (.interruptFrom none .empty fiber)

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

/-! ## 4. The driver's contract -/

/-! ### The library's names

The laws of a run's rows and the machine's tape name no scenario. They moved into the library
with their statements unchanged (decisions row 284, point 5), and their namespace is
`Effect4.Run`.

* `src/Effect4/Run/Tape.lean`: the machine's view, a position, the decision of a row, the tape,
  the fresh open, a funded run and rest. They are executable definitions of the core.
* `src/Effect4/Laws/Run/Rows.lean`: what playing rows keeps, the inertness of a receipt row, and
  the laws of a reply application and of a control.
* `src/Effect4/Laws/Run/Tape.lean`: `tape_replays`, the laws of the journal's cut and
  `funded_replays`.

The command below gives each of those names that the scenario tree uses an alias in this
namespace. So a battery writes `tapeFrom` or `funded` as it did, and a battery's own declaration
of the same short name still comes first. -/

export Effect4.Run (MachineView machineViewOf machineView Position openedOf atRest
  tapeFrom tapeOf funded Inert AppliedSelects ControlRetires
  play_id play_budget play_profile play_receiptRows receive_receiptRows
  applied_selects control_retires tape_replays tapeFrom_append tapeFrom_cut
  tapeFrom_cut_replays tapeFrom_position_prefix tapeFrom_position_replays funded_replays)

/-! ### A script's run replays from its journal -/

/-- Helper of `replays`: a script only plays rows, so it keeps what the run was opened with. -/
theorem play_opened (s : Run) (moves : List Move) :
    (play s moves).built = s.built ∧ (play s moves).id = s.id ∧
      (play s moves).budget = s.budget ∧ (play s moves).profile = s.profile := by
  induction moves generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons move rest ih =>
    obtain ⟨hb, hi, hf, hp⟩ := ih (step s move)
    exact ⟨hb.trans (Run.play_built s _), hi.trans (play_id s _), hf.trans (play_budget s _),
      hp.trans (play_profile s _)⟩

/-- Helper of `replays`: a script played from a recorded run reaches a recorded run. -/
theorem reached_play (s : Run) (moves : List Move) (h : Run.Reached s) :
    Run.Reached (play s moves) := by
  induction moves generalizing s with
  | nil => exact h
  | cons move rest ih => exact ih (step s move) (Run.Reached.play s _ h)

/-- **A script's run replays from its journal.** The run that a script reaches from an opened
program is reached again by playing the journal it recorded. The journal holds rows only, so the
replay resolves no selector and calls no fixture. Reach: any built program, name, budget and
script. It does not establish that two hosts choose the same rows, and it says nothing of a
lowered run. Consumer: every scenario of `Test/Dogfood/Scenario/`. It is `journal_replays`
(`src/Effect4/Laws/Run.lean`, R13's node) on the driver's scripts. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem replays (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move) :
    (Run.open b id budget profile).play (play (Run.open b id budget profile) moves).journal =
      play (Run.open b id budget profile) moves := by
  have recorded := Run.journal_replays _ (reached_play _ moves (Run.Reached.opened b id budget profile))
  obtain ⟨hb, hi, hf, hp⟩ := play_opened (Run.open b id budget profile) moves
  rw [hb, hi, hf, hp] at recorded
  exact recorded

/-! ### A reply receipt does not advance the machine -/

/-- The proposition of `receipt_inert`: holding a call and receiving a reply are inert. -/
def ReceiptInert : Prop :=
  ∀ (s : Run) (call : Sel) (completion : Api.HostSession.Answer),
    Inert s (step s (.hold call)) ∧ Inert s (step s (.receive call completion))

/-- **A reply receipt does not advance the machine.** When the host holds a call (`hold`) or the
session receives a reply (`receive`), four readings stay as they were: the machine, the count of
applied replies, the consumed calls and the retired calls. The session may accept the rows or
refuse them. Reach: any run and any selector, live or not. It does not establish that the session
accepts a reply receipt, and it says nothing of the reply application, a separate ordered step.
Consumer: the workers scenario's clause "receipt". It lifts `submit_machine`
(`src/Effect4/Laws/Api/HostSession.lean`) to the driver. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem receipt_inert : ReceiptInert := by
  intro s call completion
  refine ⟨play_receiptRows s _ ?_, play_receiptRows s _ ?_⟩
  · simp only [Move.rows]
    split
    · rfl
    · split <;> rfl
  · simp only [Move.rows]
    split
    · rfl
    · split
      · rfl
      · exact receive_receiptRows s _ completion

/-! ## 5. A scenario's record, and the gate at the foot of a battery -/

/-- One entry of a scenario's record: a clause of its claim, or a law beside it, with the
declaration that states it. -/
structure Clause where
  /-- The entry's name, as its controls quote it. -/
  name : String
  /-- The theorem or the planned goal that states the entry. It has a placement. -/
  claim : Lean.Name

/-- One named run of a scenario: one script on one program. A scenario's record lists each one
once, and every consumer of a script takes it from that list: the gate, the host lane
(`harness/truth/session/Keyed.lean`) and the engine's lane (`Test/Dogfood/Scenario/Tape.lean`).
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
  /-- The claim: the theorem whose proof assembles the clauses. Its standing is derived from its
  proof: proved, or proved modulo the clauses that are planned goals. -/
  claim : Lean.Name
  /-- The assembled clauses. The claim's proof uses the declaration of each, and rests on no
  planned goal besides them. The gate measures both, so the record says what the proof does. -/
  clauses : List Clause
  /-- The associated laws: laws that the scenario's runs control. The record claims no dependency
  of the claim on them, and the gate measures none. -/
  laws : List Clause := []
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

/-- The names that a record lists more than once, each once, in the record's order. -/
def Scenario.repeated (s : Scenario) : List String :=
  (s.runs.foldl (fun (state : List String × List String) run =>
    if !state.1.contains run.name then (state.1 ++ [run.name], state.2)
    else if state.2.contains run.name then state
    else (state.1, state.2 ++ [run.name])) ([], [])).2

/-- The named runs that no control reads, by name, in the record's order. The gate refuses such
a run: a lane would perform it, and no control of the battery would compare it. -/
def Scenario.unread (s : Scenario) : List String :=
  (s.runs.map (·.name)).filter fun name => !s.controls.any (·.reads.contains name)

/-- What is wrong with a record as data, each finding in a sentence: a clause or a law with no
green control or no red control, a run's name listed twice, a named run that no control reads, a
control that names no entry, a control that reads a run which the record does not list, a
control that fails. It plays each named run once, and it hands each control the runs that the
control reads. Empty for a record with no finding. -/
def Scenario.problems (s : Scenario) : List String :=
  let played := s.runs.map fun run => (run.name, run.played)
  let missing := fun (kind : String) (entries : List Clause) =>
    entries.flatMap fun entry =>
      [false, true].filterMap fun isRed =>
        if s.controls.any (fun control => control.clause == entry.name && control.isRed == isRed)
        then none
        else some (s.name ++ ": the " ++ kind ++ " \"" ++ entry.name ++ "\" has no " ++
          (if isRed then "red control" else "green control"))
  missing "clause" s.clauses ++ missing "law" s.laws ++
  s.repeated.map (fun name => s.name ++ ": the record lists the run \"" ++ name ++ "\" twice") ++
  s.unread.map (fun name => s.name ++ ": no control reads the run \"" ++ name ++ "\"") ++
  s.controls.filterMap fun control =>
    if !(s.clauses ++ s.laws).any (·.name == control.clause) then
      some (s.name ++ ": the control \"" ++ control.name ++ "\" names no clause and no law")
    else
      match control.reads.find? (fun name => !played.any (·.1 == name)) with
      | some name =>
        some (s.name ++ ": the control \"" ++ control.name ++ "\" reads the run \"" ++ name ++
          "\", which the record does not list")
      | none =>
        let runs := control.reads.filterMap fun name => (played.find? (·.1 == name)).map (·.2)
        if !control.holds runs then some (s.name ++ ": the control \"" ++ control.name ++ "\" fails")
        else none

/-- The declarations a record names besides its claims. -/
def Scenario.declarations (s : Scenario) : List Lean.Name := [s.program, s.observation]

/-- The claims a record names: the scenario's claim, then each clause's and each law's. -/
def Scenario.claims (s : Scenario) : List Lean.Name :=
  s.claim :: (s.clauses ++ s.laws).map (·.claim)

/-! The gate at the foot of a battery, `#scenario_gate`, reads the semantics registry and the
planning graph, which are tools. It stands in `Test/Audit/ScenarioGate.lean`, so this module imports
entry modules only (decisions row 332, cutover slice C4). -/

/-! ## 6. A log's note

A scenario's program keeps a log in a cell: the assignments, the released connections, the
cleanups. Each battery wrote the same append under the fixed name `xs` for the cell's value. A
row elaborates its whole binder term under that name, so a caller's variable `xs` inside the
entry would read the log. The batteries' entries hold no such variable, so their trees are the
same under either helper. The one helper here mints the name
(`Ref.updateWith`, `src/Effect4/Program/Authoring/Rows.lean`).

Placement of the controls. They are finite controls of `var_push_minted`
(`src/Effect4/Laws/Program/Author.lean`): a minted binder leaves a variable that an author wrote
reading what it read. That law serves the claim `operation-data-scoped` (concept
`initial-algebras-folds`, requirement R4). The promise is for a variable that the caller reads
through `var`. A source term that inspects its scope in another way is outside it. The two
helpers have one type, so the controls compare a value: typing cannot see the capture. -/

section Note

open Effect4.Program.Authoring

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. The name of the
cell's current value is minted, so a variable that the caller reads through `var` keeps its
reading inside the entry. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.updateWith log fun xs => app "append" [xs, app "cons" [x, app "nil" []]]

/-! The collision's control. Its pieces stand in a namespace of their own, so that no battery
of this folder reads one by accident. -/

namespace Collision

/-- The helper that each battery wrote before: the same append under the fixed name `xs`. It
stays as the red control of the collision. -/
def noteFixed (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log

/-- The list of the given numbers, as a term. -/
def numbers : List Nat → TermSrc
  | [] => app "nil" []
  | n :: rest => app "cons" [nat n, numbers rest]

/-- Codex's collision case. An outer variable, under the name `outer`, holds `[7, 8]`. The log
holds `[100]`. The entry is the length of the outer variable. The module answers the log. -/
def program (outer : String) (noteWith : TermSrc → TermSrc → Src NativeOp) : Module NativeOp :=
  { main := bindName outer (succeed (numbers [7, 8])) fun _ =>
      bindName "log" (Ref.make (numbers [100])) fun log =>
        andThen (noteWith log (app "length" [var outer])) (Ref.get log) }

/-- The log that a collision module answers. -/
def logged (m : Module NativeOp) : Option ExitV :=
  (Effect4.Api.Author.build m).toOption.map (·.runSync)

-- Green: under the minted name the entry reads the outer `xs`, of length 2.
#guard logged (program "xs" note) = some (.success (.list [.nat 100, .nat 2]))
-- Red: under the fixed name the entry reads the log itself, of length 1. Both modules build:
-- the two lists have one type.
#guard logged (program "xs" noteFixed) = some (.success (.list [.nat 100, .nat 1]))
-- A name that does not collide: the two helpers elaborate one tree, and it answers `[100, 2]`.
#guard decide (elaborateModule (program "ys" note) = elaborateModule (program "ys" noteFixed))
#guard logged (program "ys" noteFixed) = some (.success (.list [.nat 100, .nat 2]))

end Collision

end Note

end Test.Dogfood.Scenario
