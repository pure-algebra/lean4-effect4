import Test.Dogfood.Scenario.Data
import Effect4.Laws.Author

/-!
# Test.Dogfood.Scenario — the shared driver of the scenarios, and a scenario's record

Decisions row 254 (owner, 2026-10-05) asks for dogfooding that tests the semantics where features
compose, with no check outside a placed theorem or planned goal. A scenario is one unit with six
parts (`Test/Dogfood/README.md`): a program, a script, one named observation, a claim, the controls
and the lowered runs. This module holds what the scenarios share.

* **The script alphabet.** A `Move` is the library's event (`Effect4.Run.Event`,
  `src/Effect4/Run/Event.lean`, slice DM1): a control decision, holding a call (`hold`), a reply
  receipt (`receive`), a reply application (`apply`), or a remote host's run command (`wire`), the
  raw row of a red control. A script is a `List Move`: first-order data.
* **The driver.** `play` turns each move into rows of the run's own journal (`Event.rows`) and plays
  them through `Run.play`. It adds no scheduler and no program representation. The run it reaches
  is the run its journal reaches (`replays`), so a replay resolves no selector and calls no fixture.
* **Selection.** A move names a call by its key, its fiber or its row (`Sel`). The library resolves
  the name to the key of the one live call it names, and `Api.HostSession.Call.at` builds the
  call's claim. A row selector that names two live calls is unresolved, and its move plays nothing.
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
* **The record.** A `Scenario` names its program and its observation as declarations, and lists
  its named runs and its controls. Decisions row 410 retired the scenarios' claims and their gate.
* **The named runs.** A scenario's record lists each of its scripts once, as a `NamedRun`: a
  name, the built program opened for a run, and the script. A control holds no script; it names
  the runs that its comparison reads. The host lane (`git:38b94bdec:harness/truth/session/Keyed.lean`) and the
  engine's lane (`Test/Dogfood/Scenario/TapeData.lean`) take their scripts from the same list, so
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

export Effect4.Run (Inert AppliedSelects ControlRetires
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
  · simp only [Effect4.Run.Event.rows, Effect4.Run.Event.commands]
    cases call.one s with
    | none => rfl
    | some seen =>
      dsimp only
      cases Api.HostSession.Call.at s seen.key with
      | none => rfl
      | some claim => rfl
  · simp only [Effect4.Run.Event.rows, Effect4.Run.Event.commands]
    cases call.resolve s with
    | none => rfl
    | some key =>
      dsimp only
      cases (bound s).reverse.find? (fun entry => (⟨entry.1.fiber, entry.2⟩ : Key) == key) with
      | some entry => rfl
      | none => exact receive_receiptRows s key completion

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
