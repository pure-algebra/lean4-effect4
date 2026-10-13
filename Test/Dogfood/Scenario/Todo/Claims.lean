import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Application
import Test.Audit.ScenarioGate
import Effect4.Laws.Api.SessionMeaning

/-!
# The to-do application's claims and their record

The claims packet's slices RECORD to MODEL (`docs/research/2026-10-07-packet-application-claims.md`;
decisions rows 307 (9) and 336 (9)), on the application of `Test/Dogfood/Scenario/Todo.lean`.

* **The claims.** Each clause is a theorem or a planned goal with its placement. `serves`
  assembles them, and the plan derives its status (`#plan_status`).
* **Each statement is the session form of a fact of the call tree.** It reads a recorded run of a
  built entry: every run that the driver reaches (`Run.Reached`), not only the scripts below. A
  statement that reads the exit takes the premises of `denoteRows_eq_session`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`): the run is funded, at rest and driven by a host.
  So the call tree proves each statement through a theorem that exists (the packet's slice TREE).
* **The record.** `claimRecord` is the scenario's record and one note for each entry
  (`Test/Dogfood/Application.lean`). `#scenario_gate` checks the scenario, and `#guard` reads the
  notes.
* **The runs and the controls.** Each script once, as a named run. Each entry has a green control
  and a red control. Each run is a finite probe: one script on the Lean machine.

The goals stay out of the requirement rows (decisions row 336 (9)): no root of the semantics
registry loads this module. Each carries its placement at R6, which the scenario gate asks of a
battery's claim.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote (ReplyTape)
open Effect4.Run (appliedExits hostDriven)
open Test.Dogfood.P2HandlerLayers (recordVal)
open Test.Dogfood.Application (Kind Grade Premise Note Record)

/-! ## 1. Two facts of the call tree -/

/-- The proposition of `add_empty_calls_nothing`. -/
def AddEmptyCallsNothing : Prop :=
  ∀ s : Run, Run.Reached s → builtAt "add" [str ""] = some s.built → held s = []

/-- **`add` with an empty title makes no call.** In every recorded run of the entry `add` at the
empty title, the host holds no call.

Placement: concept `host-session-protocol`; property: the meaning of the row table agrees with
the session, read at one program. Question: this planned goal; consumer: the claim `serves`.
Reach: the entry `add` at the empty title, every run the driver reaches from its build, every
budget. Does not establish: what `add` calls at another title; anything of a lowered run.
Unlocks: R6's guarantee for a program with host rows, at one program (row 99). Kind: a fact of
the call tree. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal add_empty_calls_nothing : AddEmptyCallsNothing

/-- The proposition of `complete_failure_escapes`. -/
def CompleteFailureEscapes : Prop :=
  ∀ (id : Nat) (s : Run) (cause : CauseV), Run.Reached s →
    builtAt "complete" [nat id] = some s.built →
    funded s = true → atRest s = true → hostDriven s = true →
    (appliedExits s).head? = some (.failure cause) → s.exit = some (.failure cause)

/-- **A failure of the repository leaves `complete` unchanged.** In every recorded run of the
entry `complete` that is funded, at rest and driven by a host, where the first applied reply is a
failure, the root fails with that failure.

Placement: concept `host-session-protocol`; property as `add_empty_calls_nothing`. Question:
this planned goal; consumer: the claim `serves`. Reach: the entry `complete` at every id, every
cause, every such run. Does not establish: which failures the session applies (reply admission
refuses one outside the row's error column: a red control); a run with an interruption, a clock
step or a delayed cell read, where the premises fail. Unlocks: as `add_empty_calls_nothing`.
Kind: a fact of the call tree. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal complete_failure_escapes : CompleteFailureEscapes

/-! ## 2. The claim -/

/-- **The to-do application's claim.** It assembles its clauses, and the plan derives its status
from their proofs. Two laws stand beside it with controls only: a script's run replays from its
journal (`replays`), and a stored successful reply fits its row
(`Effect4.Api.HostSession.submit_success_prepared_fits`). The proof uses neither. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serves : AddEmptyCallsNothing ∧ CompleteFailureEscapes :=
  ⟨add_empty_calls_nothing, complete_failure_escapes⟩

/-! ## 3. The observation, the named runs and the controls -/

/-- The application's one observation of a run: the root's exit, the calls that the host held,
the refused rows, the exits of the applied replies, and whether the run meets the premises of
`denoteRows_eq_session` (funded, at rest, driven by a host). -/
structure Observation where
  outcome : Option ExitV
  calls : List (String × Val)
  refusals : List (String × Api.HostSession.Refusal)
  applied : ReplyTape
  settled : Bool
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { outcome := s.exit, calls := (held s).map fun call => (call.row, call.request)
    refusals := refusals s, applied := appliedExits s
    settled := funded s && atRest s && hostDriven s }

/-- A built entry, opened under the application's name. -/
def opened (b : Api.Built) : Run := Run.open b application.name

/-- The script that fails the one call of `complete` with the repository's tag. -/
def repoFails (message : String) : List Move :=
  script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" message)]

/-- The failure of an empty title, at the root. -/
def emptyTitleExit : ExitV := .failure (Cause.fail (.tagged "EmptyTitle" "a title is required"))

/-- The named runs: each script once, from one build of each entry at its argument. -/
def runsOf (empty milk done : Api.Built) : List NamedRun :=
  [ ⟨"empty", opened empty,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))]⟩
  , ⟨"milk", opened milk,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))]⟩
  , ⟨"locked", opened done, repoFails "locked"⟩
  , ⟨"other-tag", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (failed "Timeout" "slow")]⟩
  , ⟨"done", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true)))]⟩
  , ⟨"wide", opened done,
      script [[.start], answer (.row "TodoRepo.setDone")
        (ok (.some (recordVal ["id", "title", "done", "at"]
          [.nat 1, .str "milk", .bool true, .nat 0])))]⟩ ]

/-- The controls: for each clause and each law a green control and at least one red control. -/
def controlsOf : List Control :=
  [ -- `add` with an empty title makes no call
    green "no call" "an empty title fails, and the host holds no call, though offered an answer"
      ["empty"] fun
      | [empty] => observe empty == ⟨some emptyTitleExit, [], [], [], true⟩
      | _ => false
  , red "no call" "at another title the host holds the call of `insert`" ["milk"] fun
      | [milk] => (observe milk).calls == [("TodoRepo.insert", .str "milk")]
      | _ => false
    -- a failure of the repository leaves `complete` unchanged
  , green "escape" "the applied failure of the repository is the root's exit, in a settled run"
      ["locked"] fun
      | [locked] =>
        let failure : ExitV := .failure (Cause.fail (.tagged "SqlError" "locked"))
        (observe locked).outcome == some failure && (observe locked).applied == [failure] &&
          (observe locked).settled
      | _ => false
  , red "escape" "a failure under a tag that the error column does not hold is refused, and no \
      reply is applied" ["other-tag"] fun
      | [other] => (observe other).outcome == none && (observe other).applied == [] &&
          (observe other).refusals == [("submit", .envelope), ("apply", .noCall)]
      | _ => false
    -- a script's run replays from its journal
  , green "journal" "the journal alone reaches the scripted run again, verdict for verdict"
      ["done"] fun
      | [done] => observe ((openedOf done).play done.journal) == observe done &&
          ((openedOf done).play done.journal).phases == done.phases
      | _ => false
  , red "journal" "a journal that drops the reply application reaches another run" ["done"] fun
      | [done] => observe ((openedOf done).play (done.journal.eraseIdx 3)) != observe done
      | _ => false
    -- a stored successful reply fits its row
  , green "admission" "the exact record is stored and applied: no row is refused" ["done"] fun
      | [done] => (observe done).refusals == [] &&
          (observe done).outcome == some (.success (todo 1 "milk" true))
      | _ => false
  , red "admission" "a wider record is refused at the reply receipt, and the root does not move"
      ["wide"] fun
      | [wide] => (observe wide).outcome == none &&
          (observe wide).refusals == [("submit", .envelope), ("apply", .noCall)]
      | _ => false ]

/-- The runs and the controls, from one build of each entry at its argument. An entry that does
not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  match builtAt "add" [str ""], builtAt "add" [str "milk"], builtAt "complete" [nat 1] with
  | some empty, some milk, some done => (runsOf empty milk done, controlsOf)
  | _, _, _ => ([], [green "no call" "the entries build" [] fun _ => false])

/-! ## 4. The record -/

/-- The to-do application's record. The scenario's program is the application. -/
def claimRecord : Record :=
  { application := ``application
    programs := application.entryNames
    scenario :=
      { name := "todo"
        program := ``application
        observation := ``observe
        claim := ``serves
        clauses :=
          [ ⟨"no call", ``add_empty_calls_nothing⟩
          , ⟨"escape", ``complete_failure_escapes⟩ ]
        laws :=
          [ ⟨"journal", ``replays⟩
          , ⟨"admission", ``Effect4.Api.HostSession.submit_success_prepared_fits⟩ ]
        runs := runsAndControls.1
        controls := runsAndControls.2 }
    notes :=
      [ { entry := "no call", kind := .tree, reads := ["add"] }
      , { entry := "escape", kind := .tree, reads := ["complete"] }
      , { entry := "journal", kind := .inherited }
      , { entry := "admission", kind := .inherited } ] }

/-- The record's scenario, under a name that the scenario gate takes. -/
def scenario : Scenario := claimRecord.scenario

-- finite evaluation: the record's notes are right as data
#guard claimRecord.problems = []

#scenario_gate scenario

/-! ## 5. Red controls of the notes

Each record below changes one thing of `claimRecord`, and `Record.problems` names exactly that
finding. -/

/-- A record with each note changed by `change`. -/
def withNotes (change : List Note → List Note) : Record :=
  { claimRecord with notes := change claimRecord.notes }

/-- A record whose note of `entry` is changed by `change`. -/
def withNote (entry : String) (change : Note → Note) : Record :=
  withNotes (·.map fun note => if note.entry == entry then change note else note)

-- control: an entry with no note, an entry with two notes, a note that names no clause and no law
#guard (withNotes (·.drop 1)).problems.length = 1
#guard (withNotes (· ++ [{ entry := "journal", kind := .inherited }])).problems.length = 1
#guard (withNotes (· ++ [{ entry := "nowhere", kind := .run }])).problems.length = 1
-- control: a note that reads a program the application does not hold
#guard (withNote "escape" ({ · with reads := ["purge"] })).problems.length = 1
-- control: a fact of the call tree that names a premise, and an inherited law that names one
#guard ["no call", "journal"].all fun entry =>
  (withNote entry ({ · with assumes := [⟨``application, .assumed⟩] })).problems.length = 1
-- control: a fact under a promise that assumes nothing
#guard (withNote "escape" ({ · with kind := .laws })).problems.length = 1

end Test.Dogfood.Scenario.Todo
