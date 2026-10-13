import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Application
import Test.Audit.ScenarioGate
import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Validated

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
open Effect4.Run (appliedExits hostDriven conforms agrees)
open Test.Dogfood.P2HandlerLayers (recordVal)
open Test.Dogfood.Application (Kind Grade Premise Note Record)

/-! ## 1. Two facts of the call tree -/

/-- A recorded run of an entry at its arguments that meets the premises of the host's meaning
(`denoteRows_eq_session_host`): reached by the driver, funded, at rest and driven by a host. -/
def SettledRun (name : String) (args : List TermSrc) (s : Run) : Prop :=
  Run.Reached s ∧ builtAt name args = some s.built ∧ funded s = true ∧ atRest s = true ∧
    hostDriven s = true

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
  ∀ (id : Nat) (s : Run) (cause : CauseV), SettledRun "complete" [nat id] s →
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

/-! ## 2. A fact under a protocol of a row -/

/-- The proposition of `complete_answers_requested`. -/
def CompleteAnswersRequested : Prop :=
  ∀ (id : Nat) (s : Run) (answer : Val), SettledRun "complete" [nat id] s →
    conforms protocols s = true → s.exit = some (.success answer) →
    setDoneProtocol.keeps (.list [.nat id, .bool true]) (.some answer) = true

/-- **Under the protocol of `setDone`, `complete` answers the requested to-do, marked done.** In
every recorded run of the entry `complete` that is funded, at rest, driven by a host and conforms
to the application's protocols, a successful exit keeps `setDone`'s promise at the request
`(id, true)`.

Placement: concept `host-session-protocol`; property as `add_empty_calls_nothing`. Question:
this planned goal; consumer: the claim `serves`. Reach: the entry `complete` at every id, every
such run. The premise `conforms` is validated on the run's own tape (`Effect4.Run.conforms`,
`src/Effect4/Laws/Program/Validated.lean`). Does not establish: that a host conforms: a typed
answer for another to-do reaches the root (a red control). Unlocks: as `add_empty_calls_nothing`.
Kind: a fact under a protocol. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal complete_answers_requested : CompleteAnswersRequested

/-! ## 3. Two facts under the laws of the rows

The laws of the repository are, today, its reference model `repository`
(`Test/Dogfood/Scenario/Todo.lean`, section 7). A claim under it reads runs that agree with it:
the model gave the runs' answers (`Effect4.Run.agrees`, decided on each run's own tape). So the
host need be no Lean function. -/

/-- The proposition of `list_after_add`. -/
def ListAfterAdd : Prop :=
  ∀ (title : String) (adding listing : Run) (start middle finish : Repo) (added : Val)
    (todos : List Val), title ≠ "" →
    SettledRun "add" [str title] adding → SettledRun "list" [] listing →
    agrees repository adding start = some middle →
    agrees repository listing middle = some finish →
    adding.exit = some (.success added) → listing.exit = some (.success (.list todos)) →
    added ∈ todos

/-- **After `add`, `list` holds the new to-do**, under the reference model. For a settled run of
`add` at a title that is not empty, then a settled run of `list`, whose answers the model gave in
turn, a successful `list` holds the to-do that `add` answered.

Placement: concept `host-session-protocol`; property as `add_empty_calls_nothing`. Question:
this planned goal; consumer: the claim `serves`. Reach: every title but the empty one, every
start state of the model, every such pair of runs. The premise `agrees` is validated on each run.
Does not establish: that a host agrees with the model (a red control: a host that forgets); that
the runs finish (progress). Unlocks: as `add_empty_calls_nothing`. Kind: a fact under the laws of
the rows. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal list_after_add : ListAfterAdd

/-- The proposition of `complete_idempotent`. -/
def CompleteIdempotent : Prop :=
  ∀ (id : Nat) (once twice : Run) (start middle finish : Repo) (first second : ExitV),
    SettledRun "complete" [nat id] once → SettledRun "complete" [nat id] twice →
    agrees repository once start = some middle → agrees repository twice middle = some finish →
    once.exit = some first → twice.exit = some second →
    second = first ∧ finish = middle

/-- **`complete` twice leaves what `complete` once leaves**, under the reference model. For two
settled runs of `complete` at one id, whose answers the model gave in turn, the second exit is the
first, and the second run leaves the model's state where the first left it.

Placement: as `list_after_add`. Reach: every id, every start state of the model, every such pair
of runs. Does not establish: that a host agrees with the model (a red control: a host whose
`setDone` flips the flag); progress. Kind: a fact under the laws of the rows. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal complete_idempotent : CompleteIdempotent

/-! ## 4. The claim -/

/-- **The to-do application's claim.** It assembles its clauses, and the plan derives its status
from their proofs. Two laws stand beside it with controls only: a script's run replays from its
journal (`replays`), and a stored successful reply fits its row
(`Effect4.Api.HostSession.submit_success_prepared_fits`). The proof uses neither. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serves :
    AddEmptyCallsNothing ∧ CompleteFailureEscapes ∧ CompleteAnswersRequested ∧
      ListAfterAdd ∧ CompleteIdempotent :=
  ⟨add_empty_calls_nothing, complete_failure_escapes, complete_answers_requested,
    list_after_add, complete_idempotent⟩

/-! ## 5. The observation, the named runs and the controls -/

/-- The application's one observation of a run: the root's exit, the calls that the host held,
the refused rows, the exits of the applied replies, whether the run meets the premises of
`denoteRows_eq_session` (funded, at rest, driven by a host), and whether it conforms to the
application's protocols. -/
structure Observation where
  outcome : Option ExitV
  calls : List (String × Val)
  refusals : List (String × Api.HostSession.Refusal)
  applied : ReplyTape
  settled : Bool
  conforming : Bool
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { outcome := s.exit, calls := (held s).map fun call => (call.row, call.request)
    refusals := refusals s, applied := appliedExits s
    settled := funded s && atRest s && hostDriven s, conforming := conforms protocols s }

/-- A built entry, opened under the application's name. -/
def opened (b : Api.Built) : Run := Run.open b application.name

/-- The script that fails the one call of `complete` with the repository's tag. -/
def repoFails (message : String) : List Move :=
  script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" message)]

/-- The failure of an empty title, at the root. -/
def emptyTitleExit : ExitV := .failure (Cause.fail (.tagged "EmptyTitle" "a title is required"))

/-- A host that forgets what it stores: it answers as the model and keeps its state. The red
control of "after add". -/
def forgetful : Run.Reactor Repo := fun row request s =>
  (repository row request s).map fun step => (step.1, s)

/-- A host whose `setDone` flips the stored flag: the red control of "idempotent". -/
def toggling : Run.Reactor Repo := fun row request s =>
  match row.spelling, request with
  | "TodoRepo.setDone", .list [.nat id, .bool _] =>
    match s.2.find? (·.1 == id) with
    | some t =>
      some (ok (.some (todo id t.2.1 !t.2.2)),
        (s.1, s.2.map fun u => if u.1 == id then (u.1, u.2.1, !u.2.2) else u))
    | none => some (ok .none, s)
  | _, _ => repository row request s

/-- A run of a built entry driven by a host as a function (`Run.runWith`), as a named run: its
journal holds the host's rows, so the run replays with no host. -/
def drivenRun {σ : Type} (name : String) (b : Api.Built) (host : Run.Reactor σ) (st : σ) :
    NamedRun :=
  ⟨name, opened b, (Run.runWith b host st application.name).1.journal.map .wire⟩

/-- The host's state after it drives a run of a built entry. -/
def drivenState {σ : Type} (b : Api.Built) (host : Run.Reactor σ) (st : σ) : σ :=
  (Run.runWith b host st application.name).2

/-- The model's state where the runs under a host start: one to-do stored. -/
def stocked : Repo := (2, [(1, "milk", false)])

/-- The named runs: each script once, from one build of each entry at its argument. -/
def runsOf (empty milk done listed : Api.Built) : List NamedRun :=
  [ ⟨"empty", opened empty,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))]⟩
  , ⟨"milk", opened milk,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))]⟩
  , ⟨"locked", opened done, repoFails "locked"⟩
  , ⟨"other-tag", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (failed "Timeout" "slow")]⟩
  , ⟨"done", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true)))]⟩
  , ⟨"other-todo", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 2 "tea" true)))]⟩
  , ⟨"wide", opened done,
      script [[.start], answer (.row "TodoRepo.setDone")
        (ok (.some (recordVal ["id", "title", "done", "at"]
          [.nat 1, .str "milk", .bool true, .nat 0])))]⟩
  , drivenRun "model-add" milk repository (1, [])
  , drivenRun "model-list" listed repository (drivenState milk repository (1, []))
  , drivenRun "forgetful-add" milk forgetful (1, [])
  , drivenRun "forgetful-list" listed forgetful (drivenState milk forgetful (1, []))
  , drivenRun "model-once" done repository stocked
  , drivenRun "model-twice" done repository (drivenState done repository stocked)
  , drivenRun "toggling-once" done toggling stocked
  , drivenRun "toggling-twice" done toggling (drivenState done toggling stocked) ]

/-- The controls: for each clause and each law a green control and at least one red control. -/
def controlsOf : List Control :=
  [ -- `add` with an empty title makes no call
    green "no call" "an empty title fails, and the host holds no call, though offered an answer"
      ["empty"] fun
      | [empty] => observe empty == ⟨some emptyTitleExit, [], [], [], true, true⟩
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
    -- under the protocol of `setDone`, `complete` answers the requested to-do, marked done
  , green "requested" "a settled run that conforms answers the requested to-do, marked done"
      ["done"] fun
      | [done] => (observe done).outcome == some (.success (todo 1 "milk" true)) &&
          (observe done).settled && (observe done).conforming
      | _ => false
  , red "requested" "a typed answer for another to-do reaches the root, and the run does not \
      conform" ["other-todo"] fun
      | [other] => (observe other).outcome == some (.success (todo 2 "tea" true)) &&
          (observe other).refusals == [] && (observe other).settled &&
          !(observe other).conforming
      | _ => false
    -- after `add`, `list` holds the new to-do
  , green "after add" "under the model, `list` after `add` holds the added to-do, and both runs \
      agree with the model" ["model-add", "model-list"] fun
      | [added, listed] =>
        (observe added).outcome == some (.success (todo 1 "milk" false)) &&
          (observe listed).outcome == some (.success (.list [todo 1 "milk" false])) &&
          (observe added).settled && (observe listed).settled &&
          ((agrees repository added (1, [])).bind (agrees repository listed)).isSome
      | _ => false
  , red "after add" "a host that forgets answers `list` with nothing, and its runs do not agree \
      with the model" ["forgetful-add", "forgetful-list"] fun
      | [added, listed] => (observe listed).outcome == some (.success (.list [])) &&
          ((agrees repository added (1, [])).bind (agrees repository listed)).isNone
      | _ => false
    -- `complete` twice leaves what `complete` once leaves
  , green "idempotent" "under the model the second `complete` answers what the first answered, \
      and leaves the model's state" ["model-once", "model-twice"] fun
      | [once, twice] =>
        (observe once).outcome == some (.success (todo 1 "milk" true)) &&
          (observe twice).outcome == (observe once).outcome &&
          (match agrees repository once stocked with
           | some middle => agrees repository twice middle == some middle
           | none => false)
      | _ => false
  , red "idempotent" "a host whose `setDone` flips the flag answers otherwise the second time, \
      and its runs do not agree with the model" ["toggling-once", "toggling-twice"] fun
      | [once, twice] => (observe once).outcome != (observe twice).outcome &&
          ((agrees repository once stocked).bind (agrees repository twice)).isNone
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
  match builtAt "add" [str ""], builtAt "add" [str "milk"], builtAt "complete" [nat 1],
    builtAt "list" [] with
  | some empty, some milk, some done, some listed => (runsOf empty milk done listed, controlsOf)
  | _, _, _, _ => ([], [green "no call" "the entries build" [] fun _ => false])

/-! ## 6. The record -/

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
          , ⟨"escape", ``complete_failure_escapes⟩
          , ⟨"requested", ``complete_answers_requested⟩
          , ⟨"after add", ``list_after_add⟩
          , ⟨"idempotent", ``complete_idempotent⟩ ]
        laws :=
          [ ⟨"journal", ``replays⟩
          , ⟨"admission", ``Effect4.Api.HostSession.submit_success_prepared_fits⟩ ]
        runs := runsAndControls.1
        controls := runsAndControls.2 }
    notes :=
      [ { entry := "no call", kind := .tree, reads := ["add"] }
      , { entry := "escape", kind := .tree, reads := ["complete"] }
      , { entry := "requested", kind := .protocol, reads := ["complete"],
          assumes := [⟨``protocols, .validated⟩] }
      , { entry := "after add", kind := .laws, reads := ["add", "list"],
          assumes := [⟨``repository, .validated⟩] }
      , { entry := "idempotent", kind := .laws, reads := ["complete"],
          assumes := [⟨``repository, .validated⟩] }
      , { entry := "journal", kind := .inherited }
      , { entry := "admission", kind := .inherited } ] }

/-- The record's scenario, under a name that the scenario gate takes. -/
def scenario : Scenario := claimRecord.scenario

-- finite evaluation: the record's notes are right as data
#guard claimRecord.problems = []

#scenario_gate scenario

/-! ## 7. Red controls of the notes

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
#guard (withNote "requested" ({ · with assumes := [] })).problems.length = 1

end Test.Dogfood.Scenario.Todo
