import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Todo.Tree
import Test.Dogfood.Application
import Test.Audit.ScenarioGate
import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Validated

/-!
# The to-do application's claims and their record

The claims packet's slices RECORD to TREE (`docs/research/2026-10-07-packet-application-claims.md`;
decisions rows 307 (9) and 336 (9)), on the application of `Test/Dogfood/Scenario/Todo.lean`.

* **The claims.** Each clause is a theorem with its placement. `serves` assembles them, and the
  plan derives its status (`#plan_status`): it rests on one planned goal of the law graph,
  `Effect4.Run.CallTree.request_leads`, through `add_empty_calls_nothing`.
* **Each statement is the session form of a fact of the call tree.** It reads a recorded run of a
  built entry: every run that the driver reaches (`Run.Reached`), not only the scripts below. A
  statement that reads the exit takes the premises of `denoteRows_eq_session`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`): the run is funded, at rest and driven by a host.
  Each proof reads the tree form (`Test/Dogfood/Scenario/Todo/Tree.lean`) on the run through a
  theorem of the session's meaning (the packet's slice TREE).
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
open Effect4.Program.Denote (ReplyTape denoteRows)
open Effect4.Run (appliedExits hostDriven conforms agrees)
open Test.Dogfood.P2HandlerLayers (recordVal)
open Test.Dogfood.Application (Kind Evidence Premise Note Record)

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
the session, read at one program. Question: a clause of the claim `serves`, its consumer.
Reach: the entry `add` at the empty title, every run the driver reaches from its build, every
budget. Does not establish: what `add` calls at another title; anything of a lowered run.
Unlocks: R6's guarantee for a program with host rows, at one program (row 99). Kind: a fact of
the call tree.

Proof: the tree of `add` at the empty title is one leaf (`add_empty_tree`), so it waits at no call
under any tape (`add_empty_waits_nothing`), and a held call is a wait of the tree
(`Routing.Calls.held_in_tree`, over `bound_in_tree`, which rests on the planned goal
`request_leads`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem add_empty_calls_nothing : AddEmptyCallsNothing := by
  intro s hreach hbuilt
  obtain ⟨hprog, htable⟩ := builtAt_program hbuilt (add_elaborates "")
  cases hheld : held s with
  | nil => rfl
  | cons seen rest =>
    exfalso
    have hmem : seen ∈ held s := by
      rw [hheld]
      exact List.mem_cons_self
    obtain ⟨i, row, T, -, -, -, hwait⟩ := Routing.Calls.held_in_tree s hreach
      (by rw [hprog, htable]; exact add_straight "") (by rw [hprog]; exact add_noCause "")
      (by rw [hprog]; exact add_externalOnly "") (by rw [htable]; exact table_concrete) seen hmem
    rw [hprog, htable, add_empty_waits_nothing] at hwait
    cases hwait

/-- The proposition of `complete_failure_escapes`. -/
def CompleteFailureEscapes : Prop :=
  ∀ (id : Nat) (s : Run) (cause : CauseV), SettledRun "complete" [nat id] s →
    (appliedExits s).head? = some (.failure cause) → s.exit = some (.failure cause)

/-- **A failure of the repository leaves `complete` unchanged.** In every recorded run of the
entry `complete` that is funded, at rest and driven by a host, where the first applied reply is a
failure, the root fails with that failure.

Placement: concept `host-session-protocol`; property as `add_empty_calls_nothing`. Question:
a clause of the claim `serves`, its consumer. Reach: the entry `complete` at every id, every
cause, every such run. Does not establish: which failures the session applies (reply admission
refuses one outside the row's error column: a red control); a run with an interruption, a clock
step or a delayed cell read, where the premises fail. Unlocks: as `add_empty_calls_nothing`.
Kind: a fact of the call tree.

Proof: the meaning under the run's reply tape is the run's observation (`denoteRows_eq_session`),
and under a tape that starts with a failure the tree of `complete` ends at that failure
(`complete_failure_meaning`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem complete_failure_escapes : CompleteFailureEscapes := by
  intro id s cause ⟨hreach, hbuilt, hfund, hrest, hhost⟩ hhead
  obtain ⟨hprog, htable⟩ := builtAt_program hbuilt (complete_elaborates id)
  have hmean := Effect4.Run.denoteRows_eq_session s hreach hfund hrest hhost
    (by rw [hprog, htable]; exact complete_straight id)
  obtain ⟨rest, htape⟩ : ∃ rest, appliedExits s = .failure cause :: rest := by
    cases h : appliedExits s with
    | nil =>
      rw [h] at hhead
      cases hhead
    | cons x rest =>
      rw [h, List.head?_cons, Option.some.injEq] at hhead
      exact ⟨rest, by rw [hhead]⟩
  rw [htape, hprog, htable, complete_failure_meaning id cause rest] at hmean
  cases hexit : s.exit with
  | none =>
    rw [hexit] at hmean
    cases hmean
  | some ex =>
    rw [hexit, Option.map_some] at hmean
    simp only [Option.some.injEq, Prod.mk.injEq] at hmean
    rw [← hmean.1.1]

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
a clause of the claim `serves`, its consumer. Reach: the entry `complete` at every id, every
such run. The premise `conforms` is validated on the run's own tape (`Effect4.Run.conforms`,
`src/Effect4/Laws/Program/Validated.lean`). Does not establish: that a host conforms: a typed
answer for another to-do reaches the root (a red control). Unlocks: as `add_empty_calls_nothing`.
Kind: a fact under a protocol.

Proof: under the application's protocols the tree of `complete` meets the postcondition
`requested` (`complete_sat`), and a conforming run's exit meets every such postcondition
(`Effect4.Run.conforms_sat`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem complete_answers_requested : CompleteAnswersRequested := by
  intro id s answer ⟨hreach, hbuilt, hfund, hrest, hhost⟩ hconf hexit
  obtain ⟨hprog, htable⟩ := builtAt_program hbuilt (complete_elaborates id)
  have hsat : Effects.Program.Sat (Effect4.Run.rowsProtocol s.built.table protocols)
      (requested id) (denoteRows s.built.table s.built.program []) := by
    rw [hprog, htable]
    exact complete_sat id
  exact Effect4.Run.conforms_sat protocols s hreach hfund hrest hhost
    (by rw [hprog, htable]; exact complete_straight id) hconf hsat (.success answer) hexit answer
    rfl

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
a clause of the claim `serves`, its consumer. Reach: every title but the empty one, every
start state of the model, every such pair of runs. The premise `agrees` is validated on each run.
Does not establish: that a host agrees with the model (a red control: a host that forgets); that
the runs finish (progress). Unlocks: as `add_empty_calls_nothing`. Kind: a fact under the laws of
the rows.

Proof: a run that agrees with the model is a run of its call tree under the model
(`Effect4.Run.agrees_hostRun`). Under the model, `add` stores the to-do under the next id and
answers it (`add_on_model`), and `list` answers the stored to-dos (`list_on_model`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem list_after_add : ListAfterAdd := by
  intro title adding listing start middle finish added todos hne
    ⟨hr1, hb1, hf1, ha1, hh1⟩ ⟨hr2, hb2, hf2, ha2, hh2⟩ hag1 hag2 hex1 hex2
  obtain ⟨hp1, ht1⟩ := builtAt_program hb1 (add_elaborates title)
  obtain ⟨hp2, ht2⟩ := builtAt_program hb2 list_elaborates
  have hrun1 := Effect4.Run.agrees_hostRun repository adding hr1 hf1 ha1 hh1
    (by rw [hp1, ht1]; exact add_straight title) start middle hag1 _ hex1
  have hrun2 := Effect4.Run.agrees_hostRun repository listing hr2 hf2 ha2 hh2
    (by rw [hp2, ht2]; exact list_straight) middle finish hag2 _ hex2
  rw [hp1, ht1, add_on_model title hne start] at hrun1
  rw [hp2, ht2, list_on_model middle] at hrun2
  simp only [Option.some.injEq, Prod.mk.injEq, Exit.success.injEq] at hrun1 hrun2
  obtain ⟨hadded, -, hmiddle⟩ := hrun1
  obtain ⟨htodos, -, -⟩ := hrun2
  subst hadded hmiddle
  injection htodos with hlist
  rw [← hlist]
  exact List.mem_map.mpr
    ⟨(start.1, title, false), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

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
`setDone` flips the flag); progress. Kind: a fact under the laws of the rows.

Proof: by `Effect4.Run.agrees_hostRun`, each run is a run of the tree of `complete` under the
model. Where the id is stored, the first run marks it done (`complete_on_model_found`), and the
second finds it marked (`find_markDone`) and marks nothing new (`map_markDone_idem`). Where it
is not, both runs fail alike and leave the state (`complete_on_model_missing`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem complete_idempotent : CompleteIdempotent := by
  intro id once twice start middle finish first second
    ⟨hr1, hb1, hf1, ha1, hh1⟩ ⟨hr2, hb2, hf2, ha2, hh2⟩ hag1 hag2 hex1 hex2
  obtain ⟨hp1, ht1⟩ := builtAt_program hb1 (complete_elaborates id)
  obtain ⟨hp2, ht2⟩ := builtAt_program hb2 (complete_elaborates id)
  have hrun1 := Effect4.Run.agrees_hostRun repository once hr1 hf1 ha1 hh1
    (by rw [hp1, ht1]; exact complete_straight id) start middle hag1 first hex1
  have hrun2 := Effect4.Run.agrees_hostRun repository twice hr2 hf2 ha2 hh2
    (by rw [hp2, ht2]; exact complete_straight id) middle finish hag2 second hex2
  rw [hp1, ht1] at hrun1
  rw [hp2, ht2] at hrun2
  cases hfind : start.2.find? (·.1 == id) with
  | none =>
    rw [complete_on_model_missing id start hfind] at hrun1
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun1
    obtain ⟨hfirst, -, hmiddle⟩ := hrun1
    subst hmiddle
    rw [complete_on_model_missing id start hfind] at hrun2
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun2
    obtain ⟨hsecond, -, hfinish⟩ := hrun2
    exact ⟨hsecond.symm.trans hfirst, hfinish.symm⟩
  | some entry =>
    rw [complete_on_model_found id start entry hfind] at hrun1
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun1
    obtain ⟨hfirst, -, hmiddle⟩ := hrun1
    subst hmiddle
    have hfind2 : (start.1, start.2.map (markDone id)).2.find? (·.1 == id) =
        some (markDone id entry) := by
      show (start.2.map (markDone id)).find? (·.1 == id) = _
      rw [find_markDone, hfind]
      rfl
    rw [complete_on_model_found id _ (markDone id entry) hfind2] at hrun2
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun2
    obtain ⟨hsecond, -, hfinish⟩ := hrun2
    refine ⟨?_, ?_⟩
    · rw [← hsecond, ← hfirst, markDone_title]
    · rw [← hfinish, map_markDone_idem]

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
-- finite evaluation: what the record claims of `complete`, of `remove`, and of a name that the
-- application does not hold, by kind
#guard (claimRecord.claimsOf "complete").map (fun c => (c.1, c.2.2)) =
  [("escape", .tree), ("requested", .protocol), ("idempotent", .laws), ("journal", .inherited),
    ("admission", .inherited)]
#guard (claimRecord.claimsOf "remove").map (·.1) = ["journal", "admission"] &&
  (claimRecord.claimsOf "purge").isEmpty

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
