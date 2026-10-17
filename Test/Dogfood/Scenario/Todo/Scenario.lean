import Test.Dogfood.Scenario.Todo.Runs
import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Todo.Entries
import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Validated

/-!
# The to-do application's scenario

The application of `Test/Dogfood/Scenario/Todo.lean` as a scenario: its observation, its named
runs and its controls. The host lane performs its runs on rc.112
(`harness/truth/session/Keyed.lean`). Decisions row 410 retired its claims and their proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote (ReplyTape denoteRows)
open Effect4.Run (appliedExits hostDriven conforms agrees)
open Test.Dogfood.P2HandlerLayers (recordVal)

/-! ## 1. The observation, the named runs and the controls -/

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
  match builtInputs with
  | some (_empty, _milk, _done, _listed) => (runSet.runs, controlsOf)
  | none => ([], [green "no call" "the entries build" [] fun _ => false])

/-! ## 2. The record -/

/-- The to-do application's scenario: the application, its observation, its named runs and its
controls, which the host lane performs (`harness/truth/session/Keyed.lean`). -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``application
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.Todo

