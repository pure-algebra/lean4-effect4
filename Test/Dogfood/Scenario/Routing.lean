import Test.Dogfood.Scenario.Routing.Runs
import Test.Dogfood.Scenario.Routing.Model
import Test.Dogfood.Scenario
import Test.Dogfood.P2HandlerLayers

/-!
# The routing scenario: exact handlers, and the call that must not happen

Decisions row 254. The scenario extends the consumer of `Test/Dogfood/P2HandlerLayers.lean`: its
admitted `handle` program over the two host rows. It composes four features: two nested handlers
selected by a tag, a branch on a host answer, host calls in sequence, and a typed failure that a
host answer carries.

* **Program.** `request`: p2's handler on fixed arguments. `handleOn` writes the same handler
  over any repository row and any two handler tests, so a red control changes one part. The
  instance at p2's row and tests elaborates to p2's own program (a control pins it).
* **Script.** The host answers the configuration, then each repository lookup. A script offers a
  repository answer even where the program must not ask for one. `runsOf` lists each script
  once, as a named run.
* **Observation.** `Observation`, three fields: the exact response or the failure that escapes,
  the repository's calls, and the refused rows with the session's reason.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads.
* **Lowered runs.** The program prints and reads back (`Test/Dogfood/Scenario/Faces.lean`). The
  host lane and the engine's lane take their scripts from `runsOf`: the keyed lane performs each
  named run that a host can perform, and `Test/Dogfood/Scenario/TapeData.lean` names the runs of the
  engine's fixture.

Two findings stand in the controls. The repository row's error column is a pair of strings, so a
host failure that wears a business tag is routed as that business failure. With the exact column,
the session refuses that reply. Each run is a finite probe: one script on the Lean machine.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Agreement Effect4.Program.Denote
open Test.Dogfood.P2HandlerLayers (getConfig findById response userTy recordVal user caseModule)

/-! ## 1. The runs and the controls -/

/-- A `Response` value, and a tagged failure at the root. -/
def responded (status : Nat) (body : String) : Option ExitV :=
  some (.success (recordVal ["status", "body"] [.nat status, .str body]))
def escaped (tag message : String) : Option ExitV :=
  some (.failure (Cause.fail (.tagged tag message)))

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. -/
def controlsOf : List Control :=
  [ -- each handler catches only its named failure
    green "exact" "the three requests of run-p2.ts get rc.112's three responses"
      ["200", "404", "401"] fun
      | [served, missing, denied] =>
        shows served ⟨responded 200 "bob", [.nat 1, .nat 2], []⟩ &&
          shows missing ⟨responded 404 "no user 9", [.nat 1, .nat 9], []⟩ &&
          shows denied ⟨responded 401 "bad token", [], []⟩
      | _ => false
  , red "exact" "a handler that names another tag lets the business failure escape"
      ["misnamed"] fun
      | [misnamed] => shows misnamed ⟨escaped "Unauthorized" "bad token", [], []⟩
      | _ => false
  , red "exact" "a handler that catches every failure answers 401 to an infrastructure failure"
      ["catch-all"] fun
      | [caught] => shows caught ⟨responded 401 "connection lost", [.nat 1], []⟩
      | _ => false
    -- an infrastructure failure escapes the business handlers
  , green "escape" "a repository failure with another tag reaches the root unchanged"
      ["escape"] fun
      | [escaping] => shows escaping ⟨escaped "SqlError" "connection lost", [.nat 1], []⟩
      | _ => false
  , red "escape" "a repository failure that wears a business tag is routed as that failure"
      ["business-tag"] fun
      | [tagged] => shows tagged ⟨responded 404 "no user db", [.nat 1], []⟩
      | _ => false
  , red "escape" "with the exact error column the session refuses the business tag"
      ["exact-business-tag", "exact-escape"] fun
      | [tagged, escaping] =>
        shows tagged ⟨none, [.nat 1], [("submit", .envelope), ("apply", .noCall)]⟩ &&
          shows escaping ⟨escaped "SqlError" "connection lost", [.nat 1], []⟩
      | _ => false
    -- an unauthorized request makes no call of the repository
  , green "no call" "a request with a wrong token holds no repository call, though offered"
      ["401"] fun
      | [denied] => shows denied ⟨responded 401 "bad token", [], []⟩
      | _ => false
  , red "no call" "a handler that looks the caller up first calls the repository" ["eager"] fun
      | [eager] =>
        shows eager
          ⟨responded 401 "bad token", [.nat 1], [("submit", .noCall), ("apply", .noCall)]⟩
      | _ => false
    -- a stored successful reply fits its row
  , green "admission" "the exact records are stored and applied: no row is refused" ["200"] fun
      | [served] => shows served ⟨responded 200 "bob", [.nat 1, .nat 2], []⟩
      | _ => false
  , red "admission" "a wider record is refused at the reply receipt, and the root does not move"
      ["wide"] fun
      | [widened] => shows widened ⟨none, [.nat 1], [("submit", .envelope), ("apply", .noCall)]⟩
      | _ => false ]

/-- The scenario's runs and its controls, from one build of each program. The first control pins
that the scenario's program is p2's own. A program that does not build leaves no run and one
failing control. -/
def runsAndControls : List NamedRun × List Control :=
  match builtInputs with
  | some (bob, _missing, _denied, _misnamed, _catchAll, _eager, _exact, p2) => (runSet.runs, green "exact" "the scenario's program is p2's own handler" []
        (fun _ => decide (bob.program = p2.program)) :: controlsOf)
  | none => ([], [green "exact" "the handler and its variants build" [] fun _ => false])

/-! ## 2. The record -/

/-- The routing scenario. The claim assembles the three clauses. The session's law of a stored
successful reply is an associated law: the record claims no dependency of `routing` on it. The
registry places it by its module, a default module of `host-session-protocol`. -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``request
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.Routing

