import Test.Dogfood.Scenario.Routing.Model

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (getConfig findById response userTy recordVal user caseModule)

/-- A user row with a column the type does not name, as a row decoder hands a wider row on. -/
def wide : Val :=
  .some (recordVal ["id", "name", "role", "createdAt"] [.nat 1, .str "ada", .str "admin", .nat 0])

/-- The scenario's named runs: each script of a control, once, from one build of each program.
The first six are on the scenario's own program `request`. The others are on the variants of the
red controls. The host lane performs them in this order. -/
def runsOf (bob missing denied misnamed catchAll eager exact : Api.Built) : List NamedRun :=
  [ ⟨"200", opened bob, lookups 2⟩
  , ⟨"404", opened missing, lookups 9⟩
  , ⟨"401", opened denied, lookups 2⟩
  , ⟨"escape", opened bob, failing "SqlError" "connection lost"⟩
  , ⟨"business-tag", opened bob, failing "NotFound" "db"⟩
  , ⟨"wide", opened bob,
      script [[.start], answer cfg (ok (configOf "secret" 20)), answer repo (ok wide)]⟩
  , ⟨"misnamed", opened misnamed, lookups 2⟩
  , ⟨"catch-all", opened catchAll, failing "SqlError" "connection lost"⟩
  , ⟨"eager", opened eager, lookups 2⟩
  , ⟨"exact-business-tag", opened exact, failing "NotFound" "db"⟩
  , ⟨"exact-escape", opened exact, failing "SqlError" "connection lost"⟩ ]


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built) := do
  let build := fun (m : Module NativeOp) => (Effect4.Api.Author.build m).toOption
  let bob ← build (request "secret" 2 "2")
  let missing ← build (request "secret" 9 "9")
  let denied ← build (request "wrong" 2 "2")
  let misnamed ← build (routed false findById (named "NotFound") (named "Unauthorised") "wrong" 2 "2")
  let catchAll ← build (routed false findById (named "NotFound") (fun _ => bool true) "secret" 2 "2")
  let eager ← build (routed true findById (named "NotFound") (named "Unauthorized") "wrong" 2 "2")
  let exact ← build (routed false findByIdExact (named "NotFound") (named "Unauthorized") "secret" 2 "2")
  let p2 ← build (caseModule "secret" 2 "2")
  pure (bob, missing, denied, misnamed, catchAll, eager, exact, p2)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "routing"
    runs := match builtInputs with
      | some (bob, missing, denied, misnamed, catchAll, eager, exact, _p2) => runsOf bob missing denied misnamed catchAll eager exact
      | none => [] }

end Test.Dogfood.Scenario.Routing
