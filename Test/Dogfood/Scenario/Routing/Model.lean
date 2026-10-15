import Test.Dogfood.Scenario.Data
import Test.Dogfood.P2HandlerLayers.Data

/-!
# The routing scenario's program and observation

The source, scripts and propositions are extracted unchanged for the proof modules.
The claims and their finite controls remain in `Scenario/Routing.lean`.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (getConfig findById response userTy recordVal user caseModule)

/-! ## 1. The program -/

/-- `catchTag(tag, …)`'s test: `catchIf` over `tagIs`. -/
def named (tag : String) (e : TermSrc) : TermSrc := app "tagIs" [str tag, e]

/-- p2's `findOrFail` over a repository row. -/
def findOrFail (find : RowDef) (id idText : TermSrc) : Src NativeOp :=
  bindName "found" (Row.call find id) fun found =>
    selectOption "user" found
      (fail (app "pair" [str "NotFound", idText]))
      (succeed (var "user"))

/-- p2's `getProfile` over a repository row. -/
def getProfile (find : RowDef) (me id idText : TermSrc) : Src NativeOp :=
  ifElse (app "and" [app "not" [app "eq" [field me "role", str "admin"]],
                     app "not" [app "eq" [field me "id", id]]])
    (fail (app "pair" [str "Unauthorized", str "not yours"]))
    (findOrFail find id idText)

/-- p2's `withAuth` over a repository row. With `eager`, the program looks the caller up before
it checks the token: the fault of the red control "a call that must not happen". -/
def withAuth (eager : Bool) (find : RowDef) (token id idText : TermSrc) : Src NativeOp :=
  bindName "config" (Row.call getConfig unit) fun config =>
    if eager then
      bindName "me" (findOrFail find (nat 1) (str "1")) fun me =>
        ifElse (app "not" [app "eq" [token, field config "adminToken"]])
          (fail (app "pair" [str "Unauthorized", str "bad token"]))
          (getProfile find me id idText)
    else
      ifElse (app "not" [app "eq" [token, field config "adminToken"]])
        (fail (app "pair" [str "Unauthorized", str "bad token"]))
        (bindName "me" (findOrFail find (nat 1) (str "1")) fun me =>
          getProfile find me id idText)

/-- p2's `handle` over a repository row and two handler tests. -/
def handleOn (eager : Bool) (find : RowDef) (notFound unauthorized : TermSrc → TermSrc)
    (token id idText : TermSrc) : Src NativeOp :=
  catchIf "e" (notFound (var "e"))
    (catchIf "e2" (unauthorized (var "e2"))
      (bindName "user" (withAuth eager find token id idText) fun user =>
        succeed (response (nat 200) (field user "name")))
      (succeed (response (nat 401) (app "snd" [var "e2"]))))
    (succeed (response (nat 404) (app "concat" [str "no user ", app "snd" [var "e"]])))

/-- One request as a module, with every part a parameter. -/
def routed (eager : Bool) (find : RowDef) (notFound unauthorized : TermSrc → TermSrc)
    (token : String) (id : Nat) (idText : String) : Module NativeOp :=
  { rows := [getConfig, find]
    main := handleOn eager find notFound unauthorized (str token) (nat id) (str idText) }

/-- The scenario's program: p2's handler on its own row, with its own two tests. -/
def request (token : String) (id : Nat) (idText : String) : Module NativeOp :=
  routed false findById (named "NotFound") (named "Unauthorized") token id idText

/-- The repository row with its exact error column: rc.112's two infrastructure failures. -/
def findByIdExact : RowDef :=
  Row.host "UserRepo.findById" .nat (.option userTy)
    (.union (.prod (.lit "SqlError") .string) (.prod (.lit "SchemaError") .string))
    "p2-handler-layers.ts:58-70"

/-! ## 2. The scripts -/

/-- The two rows, as a script names them. -/
def cfg : Sel := .row "AppConfig.get"
def repo : Sel := .row "UserRepo.findById"

/-- The configuration `run-p2.ts` loads, with a given token. -/
def configOf (token : String) (pageSize : Nat) : Val :=
  recordVal ["adminToken", "pageSize"] [.str token, .nat pageSize]

/-- The repository's answer for a user id: the decoded record, or nothing. -/
def found (id : Nat) : Val := (user id).elim .none .some

/-- The host answers the configuration, then two lookups: the caller's and the requested user's.
The script offers both lookups whatever the program asks. -/
def lookups (id : Nat) : List Move :=
  script [[.start], answer cfg (ok (configOf "secret" 20)), answer repo (ok (found 1)),
    answer repo (ok (found id))]

/-- The host answers the configuration, and fails the first lookup with a tag and a message. -/
def failing (tag message : String) : List Move :=
  script [[.start], answer cfg (ok (configOf "secret" 20)), answer repo (failed tag message)]

/-- A built program opened under the scenario's name, at the default budgets. -/
def opened (b : Api.Built) : Run := Run.open b "routing"

/-! ## 3. The observation -/

/-- The scenario's one observation. -/
structure Observation where
  /-- The exact response, or the failure that escapes: the root's exit. -/
  outcome : Option ExitV
  /-- The repository's calls: the request of each `UserRepo.findById` call the host held. -/
  repositoryCalls : List Val
  /-- The refused rows, each with the session's reason. -/
  refusals : List (String × Api.HostSession.Refusal)
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { outcome := s.exit, repositoryCalls := requestsOn s "UserRepo.findById", refusals := refusals s }

/-- The machine's part of the observation: the root's exit and the calls the machine waits on.
The held calls and the refused rows are the session's. -/
def machineView (s : Run) : Option ExitV × List Await := (s.exit, s.outstanding)

/-- The proposition of `infrastructure_escapes`. -/
def InfrastructureEscapes : Prop :=
  ∀ (id : Nat) (idText tag message : String) (b : Api.Built),
    Effect4.Api.Author.build (request "secret" id idText) = .ok b →
    tag ≠ "NotFound" → tag ≠ "Unauthorized" →
    (observe (Scenario.play (opened b) (failing tag message))).outcome =
      some (.failure (Cause.fail (.tagged tag message)))

/-- The proposition of `unauthorized_calls_nothing`. -/
def UnauthorizedCallsNothing : Prop :=
  ∀ (token : String) (id : Nat) (idText : String) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (request token id idText) = .ok b →
    (∀ reply pageSize, Effect4.Api.Runner.Command.submit reply ∈
        (Scenario.play (opened b) moves).journal →
      reply.completion ≠ ok (configOf token pageSize)) →
    (observe (Scenario.play (opened b) moves)).repositoryCalls = []

end Test.Dogfood.Scenario.Routing
