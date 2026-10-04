import Test.Dogfood.Stage
import Effect4.Run

/-!
# p2: a request handler over layered services

The rc.112 source is `Test/Dogfood/rc112/p2-handler-layers.ts`. A `UserRepo` service runs SQL
through the client it captured, `AppConfig` reads `ADMIN_TOKEN` through `Config`, an
authentication middleware provides `CurrentUser`, and `main` provides the layer graph once.
`run-p2.ts` ran three requests on effect 4.0.0-rc.112 under bun 1.4.2 and recorded
`{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}` and
`{"status":401,"body":"bad token"}` (`Test/Dogfood/rc112/hostruns.log`).

This battery ports four encodings:

* the handler of the data probe (`git:e34b3125:docs/research/2026-10-01-data-probe/programs/ProbeTodayP2.lean`)
  and of seat R's acceptance harness
  (`git:db6ff5d7:docs/research/2026-10-01-type-language-probe/R/probes/P2RecordHarness.lean`);
* the capture control of the model probe
  (`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbePrograms345.lean`, "Program 2"),
  with the verifier's red control (`verify/VerifyPrograms.lean` §2 at the same revision);
* the carrier and payload refusals of `ProbeRefusals.lean` at the same revision.

**Changes since 2026-09-30 and 2026-10-01.**
* Records landed (rows 119, 165, 166, 195). The handler uses `Ty.record`, `Authoring.record` and
  `Authoring.field`. The 2026-10-01 harness wrote it against a `DataWave` interface whose six
  parts were all missing. Five exist today: `Ty.record`, the two term builders and the codec's
  record arm in `Schema.encode` and `Schema.decode`. The sixth, route A's row adapter, does not
  exist. So the scripted host answers the exact record, and the reply check refuses a wider one.
* The host is a `Run.Reactor` driven by `Run.runWith` (`src/Effect4/Run.lean`). The probes wrote
  the same policy by hand over `Api.HostSession`, whose `outstanding` now answers `Await` records
  (row 16).

**Bounded as seat W10's brief bounds the data wave's acceptance**
(`docs/research/2026-10-01-data-wave/brief-W10.md`): the handler only; errors are DB-15's
literal-tagged pairs; the caller threads the id's text (row 131); the host decodes (route A);
`CurrentUser` is a value, not a service (row 118). The battery encodes no layered program.

**What the language refuses** (section 6): a string or record service carrier (`AppConfig`,
`CurrentUser`), a number or record payload in a typed failure (`NotFound{id}`,
`Unauthorized{reason}`), number-to-text, and the `catchTag` form. `UserRepo`'s methods are code,
which no value holds (R7).

**Waits on:** R3 and row 120 (error payloads); R5 and R7 with rows 21, 82 and 118 (code-valued
services and structured carriers); R13 with rows 51 and 83 (`Config` at load); row 131
(number to text); row 123 (decoding inside a program); R10 with DI-39, DI-89 and row 130
(`catchTag` and its residual). The slices of row 204 that move it: error payloads (row 120), and
the derived forms beside them.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P2HandlerLayers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The data and the rows -/

/-- `role: Schema.Literals(["admin", "member"])`: a union of two string literals. -/
def roleTy : Ty := .union (.lit "admin") (.lit "member")
/-- `User = { id: number, name: string, role }`. -/
def userFields : List (String × Bool × Ty) :=
  [("id", false, .nat), ("name", false, .string), ("role", false, roleTy)]
def userTy : Ty := .record userFields
/-- `AppConfig = { adminToken: string, pageSize: number }`. -/
def configFields : List (String × Bool × Ty) := [("adminToken", false, .string), ("pageSize", false, .nat)]
def configTy : Ty := .record configFields
/-- `Response = { status: number, body: string }`. -/
def responseFields : List (String × Bool × Ty) := [("status", false, .nat), ("body", false, .string)]
def responseTy : Ty := .record responseFields
/-- `SqlError | SchemaError`, crossing as DB-15's `(tag, message)` pair. -/
def infraErrTy : Ty := .prod .string .string

/-- `AppConfigLive`'s value, read by the host. -/
def getConfig : RowDef := Row.host "AppConfig.get" .unit configTy .never "p2-handler-layers.ts:51-55"
/-- `UserRepo.findById`, with the query and `Schema.decodeUnknownEffect(User)` in the host: it
answers the decoded record or nothing, and fails with the infrastructure's pair. -/
def findById : RowDef :=
  Row.host "UserRepo.findById" .nat (.option userTy) infraErrTy "p2-handler-layers.ts:58-70"

/-! ## 2. The handler -/

def response (status body : TermSrc) : TermSrc :=
  record responseFields [("status", status), ("body", body)]

/-- `row === undefined ? fail(new NotFound({ id })) : decode(row)`, with the decode in the host.
The id's text is a parameter: no atom turns a number into text. -/
def findOrFail (id idText : TermSrc) : Src NativeOp :=
  bindName "found" (Row.call findById id) fun found =>
    selectOption "user" found
      (fail (app "pair" [str "NotFound", idText]))
      (succeed (var "user"))

/-- `getProfile(id)`: `me.role !== "admin" && me.id !== id`, with `CurrentUser` as the value `me`. -/
def getProfile (me id idText : TermSrc) : Src NativeOp :=
  ifElse (app "and" [app "not" [app "eq" [field me "role", str "admin"]],
                     app "not" [app "eq" [field me "id", id]]])
    (fail (app "pair" [str "Unauthorized", str "not yours"]))
    (findOrFail id idText)

/-- `withAuth(token, getProfile(id))`: `token !== config.adminToken`. -/
def withAuth (token id idText : TermSrc) : Src NativeOp :=
  bindName "config" (Row.call getConfig unit) fun config =>
    ifElse (app "not" [app "eq" [token, field config "adminToken"]])
      (fail (app "pair" [str "Unauthorized", str "bad token"]))
      (bindName "me" (findOrFail (nat 1) (str "1")) fun me =>
        getProfile me id idText)

/-- `handle(token, id)`: `{ status: 200, body: user.name }`, and the two tagged failures as 404 and
401 responses. `catchTag` is `catchIf` over `tagIs`. -/
def handle (token id idText : TermSrc) : Src NativeOp :=
  catchIf "e" (app "tagIs" [str "NotFound", var "e"])
    (catchIf "e2" (app "tagIs" [str "Unauthorized", var "e2"])
      (bindName "user" (withAuth token id idText) fun user =>
        succeed (response (nat 200) (field user "name")))
      (succeed (response (nat 401) (app "snd" [var "e2"]))))
    (succeed (response (nat 404) (app "concat" [str "no user ", app "snd" [var "e"]])))

/-- One request as a module: the handler on fixed arguments, with its two rows. -/
def caseModule (token : String) (id : Nat) (idText : String) : Module NativeOp :=
  { rows := [getConfig, findById], main := handle (str token) (nat id) (str idText) }

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

-- It builds: typed against its own row table and admitted.
#guard verdict (caseModule "secret" 2 "2") = "built"
-- The checked type: the answer is `Response`; the error column is the infrastructure pair alone,
-- which absorbs the program's own literal-tagged failures (rc.112's pinned error is
-- `SchemaError | SqlError | ConfigError`).
#guard (built? (caseModule "secret" 2 "2")).map (fun b => (b.ty.answer, b.ty.error)) =
  some (responseTy.normalize, infraErrTy)

/-! ## 3. The run under a scripted host -/

/-- A record value, its fields in canonical order. -/
def recordVal (names : List String) (values : List Val) : Val :=
  (Effect4.Machine.Record.build names values).getD .unit

/-- The users table of `run-p2.ts`: `(1, ada, admin)` and `(2, bob, member)`. -/
def user : Nat → Option Val
  | 1 => some (recordVal ["id", "name", "role"] [.nat 1, .str "ada", .str "admin"])
  | 2 => some (recordVal ["id", "name", "role"] [.nat 2, .str "bob", .str "member"])
  | _ => none

/-- The host: the configuration, and the repository answering each user as its exact record. -/
def host : Run.Reactor Unit := fun row request _ =>
  if row.spelling == "AppConfig.get" then
    some (.ofExit (.success (recordVal ["adminToken", "pageSize"] [.str "secret", .nat 20])), ())
  else if row.spelling == "UserRepo.findById" then
    match request with
    | .nat n => some (.ofExit (.success ((user n).elim .none .some)), ())
    | _ => none
  else none

/-- The run of one request: the root evaluated, then every call answered, flushing between rounds. -/
def runCase (m : Module NativeOp) (h : Run.Reactor Unit) : Option Run :=
  (built? m).map fun b => (Run.runWith b h ()).1

/-- The three requests of `run-p2.ts`, with rc.112's answers as `Response` values. -/
def cases : List (String × Nat × String × Val) :=
  [ ("secret", 2, "2", recordVal ["status", "body"] [.nat 200, .str "bob"])
  , ("secret", 9, "9", recordVal ["status", "body"] [.nat 404, .str "no user 9"])
  , ("wrong", 2, "2", recordVal ["status", "body"] [.nat 401, .str "bad token"]) ]

def num (n : Nat) : Json := Effect4.Arch.Json.ofNat n

/-- rc.112's answers as `hostruns.log` printed them, in its key order. -/
def rc112Json : List Json :=
  [ .obj [("status", num 200), ("body", .str "bob")]
  , .obj [("status", num 404), ("body", .str "no user 9")]
  , .obj [("status", num 401), ("body", .str "bad token")] ]

/-- Each request's root exit. -/
def exits : List (Option ExitV) :=
  cases.map fun (token, id, idText, _) =>
    (runCase (caseModule token id idText) host).bind (·.exit)

-- The three answers are rc.112's, as `Response` values.
#guard exits = cases.map fun (_, _, _, v) => some (.success v)
-- Encoded at `Response` by the codec, each equals rc.112's JSON modulo object key order (`normJ`).
#guard (exits.zip rc112Json).all fun (exit, expected) =>
  match exit with
  | some (.success v) => (Effect4.Schema.encode responseTy v).map Effect4.Schema.Codec.normJ ==
      some (Effect4.Schema.Codec.normJ expected)
  | _ => false
-- Every row of the green run was accepted: no phase is a refusal.
#guard (runCase (caseModule "secret" 2 "2") host).map (fun r =>
  r.phases.all fun | .refused _ => false | _ => true) = some true
-- The threaded text is trusted, not computed: a caller that threads the wrong text gets a wrong
-- body, and the type does not say so (row 131).
#guard ((runCase (caseModule "secret" 9 "nine") host).bind (·.exit)) =
  some (.success (recordVal ["status", "body"] [.nat 404, .str "no user nine"]))

/-! ## 4. The boundary's red controls -/

/-- A host that answers user 1 with a column the type does not name (`createdAt`), as rc.112's
row decoder hands a wider row to the program. -/
def wideHost : Run.Reactor Unit := fun row request st =>
  if row.spelling == "UserRepo.findById" && request == .nat 1 then
    some (.ofExit (.success (.some
      (recordVal ["id", "name", "role", "createdAt"] [.nat 1, .str "ada", .str "admin", .nat 0]))), st)
  else host row request st

/-- A host that answers the record in the 2026-10-01 pair spelling. -/
def pairHost : Run.Reactor Unit := fun row request st =>
  if row.spelling == "UserRepo.findById" then
    some (.ofExit (.success (.some (.list [.nat 2, .list [.str "bob", .str "member"]]))), st)
  else host row request st

/-- The refused phases of a run, in order. -/
def refusals (r : Run) : List Effect4.Api.HostSession.Refusal :=
  r.phases.filterMap fun | .refused why => some why | _ => none

-- The reply check refuses the wider record (`envelope`), so no route A adapter projects it; the
-- next row then has no call to apply, and the root has no exit.
#guard (runCase (caseModule "secret" 2 "2") wideHost).map (fun r => (r.exit.isNone, refusals r)) =
  some (true, [.envelope, .noCall])
-- The pair spelling no longer fits the record row.
#guard (runCase (caseModule "secret" 2 "2") pairHost).map (fun r => (r.exit.isNone, refusals r)) =
  some (true, [.envelope, .noCall])
-- The strict codec refuses the wider JSON object and decodes the exact one to the host's record.
def wideJson : Json := .obj [("name", .str "bob"), ("createdAt", num 0), ("id", num 2), ("role", .str "member")]
def exactJson : Json := .obj [("name", .str "bob"), ("id", num 2), ("role", .str "member")]
#guard (Effect4.Schema.decode userTy wideJson).isNone
#guard Effect4.Schema.decode userTy exactJson = user 2

/-! ## 5. Printing -/

-- The handler prints as TypeScript and reads back as itself, as an expression and as a module.
#guard (built? (caseModule "secret" 2 "2")).map (fun b => printedOf b) = some (true, true)
#guard ((built? (caseModule "secret" 2 "2")).bind fun b =>
  (Effect4.Api.printModule "handle" b.program b.table).map fun module =>
    match Effect4.Api.readModule module b.table with
    | .ok p => decide (p = b.program)
    | .error _ => false) = some true

/-! ## 6. What the language refuses -/

/-- `AppConfig` reduced to its token: a string carrier under a free name. -/
def AdminToken : ServiceDef := { key := ⟨⟨12⟩, ⟨12⟩⟩, carrier := .string }
def adminTokenModule : Module NativeOp :=
  { services := [AdminToken]
    layers := [("cfg", AdminToken.constant (str "secret"))]
    main := provide (Layer.ref "cfg") AdminToken.use }

/-- `CurrentUser`, a service whose value is the `User` record. -/
def CurrentUser : ServiceDef := { key := ⟨⟨14⟩, ⟨14⟩⟩, carrier := userTy }
def currentUserModule : Module NativeOp :=
  { services := [CurrentUser]
    main := CurrentUser.give
      (record userFields [("id", nat 1), ("name", str "ada"), ("role", str "admin")])
      CurrentUser.use }

/-- `new NotFound({ id })`: a record payload with a number. -/
def notFoundModule : Module NativeOp :=
  program (fail (record [("_tag", false, .lit "NotFound"), ("id", false, .nat)]
    [("_tag", str "NotFound"), ("id", nat 9)]))

/-- `new Unauthorized({ reason })`: a record payload with a string only. -/
def unauthorizedModule : Module NativeOp :=
  program (fail (record [("_tag", false, .lit "Unauthorized"), ("reason", false, .string)]
    [("_tag", str "Unauthorized"), ("reason", str "bad token")]))

/-- `` `no user ${e.id}` ``: a number in a template string. -/
def interpolateModule : Module NativeOp := program (succeed (app "concat" [str "no user ", nat 9]))

-- The service table types no string and no record carrier (row 118; R1's open part).
#guard verdict adminTokenModule = "serviceCarrier: signature none"
#guard verdict currentUserModule = "serviceCarrier: signature none"
-- A typed failure carries no number and no record payload (row 120, ratified, not landed).
#guard typingReason? notFoundModule = some (.errorNotAdmitted
  (.record [("_tag", false, .lit "NotFound"), ("id", false, .nat)]))
#guard verdict unauthorizedModule = "typing: errorNotAdmitted"
#guard typingReason? (program (fail (app "pair" [str "NotFound", nat 7]))) =
  some (.errorNotAdmitted (.prod (.lit "NotFound") .nat))
-- Green control: the tag with a string message types (DB-15's pair).
#guard verdict (program (fail (app "pair" [str "NotFound", str "7"]))) = "built"
-- No atom turns a number into text (row 131): the term has no type.
#guard verdict interpolateModule = "typing: term"

/-- The builder route's `UserRepo`: its carrier is the SQL handle it captured (type code 8), and
its methods are Lean functions (the model probe's `ProbeRefusals.lean`). -/
def UserRepo : ServiceDef := { key := ⟨⟨13⟩, ⟨8⟩⟩, carrier := NativeOp.sqlTy }
/-- `CurrentUser` reduced to the user's id: a number carrier. -/
def CurrentUserId : ServiceDef := { key := ⟨⟨14⟩, ⟨4⟩⟩, carrier := .nat }

#guard ServiceDef.Agrees nativeSignature UserRepo
#guard ServiceDef.Agrees nativeSignature CurrentUserId
-- The middleware as a requirement transformer: `give` discharges the handler's `CurrentUserId`.
#guard verdict (program (CurrentUserId.give (nat 1) (bindName "me" CurrentUserId.use fun me =>
    succeed me))) = "built"

-- The form table admits no `Effect.catchTag` (DI-39, DI-89).
#guard !formAdmits "Effect.catchTag"

/-! ## 7. The capture control: a layer captures data at build time

`Test/Dogfood/rc112/capture-control.ts` answers `[1, 2]` on rc.112: a method a layer built over
a service ignores a re-provision at the call site, and a method that reads the service when called
sees it. When the layer captures data, the model answers the same. A captured method is code,
which has no spelling (R7). -/

def N : ServiceDef := { key := ⟨⟨15⟩, ⟨4⟩⟩, carrier := .nat }
/-- The service a layer builds over `N`: it captures `N`'s value at build time. -/
def Svc : ServiceDef := { key := ⟨⟨16⟩, ⟨4⟩⟩, carrier := .nat }

def captureControl : Module NativeOp :=
  { services := [N, Svc]
    layers := [("svc", Svc.layer N.use)]
    main := N.give (nat 1) (provide (Layer.ref "svc") (eff do
      let captured ← N.give (nat 2) Svc.use
      let atCall ← N.give (nat 2) N.use
      return app "pair" [captured, atCall])) }

/-- Red control (the verifier's): the same layer built where `N` is already re-provided reads 2,
so the guard's `1` is the build-time value. -/
def captureBuiltLate : Module NativeOp :=
  { services := [N, Svc]
    layers := [("svc", Svc.layer N.use)]
    main := N.give (nat 1) (N.give (nat 2) (provide (Layer.ref "svc") (eff do
      let captured ← Svc.use
      let atCall ← N.use
      return app "pair" [captured, atCall]))) }

def runPure (m : Module NativeOp) : Option (Option ExitV) :=
  (built? m).map fun b => (Effect4.Api.run b.program 4000).exit

#guard runPure captureControl = some (some (.success (.list [.nat 1, .nat 2])))
#guard runPure captureBuiltLate = some (some (.success (.list [.nat 2, .nat 2])))
-- No host row and no form: it reads back.
#guard (built? captureControl).map (fun b => (b.table.isEmpty, printedOf b)) = some (true, (true, true))

/-! ## 8. The stage -/

def measured : Reach :=
  { refused :=
      [ ("AppConfig as a string service", verdict adminTokenModule)
      , ("CurrentUser as a record service", verdict currentUserModule)
      , ("NotFound{id} as a typed failure", verdict notFoundModule)
      , ("Unauthorized{reason} as a typed failure", verdict unauthorizedModule)
      , ("a number in a template string", verdict interpolateModule) ]
    admitted := verdict (caseModule "secret" 2 "2") == "built"
    answer := if exits = cases.map (fun (_, _, _, v) => some (.success v)) then .rc112 else .differs
    printed := ((built? (caseModule "secret" 2 "2")).map fun b => (printedOf b).1) == some true
    readBack := ((built? (caseModule "secret" 2 "2")).map fun b => (printedOf b).2) == some true }

/-- The stage p2 reaches today, as `Test/Dogfood/README.md` quotes it: the bounded handler runs to
rc.112's three answers, prints and reads back. -/
def stage : Reach :=
  { refused :=
      [ ("AppConfig as a string service", "serviceCarrier: signature none")
      , ("CurrentUser as a record service", "serviceCarrier: signature none")
      , ("NotFound{id} as a typed failure", "typing: errorNotAdmitted")
      , ("Unauthorized{reason} as a typed failure", "typing: errorNotAdmitted")
      , ("a number in a template string", "typing: term") ]
    admitted := true, answer := .rc112, printed := true, readBack := true }

#guard measured = stage

end Test.Dogfood.P2HandlerLayers
