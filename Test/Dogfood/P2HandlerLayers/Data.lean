import Effect4.Author

/-! Data shared by the scenario battery and fixture writers. -/

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

/-! ## 3. The run under a scripted host -/

/-- A record value, its fields in canonical order. -/
def recordVal (names : List String) (values : List Val) : Val :=
  (Effect4.Machine.Record.build names values).getD .unit

/-- The users table of `run-p2.ts`: `(1, ada, admin)` and `(2, bob, member)`. -/
def user : Nat → Option Val
  | 1 => some (recordVal ["id", "name", "role"] [.nat 1, .str "ada", .str "admin"])
  | 2 => some (recordVal ["id", "name", "role"] [.nat 2, .str "bob", .str "member"])
  | _ => none

end Test.Dogfood.P2HandlerLayers
