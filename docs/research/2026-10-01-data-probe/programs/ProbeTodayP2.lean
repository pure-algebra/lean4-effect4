import Effect4.Api.Author
import Effect4.Api.HostSession
import Effect4.Api
import TypeScript.Render

/-! Seat PROGRAMS of the data probe (2026-10-01), probe 1: program 2's request handler
(`docs/research/2026-09-30-model-probe/programs/ts/p2-handler-layers.ts`) written with today's
`Ty` through the authoring surface (`Api.Author`, `Row.host`), run through the live keyed session
under a scripted host, and printed as TypeScript.

Today's spellings, each a workaround with a named cost:
* records are nested pairs, fields by position (`fst`, `snd`): `User`, `AppConfig`, `Response`;
* the variant field `role: "admin" | "member"` is a union of string literals (this one is exact);
* `NotFound{id: number}` cannot carry the number (DI-62's error image), and no atom turns a
  number into text, so the caller threads the id's decimal text beside the id;
* `UserRepo.findById` is a host row that answers the decoded record or nothing (the typed host
  answer route, D12); the query and `Schema.decodeUnknownEffect(User)` live in the host;
* `CurrentUser` holds a record, which no service carrier may (rows 114, 118), so `me` is passed
  as a value;
* `AppConfig` is a host row that answers the pair (the `Config` route is R13, not this probe's).

Scratch, not in the tree. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Probe.DataP2
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession

/-! ## The data, as today's `Ty` spells it -/

/-- `role: Schema.Literals(["admin", "member"])` (p2:29). -/
def roleTy : Ty := .union (.lit "admin") (.lit "member")
/-- `User = { id: number, name: string, role }` (p2:26-30), declaration order, by position. -/
def userTy : Ty := .prod .nat (.prod .string roleTy)
/-- `AppConfig = { adminToken: string, pageSize: number }` (p2:37-40). -/
def configTy : Ty := .prod .string .nat
/-- `SqlError | SchemaError`, crossing as DB-15's `(tag, message)` pair. -/
def infraErrTy : Ty := .prod .string .string

/-- `AppConfigLive`'s value (p2:51-55), read by the host. -/
def getConfig : RowDef := Row.host "AppConfig.get" .unit configTy .never "p2-handler-layers.ts:51-55"
/-- `UserRepo.findById` (p2:58-70) with the query and the decode done by the host: it answers the
decoded record or nothing; its failures are the infrastructure's pairs. -/
def findById : RowDef :=
  Row.host "UserRepo.findById" .nat (.option userTy) infraErrTy "p2-handler-layers.ts:58-70"

/-! ## Field access by position -/

def userId (u : TermSrc) : TermSrc := app "fst" [u]
def userName (u : TermSrc) : TermSrc := app "fst" [app "snd" [u]]
def userRole (u : TermSrc) : TermSrc := app "snd" [app "snd" [u]]
def response (status body : TermSrc) : TermSrc := app "pair" [status, body]

/-! ## The handler -/

/-- p2:62-67: `row === undefined ? fail(new NotFound({ id })) : decode(row)`. The id's text is a
parameter: no atom turns a number into text (`Machine/Term.lean`, `NativeAtom`). -/
def findOrFail (id idText : TermSrc) : Src NativeOp :=
  bindName "found" (Row.call findById id) fun found =>
    selectOption "user" found
      (fail (app "pair" [str "NotFound", idText]))
      (succeed (var "user"))

/-- `getProfile(id)` (p2:85-93), with `CurrentUser` passed as the value `me`. -/
def getProfile (me id idText : TermSrc) : Src NativeOp :=
  ifElse (app "and" [app "not" [app "eq" [userRole me, str "admin"]],
                     app "not" [app "eq" [userId me, id]]])
    (fail (app "pair" [str "Unauthorized", str "not yours"]))
    (findOrFail id idText)

/-- `withAuth(token, getProfile(id))` (p2:74-83). -/
def withAuth (token id idText : TermSrc) : Src NativeOp :=
  bindName "config" (Row.call getConfig unit) fun config =>
    ifElse (app "not" [app "eq" [token, app "fst" [config]]])
      (fail (app "pair" [str "Unauthorized", str "bad token"]))
      (bindName "me" (findOrFail (nat 1) (str "1")) fun me =>
        getProfile me id idText)

/-- `handle(token, id)` (p2:101-106): the success maps to `{status: 200, body: user.name}`, the
two tagged failures to 404 and 401 responses. -/
def handle (token id idText : TermSrc) : Src NativeOp :=
  catchIf "e" (app "tagIs" [str "NotFound", var "e"])
    (catchIf "e2" (app "tagIs" [str "Unauthorized", var "e2"])
      (bindName "user" (withAuth token id idText) fun user =>
        succeed (response (nat 200) (userName user)))
      (succeed (response (nat 401) (app "snd" [var "e2"]))))
    (succeed (response (nat 404) (app "concat" [str "no user ", app "snd" [var "e"]])))

/-- One request as a module: the handler on fixed arguments, with its two rows. -/
def caseModule (token : String) (id : Nat) (idText : String) : Module NativeOp :=
  { rows := [getConfig, findById], main := handle (str token) (nat id) (str idText) }

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

-- It builds: typed against its own table and admitted.
#guard (built? (caseModule "secret" 2 "2")).isSome
-- The checked type. The answer is `readonly [number, string]`; the error column is the
-- infrastructure pair alone: `["NotFound", string]` and `["Unauthorized", …]` are subtypes of
-- `[string, string]`, so the union absorbs them and the program's own failure tags are not
-- in its type (rc.112's pinned type is `Response` / `SchemaError | SqlError | ConfigError`).
#guard (built? (caseModule "secret" 2 "2")).map (fun b => (b.ty.answer, b.ty.error)) =
  some (.prod .nat .string, .prod .string .string)

/-! ## A scripted host, through the live keyed session -/

abbrev HostAnswer := Completion Val Err Defect FiberId Ann

/-- The users table of `run-p2.ts:13`: (1, ada, admin), (2, bob, member). -/
def users : Nat → Option Val
  | 1 => some (.list [.nat 1, .list [.str "ada", .str "admin"]])
  | 2 => some (.list [.nat 2, .list [.str "bob", .str "member"]])
  | _ => none

/-- A host: the configuration, and the repository answering each user as today's nested pair. -/
def pairHost (b : Effect4.Api.Built) (op : NativeOp) (request : Val) : Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "AppConfig.get" then
      some (.ofExit (.success (.list [.str "secret", .nat 20])))
    else if some i = b.positionOf "UserRepo.findById" then
      match request with
      | .nat n => some (.ofExit (.success (match users n with | some u => .some u | none => .none)))
      | _ => none
    else none
  | _ => none

/-- Red control's host: the repository answers the record the way rc.112's decoder hands it to
the program, an object (`Val.ctor`, the only keyed-looking value the carrier has), not the pair. -/
def objectHost (b : Effect4.Api.Built) (op : NativeOp) (request : Val) : Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "UserRepo.findById" then
      some (.ofExit (.success (.some (.ctor 0 [.nat 2, .str "bob", .str "member"]))))
    else pairHost b op request
  | _ => none

/-- Red control's host: the record flattened to one three-element list. -/
def flatHost (b : Effect4.Api.Built) (op : NativeOp) (request : Val) : Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "UserRepo.findById" then
      some (.ofExit (.success (.some (.list [.nat 2, .str "bob", .str "member"]))))
    else pairHost b op request
  | _ => none

structure Driver (b : Effect4.Api.Built) where
  session : Session b.program b.table
  refused : List Effect4.Api.HostSession.Refusal := []
  stopped : Bool := false

/-- One step: bind the first outstanding call, answer it, apply the reply; with nothing
outstanding, flush the scheduler. A refused reply stops the run and is recorded. -/
def step (b : Effect4.Api.Built) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer)
    (d : Driver b) : Driver b :=
  if d.stopped then d else
  let s := d.session
  match outstanding s with
  | (fiber, token, op, request) :: _ =>
    let call : Call := ⟨version, "p2", b.table, s.nextCall, fiber, op, request⟩
    let r1 := bindCall s call token
    match r1.phase with
    | .refused why => { d with refused := d.refused ++ [why], stopped := true }
    | _ =>
      match host b op request with
      | none => { d with session := r1.session, stopped := true }
      | some completion =>
        let reply : Reply := ⟨version, "p2", call.callId, ⟨fiber, token⟩, completion⟩
        let r2 := submit r1.session reply
        match r2.phase with
        | .refused why => { d with session := r1.session, refused := d.refused ++ [why], stopped := true }
        | _ => { d with session := (applyReply r2.session reply.key 1000).session }
  | [] => { d with session := (advance s 1000 Api.flush).session }

def drive (b : Effect4.Api.Built) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer) :
    Nat → Driver b → Driver b
  | 0, d => d
  | n + 1, d => drive b host n (step b host d)

/-- The root's exit and the session's refusals. -/
def runLive (m : Module NativeOp) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer) :
    Option (Option ExitV × List Effect4.Api.HostSession.Refusal) :=
  (built? m).bind fun b =>
    match start b.program b.table "p2" ⟨version, "p2", "p2", b.table⟩ 1000 with
    | .error _ => none
    | .ok s0 =>
      let d := drive b host 60 { session := (advance s0 1000 Api.evaluate).session }
      some ((d.session.machine.fiber? Api.root).bind (·.exit), d.refused)

-- Green: the three requests of `run-p2.ts:18` answer what rc.112 answered there
-- (`hostruns.log`: `{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}`,
-- `{"status":401,"body":"bad token"}`), with the id's text threaded by hand for the 404.
#guard (runLive (caseModule "secret" 2 "2") pairHost) =
  some (some (.success (.list [.nat 200, .str "bob"])), [])
#guard (runLive (caseModule "secret" 9 "9") pairHost) =
  some (some (.success (.list [.nat 404, .str "no user 9"])), [])
#guard (runLive (caseModule "wrong" 2 "2") pairHost) =
  some (some (.success (.list [.nat 401, .str "bad token"])), [])
-- The threaded text is trusted, not computed: a caller that threads the wrong text gets a
-- wrong body, and nothing in the type says so.
#guard (runLive (caseModule "secret" 9 "nine") pairHost) =
  some (some (.success (.list [.nat 404, .str "no user nine"])), [])

-- Red control: the record answered as an object, or flattened, is refused at `submit` by the
-- reply check (`preflight` → `acceptReply`, `Api/HostSession.lean:162-174`): the session
-- records `envelope` and the root has no exit.
#guard (runLive (caseModule "secret" 2 "2") objectHost) = some (none, [.envelope])
#guard (runLive (caseModule "secret" 2 "2") flatHost) = some (none, [.envelope])

/-! ## The JSON body as `unknown`: admitted, carried, unreadable

p1's `response.json()` with no decode (`p1-http-cache.ts:52`, a cast). A row may answer
`unknown` (row 97's scan passes it, `Program/Admission.lean`), and the reply check admits any
handle-free value there, an object included; no atom reads it (`ProbeRedControls.lean`, RC17). -/

def getJson : RowDef := Row.host "Http.getJson" .string .unknown .never "p1-http-cache.ts:52"
def jsonModule : Module NativeOp := { rows := [getJson], main := Row.call getJson (str "EFX") }

def jsonHost (b : Effect4.Api.Built) (op : NativeOp) (_request : Val) : Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "Http.getJson" then
      some (.ofExit (.success (.ctor 0 [.str "EFX", .nat 21])))
    else none
  | _ => none

#guard (runLive jsonModule jsonHost) = some (some (.success (.ctor 0 [.str "EFX", .nat 21])), [])

/-! ## The printed TypeScript -/

/-- The printed module, rendered (`Api.printModule`, then the pinned renderer). -/
def printed (m : Module NativeOp) : Option String := do
  let b ← built? m
  let module ← Effect4.Api.printModule "handle" b.program b.table
  pure (TypeScript.Render.module TypeScript.house0 module)

#guard (printed (caseModule "secret" 2 "2")).isSome

#eval show IO Unit from do
  IO.println "=== printed module: handle(\"secret\", 2) ==="
  IO.println ((printed (caseModule "secret" 2 "2")).getD "<refused>")
  IO.println "=== sizes: printed characters, canonical program bytes ==="
  match built? (caseModule "secret" 2 "2") with
  | some b =>
    IO.println s!"printed {((printed (caseModule "secret" 2 "2")).getD "").length} chars; bytes {(Effect4.Api.bytesOf b.program).length}"
  | none => IO.println "<not built>"

end Probe.DataP2
