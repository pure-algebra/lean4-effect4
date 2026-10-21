import Compiler.Run
import Test.Dogfood.Scenario.Todo.CachedProgram
import Effect4.Laws.Program.ValidatedBlocks
import Effect4.Run.LiveRecord
import Effect4.Tool.ToolDerived
import Effect4.Codegen.RowServices

/-! Probe: the lifetime of an application is one run of one program, its session program. The
session program is the object's own block with one more main program and the session rows
appended: an object built from an object, with no source. Its run serves every request, so the
service's state lives as long as the run. Each `#guard` is a finite evaluation on the to-do or on
the to-do with the banked cache; the definitions are this probe's, proposed for the landing. -/

set_option autoImplicit false
namespace Probe.Session
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Machine
open Test.Dogfood.Scenario.Todo (repository Repo)

/-! ## 1. The session program, as a function of the object -/

/-- A method of the session: its name, its definition's name and arity, and the types of its
payload, answer and error, all read off the object's service view and declarations. -/
structure Method where
  name : String
  def_ : String
  arity : Nat
  payload : Ty
  answer : Ty
  error : Ty

/-- The requests: one tagged pair `[name, payload]` for each method. -/
def requestUnion : List Method → Ty
  | [] => .never
  | [m] => .prod (.lit m.name) m.payload
  | m :: rest => .union (.prod (.lit m.name) m.payload) (requestUnion rest)

/-- The session's request row: the next request, or none at the end. -/
def nextRow (ms : List Method) : Row := (Row.host "Session.next" .unit (.option (requestUnion ms))).row

/-- The spelling of a method's reply row. -/
def replySpelling (m : Method) : String := "Session.reply_" ++ m.name

/-- A method's reply row: it takes the method's exit as a value. -/
def replyRow (m : Method) : Row := (Row.host (replySpelling m) (.exitOf m.answer m.error) .unit).row

/-- Dispatch a request by its tag: invoke the method on the state and the payload, reply with its
exit, and continue. A request that names no method ends the loop. -/
def dispatch (state : TermSrc) : List Method → TermSrc → Src NativeOp
  | [], _ => succeed (bool false)
  | m :: rest, req =>
    selectTagWith req m.name
      (fun payload =>
        bindWith (exit (Def.invoke m.def_ (if m.arity == 0 then [state] else [state, payload])))
          fun ex => andThen (Row.callNamed (replySpelling m) ex) (succeed (bool true)))
      (fun residual => dispatch state rest residual)

/-- The session's main program: provide each required unit service, make the state once, then
loop on the next request. -/
def sessionMain (provide : List ServiceKey) (init : String) (ms : List Method) : Src NativeOp :=
  provide.foldr (fun k body => provideService k unit body)
    (bindWith (Def.invoke init []) fun state =>
      loopWith (bool true) (fun c => c)
        (fun _ => bindWith (Row.callNamed "Session.next" unit) fun r =>
          selectOptionWith r (succeed (bool false)) (fun req => dispatch state ms req))
        (fun _ a => a) (fun _ => unit))

/-- The methods of a service, from the object alone. -/
def methodsOf (o : Object) (s : Service) (state : Ty) : Option (List Method) :=
  s.methods.mapM fun (m, k, n) => do
    let d ← o.program.defsOf[k]?
    let args ← methodArgs state d n
    pure ⟨m, d.name, n, requestTy args, d.answer, d.error⟩

/-- **The session object** of a service of the object: the same block, a session main program,
and the session rows appended after the application's rows. `provide := false` is the control
that omits the services. Refusals are strings in this probe. -/
def session (o : Object) (service : String) (provide : Bool := true) : Except String Object := do
  let ss ← o.services.mapError fun _ => "the block's services do not form"
  let some s := ss.find? (·.name == service) | throw "the block declares no such service"
  let some initD := o.program.defsOf[s.init]? | throw "no initial program"
  let some ms := methodsOf o s initD.answer
    | throw "a method's request is not the state and its arguments"
  let keys := initD.requires
  if provide && !(keys.all fun k => o.app.serviceTy k == some .unit) then
    throw "a required service has no unit carrier"
  let rows := o.app.rows ++ [nextRow ms] ++ ms.map replyRow
  match o.program with
  | .defs decls bodies _ layers =>
    let env : Env := { rows := RowDef.names (rows.map RowDef.mk),
                       defs := o.program.defsOf.zipIdx.map fun (d, k) => (d.name, k) }
    let main ← (sessionMain (if provide then keys else []) initD.name ms env [1]).mapError
      fun _ => "the session's main program does not elaborate"
    pure { app := { o.app with rows := rows }, program := .defs decls bodies main layers }
  | _ => throw "the object holds no definition block"

def todoObject : Option Object :=
  (Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.application).map Object.ofBuilt
def cachedObject : Option Object :=
  (Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.Cached.cached).map Object.ofBuilt

def todoSession : Option Object := todoObject.bind fun o => (session o "TodoApp").toOption
def cachedSession : Option Object := cachedObject.bind fun o => (session o "TodoApp").toOption
def todoSessionBuilt : Option Api.Built := todoSession.bind fun o => o.open.toOption
def cachedSessionBuilt : Option Api.Built := cachedSession.bind fun o => o.open.toOption

-- finite evaluation: the session object has the four rows, then `Session.next`, then one reply
-- row a method, and its program opens (program admission at the extended signature)
#guard todoSession.map (fun o => o.app.rows.map (·.spelling)) = some ["TodoRepo.insert",
  "TodoRepo.all", "TodoRepo.setDone", "TodoRepo.delete", "Session.next", "Session.reply_add",
  "Session.reply_list", "Session.reply_complete", "Session.reply_remove"]
#guard todoSessionBuilt.isSome && cachedSessionBuilt.isSome
-- finite evaluation: the session program's requirement row is closed; the block is unchanged
#guard todoSessionBuilt.map (fun b => b.requires.length) = some 0
#guard (todoObject.bind fun o => todoSession.map fun so => decide (so.program.defsOf = o.program.defsOf)) =
  some true
-- control (the plan's hole B): without the provision the main program requires the rows' key
#guard (todoObject.bind fun o => ((session o "TodoApp" (provide := false)).toOption.bind
  fun so => so.open.toOption.map fun b => b.requires.length)) = some 1
-- finite evaluation: the session programs lie in the block fragment of `h9_blocks`
#guard todoSession.map (fun o => Denote.BlockRows o.app.rows o.program) = some true
#guard cachedSession.map (fun o => Denote.BlockRows o.app.rows o.program) = some true
-- control: a service the block does not declare, and the cached block's second service, refuse
#guard (todoObject.map fun o => (session o "Missing").toOption.isNone) = some true
#guard (cachedObject.map fun o => match o.services with
  | .ok ss => ss.map (·.name) | .error _ => []) = some ["ListCache", "TodoApp"]
-- control: a required key whose carrier is not the unit refuses the session (a natural's code)
#guard (todoObject.map fun o =>
  match o.program with
  | .defs (d :: ds) bodies main layers =>
    (session { o with program := .defs ({ d with requires := [⟨⟨30⟩, ⟨4⟩⟩] } :: ds) bodies main layers }
      "TodoApp") == .error "a required service has no unit carrier"
  | _ => false) = some true

-- finite evaluation (the call map, `Built.calls`): the block's four calls, one a row, then the
-- main program's calls of the session rows
#guard todoSessionBuilt.map (fun b => b.calls.map (·.2.1)) = some ["TodoRepo.insert", "TodoRepo.all",
  "TodoRepo.setDone", "TodoRepo.delete", "Session.next", "Session.reply_add", "Session.reply_list",
  "Session.reply_complete", "Session.reply_remove"]

-- finite evaluation (the TypeScript interface of the session object): the repository's rows print
-- as the service `TodoRepo`, which a layer provides, and the session rows are the one free host
-- namespace `Session`, which the driver binds (`rowServiceDecls`, `hostBindings`)
#guard todoSession.map (fun o => match rowServiceDecls (nativeSignature o.app.rows) o.app.rows with
  | .ok ds => ds.map (·.name)
  | .error _ => []) = some ["TodoRepoKey", "TodoRepo"]
#guard todoSession.map (fun o => match hostBindings (nativeSignature o.app.rows) o.app.rows with
  | .ok (spaces, _) => spaces
  | .error _ => ["refused"]) = some ["Session"]

/-! ## 2. The driver is a host of the session rows -/

/-- The driver's state: the requests not yet served, and each reply with its row. -/
abbrev Script := List Val × List (String × Val)

/-- **The driver as a reactor**: it answers `Session.next` from its queue and records each reply.
It answers no row of the application. -/
def script (replies : List String) : Run.Reactor Script := fun row sent st =>
  if row.spelling == "Session.next" then
    match st.1 with
    | [] => some (.ofExit (.success .none), st)
    | r :: rest => some (.ofExit (.success (.some r)), (rest, st.2))
  else if replies.contains row.spelling then
    some (.ofExit (.success .unit), (st.1, st.2 ++ [(row.spelling, sent)]))
  else none

/-- Two hosts of disjoint rows side by side, each over its own state: the reactor reading of
`Effects.Comodel.route`. -/
def both {α β : Type} (r : Run.Reactor α) (s : Run.Reactor β) : Run.Reactor (α × β) :=
  fun row v st =>
    match r row v st.1 with
    | some (c, a') => some (c, (a', st.2))
    | none => (s row v st.2).map fun (c, b') => (c, (st.1, b'))

def replySpellings : List String :=
  ["Session.reply_add", "Session.reply_list", "Session.reply_complete", "Session.reply_remove"]

/-- The host lane's script as session requests. -/
def requests : List Val :=
  [.list [.str "add", .str "milk"], .list [.str "add", .str "café 日本 🙂"], .list [.str "list", .unit],
   .list [.str "complete", .nat 1], .list [.str "list", .unit], .list [.str "remove", .nat 1],
   .list [.str "list", .unit]]

/-- The lifetime: one run of the session program under the driver and the repository. -/
def sessionRun (b : Api.Built) (reqs : List Val) (start : Repo) : Run × (Script × Repo) :=
  Run.runWith b (both (script replySpellings) repository) ((reqs, []), start) "session" {} 512

def todoRun : Option (Run × (Script × Repo)) := todoSessionBuilt.map fun b => sessionRun b requests (1, [])

-- finite evaluation: one run serves the seven requests and ends; seven replies are recorded, and
-- the repository's state is the host lane's last one
#guard todoRun.map (fun (s, st) => (s.exit.isSome, st.1.1.length, st.1.2.length, st.2.1, st.2.2.length)) =
  some (true, 0, 7, 3, 1)

-- finite evaluation (hole B at run time): without the provision the run still serves the seven
-- requests with the same replies; the machine's context read does not fail on a unit service. So
-- the hole is the open requirement row, which excludes the run from `M7Fragment`'s closed row
#guard (todoObject.bind fun o => ((session o "TodoApp" (provide := false)).toOption.bind
  fun so => so.open.toOption.map fun b =>
    let (s, st) := sessionRun b requests (1, [])
    (s.exit.isSome, decide (some (st.1.2.map (·.2)) = todoRun.map fun (_, st') => st'.1.2.map (·.2))))) =
  some (true, true)

/-! ## 3. The session against today's runner -/

/-- Today's runner (`Compiler.serve`'s run): each request its own program, the entry at its
arguments over the application's declarations, from the state the request before it left. -/
def perRequest : List Compiler.Request → Repo → List (Option ExitV)
  | [], _ => []
  | r :: rest, st =>
    match (r.moduleOf? Test.Dogfood.Scenario.Todo.application).bind
        fun m => (Api.Author.build m).toOption with
    | none => none :: perRequest rest st
    | some b =>
      let (run, next) := Run.runWith b repository st
      run.exit :: perRequest rest next

def scriptRequests : List Compiler.Request :=
  [⟨"add", [.str "milk"]⟩, ⟨"add", [.str "café 日本 🙂"]⟩, ⟨"list", []⟩, ⟨"complete", [.nat 1]⟩,
   ⟨"list", []⟩, ⟨"remove", [.nat 1]⟩, ⟨"list", []⟩]

-- finite evaluation (stateless service): each reply of the one run is the exit that today's
-- runner gives the same request, as a value
#guard todoRun.map (fun (_, st) => st.1.2.map (·.2)) =
  some ((perRequest scriptRequests (1, [])).map fun ex => match ex with
    | some e => reifyExitVal e
    | none => .unit)
#guard (perRequest scriptRequests (1, [])).all (·.isSome)

/-- Today's runner, with each request's built program: the data `run --typed` prints from. -/
def perRequestBuilt : List Compiler.Request → Repo → List (Option (Api.Built × Option ExitV))
  | [], _ => []
  | r :: rest, st =>
    match (r.moduleOf? Test.Dogfood.Scenario.Todo.application).bind
        fun m => (Api.Author.build m).toOption with
    | none => none :: perRequestBuilt rest st
    | some b =>
      let (run, next) := Run.runWith b repository st
      some (b, run.exit) :: perRequestBuilt rest next

-- finite evaluation: each reply of the one run, encoded at its reply row's request type (the
-- method's exit type), is the text that `run --typed` prints today for the same request
-- (`Compiler.typedJson`); the rendered text stays inside the guard
#guard (todoRun.bind fun (_, st) => todoSession.map fun o => st.1.2.map fun (spelling, v) =>
  match o.app.rows.find? (·.spelling == spelling) with
  | some row => match Ty.encode (nativeSignature o.app.rows).keyNames row.request v with
    | some j => Compiler.jsonText (NatJson.ofBinary64 (Schema.Codec.normJ j))
    | none => "refused"
  | none => "no row") =
  some ((perRequestBuilt scriptRequests (1, [])).map fun x => match x with
    | some (b, ex) => Compiler.typedJson b ex
    | none => "unbuilt")

/-- The repository, recording the spelling of each row it answers. -/
def recorded : Run.Reactor (Repo × List String) := fun row v st =>
  (repository row v st.1).map fun (c, next) => (c, (next, st.2 ++ [row.spelling]))

def twoLists : List Val := [.list [.str "list", .unit], .list [.str "list", .unit]]
def stocked : Repo := (2, [(1, "milk", false)])

-- finite evaluation (stateful service, the plan's hole A): with the banked cache imposed, the one
-- run answers two lists with one call of the repository, the second from the cache
#guard (cachedSessionBuilt.map fun b =>
  (Run.runWith b (both (script replySpellings) recorded) ((twoLists, []), (stocked, []))
    "session" {} 512).2.2.2) = some ["TodoRepo.all"]
-- control: one program a request makes the cache again each time, and asks the repository twice
#guard ((Test.Dogfood.Scenario.Todo.Cached.consumerBuiltAt "list" []).map fun b =>
  let (_, s1) := Run.runWith b recorded (stocked, [])
  (Run.runWith b recorded s1).2.2) = some ["TodoRepo.all", "TodoRepo.all"]

/-! ## 4. The lifetime under the laws -/

-- finite evaluation: the run is funded, at rest, driven by a host, and exited: the premises of
-- `h9_blocks` and `agrees_hostRun_blocks` (`src/Effect4/Laws/Program/ValidatedBlocks.lean`)
#guard todoRun.map (fun (s, _) => (Run.funded s, Run.atRest s, Run.hostDriven s, s.exit.isSome)) =
  some (true, true, true, true)
-- finite evaluation: the driver and the repository, read as one model, gave the run's answers,
-- from the start to the drive's end (`Run.agrees`, the premise `HostAnswered` decided)
#guard todoRun.map (fun (s, fin) =>
  (Run.agrees (both (script replySpellings) repository) s ((requests, []), (1, []))).map
    fun (st : Script × Repo) => decide (st = fin)) = some (some true)
-- finite evaluation: every bind row is bound, so `journal_bound_call` reads each request sent
#guard todoRun.map (fun (s, _) => (Run.rows s).all fun (c, ph) => match c with
  | .bind _ _ => decide (ph = .bound)
  | _ => true) = some true
-- control: a request that is no member of the request row is refused at reply admission, and the
-- run waits at `Session.next` with no exit: the driver cannot inject a request the methods lack
#guard todoSessionBuilt.map (fun b =>
  let (s, _) := sessionRun b [.list [.str "bogus", .unit]] (1, [])
  (s.exit.isNone, s.phases.any fun ph => decide (ph = .refused .envelope))) = some (true, true)

/-! ## 5. The lifetime as data -/

/-- The lifetime's run as a live run: the journal fed through `Live.feedAll` from the open, so
the value is a `Live` by construction (`Live.feedAll_wire`, `Live.journal_replays`). -/
def todoLive : Option Live := todoSessionBuilt.bind fun b =>
  todoRun.map fun (s, _) => (Live.open b "session").feedAll (s.journal.map .wire)

-- finite evaluation: the live run is the driven run
#guard (todoLive.bind fun l => todoRun.map fun (s, _) => decide (l.run.observe = s.observe)) = some true
-- finite evaluation: the lifetime saves as the object and the journal, and restores to the same run
-- with no host (`LiveRecord.restore_save`); the record's canonical bytes and the session object's
-- node bytes have these sizes
#guard (todoLive.map fun l => match LiveRecord.restore (LiveRecord.save l) with
  | .ok l' => decide (l'.run.observe = l.run.observe) && decide (l'.run.journal = l.run.journal)
  | .error _ => false) = some true
#guard todoLive.map (fun l => (l.run.journal.length, (Store.Canonical.encode (LiveRecord.save l)).length)) =
  some (68, 137402)
/-- A journal with each call claim's raw table emptied: a measurement of the table's share only. -/
def withoutTables (j : List Api.Runner.Command) : List Api.Runner.Command := j.map fun
  | .bind call token => .bind { call with table := [] } token
  | c => c
-- finite evaluation: 22 of the 68 commands bind a call, each claim carrying the raw table; with the
-- tables emptied the record is 28,150 bytes
#guard todoLive.map (fun l =>
  let r := LiveRecord.save l
  ((l.run.journal.filter fun c => match c with | .bind _ _ => true | _ => false).length,
    (Store.Canonical.encode { r with journal := withoutTables r.journal }).length)) = some (22, 28150)
-- finite evaluation: the object's node is 7,894 bytes and the session object's 13,190
#guard (todoObject.map fun o => (Object.bytes o).length, todoSession.map fun o => (Object.bytes o).length) =
  (some 7894, some 13190)

end Probe.Session
