import Compiler.Check
import Effect4.Run
import Effect4.Run.Kit
import Effect4.Data.JsonNorm

/-!
# Compiler.Run — the Lean machine over a Lean host, one line a request

`run` is the reference interpreter as a command, as CompCert's `-interp` is
(`docs/research/2026-10-20-compiler-entry/README.md`, §5; the entry point's third slice). Each
request of a script is an entry of the application at literal arguments: built, then run on the
Lean machine under the application's host, and written as one line. Everything here is computed
with no IO. The command line, which reads the options and the script's file, is `Compiler.Main`'s.

- **The host** (`Hosted`) is what an application supplies to be run: its state's type, the state a
  run starts from, the host as a function (`Run.Reactor`), and how the state is shown after a
  request (`view`). A project passes it to `Compiler.main`, with its script.
- **A request** (`Request`) is an entry's name and its arguments, each a literal. Its module is the
  entry at its arguments over the application's declarations, one argument for each parameter
  (`Request.moduleOf?`).
- **A request's run** (`serve`): its module built (`Api.Author.build`), then run from the host's
  state with its reactor, at the execution budget (`Run.runWith`). Its outcome (`Served`) is the
  request, the built program, the exit and the state after it, which is the next request's. A
  refused build is the build's located refusal, as `check` prints it, and the state does not
  change.
- **A request's line** (`lineOf`), by the mode: a readable line, the default: the request, its exit
  encoded at the built program's exit type by the type-directed codec, Effect's own `Schema.Exit`
  encoding (`typedJson`), and the host's state as its value tree's JSON; the request and that exit
  alone; or the result as one value tree in JSON (`resultVal`, `valueText`), which the lowered
  native run prints too.
- **A script from JSON** (`scriptOf`): an array of objects `{"entry": …, "args": […]}`, its text
  read by the profile's reader (`NatJson.parse`, `Compiler.readJson`). An argument is a string, a
  natural, a Boolean, or `null` for the unit, as a result's value tree prints each literal. No
  text is read as a program (decisions row 420).

What it does not establish: a run on Effect or on the native kit, which their own lanes compare.
A frontier is no refusal: a run that stops for fuel, at a row the host does not answer, or at the
drive's last round has no exit, and its line says so.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Store

/-! ## A request, and what an application supplies to be run -/

/-- **One request** of an application: an entry's name and its arguments, each a literal. -/
structure Request where
  entry : String
  args : List Lit := []
  deriving DecidableEq, Repr

/-- **What an application supplies to be run**: its host's state type `σ`, the state a run starts
from, the host as a function of the row, the request and the state (`Run.Reactor`), and how the
state is shown after a request (`view`). -/
structure Hosted where
  σ : Type
  initial : σ
  reactor : Run.Reactor σ
  view : σ → Val

/-- **A request's module**: its entry at its arguments over the application's declarations
(`Application.moduleOf`); `none` when no entry has its name, or when its arguments are not one for
each of the entry's parameters. `Application.Entry.applied` would leave a missing parameter unbound
and drop an extra argument. -/
def Request.moduleOf? (app : Application NativeOp) (r : Request) : Option (Module NativeOp) :=
  (app.entry? r.entry).bind fun e =>
    if r.args.length == e.params.length then some (app.moduleOf e (r.args.map lit)) else none

/-! ## A request's line -/

/-- A literal as a value. -/
def litVal : Lit → Val
  | .unit => .unit
  | .nat n => .nat n
  | .bool b => .bool b
  | .str s => .str s

/-- An exit as a value: its image, or none where the run has no exit. -/
def exitVal : Option Machine.ExitV → Val
  | none => .none
  | some e => .some (Machine.exitImage.toVal e)

/-- **One request's result as one value**: the request's entry and arguments, its exit, and the
host's state after it, as `view` shows it. -/
def resultVal {σ : Type} (view : σ → Val) (r : Request) (exit : Option Machine.ExitV) (s : σ) :
    Val :=
  .list [.str r.entry, .list (r.args.map litVal), exitVal exit, view s]

/-- **A value as one line of JSON**: its value tree's print (`Run.Kit.valShape`, the shape the
native kit prints a value with), in the profile's compact text. -/
def valueText (v : Val) : String := jsonText (Run.Kit.valShape.printTree v)

/-- **An exit encoded at the built program's exit type** (`Ty.exitOf answer error`) by the
type-directed codec, Effect's own `Schema.Exit` encoding, its JSON keys in canonical order
(`Schema.Codec.normJ`). The codec takes the program's key names: the names its signature gives the
service keys. The text is "no exit" where the run has none, and "refused" where the codec admits no
value of the type. -/
def typedJson (b : Api.Built) (exit : Option Machine.ExitV) : String :=
  match exit with
  | none => "no exit"
  | some e =>
    match Ty.encode (nativeSignature b.table).keyNames (.exitOf b.ty.answer b.ty.error)
        (Machine.exitImage.toVal e) with
    | some j => jsonText (NatJson.ofBinary64 (Schema.Codec.normJ j))
    | none => "refused"

/-- A literal as text. -/
def litText : Lit → String
  | .unit => "()"
  | .nat n => toString n
  | .bool b => toString b
  | .str s => s.quote

/-- A request as text: its entry, then its arguments in parentheses. -/
def requestText (r : Request) : String := s!"{r.entry}({", ".intercalate (r.args.map litText)})"

/-- **How `run` writes a request's line.** -/
inductive Mode where
  /-- the request, its exit encoded at its own type (`typedJson`), and the host's state after it as
  its value tree's JSON (`valueText`): the default -/
  | text
  /-- the request, then its exit encoded at its own type (`typedJson`) -/
  | typed
  /-- the result as one value tree in JSON (`resultVal`), as the lowered native run prints it -/
  | json
  deriving DecidableEq, Repr

/-- **A request's line**, after its run: by the mode, from the request, the built program, the
exit and the host's state after it. -/
def lineOf (h : Hosted) (mode : Mode) (r : Request) (b : Api.Built) (exit : Option Machine.ExitV)
    (s : h.σ) : String :=
  match mode with
  | .json => valueText (resultVal h.view r exit s)
  | .typed => s!"{requestText r} {typedJson b exit}"
  | .text => s!"{requestText r} -> {typedJson b exit} | {valueText (h.view s)}"

/-! ## The run -/

/-- **One request's outcome**: the request, its built program, its exit and the host's state after
it; a line is its print in a mode (`line`). -/
structure Served (σ : Type) where
  request : Request
  built : Api.Built
  exit : Option Machine.ExitV
  state : σ

/-- An outcome's line in a mode (`lineOf`). -/
def Served.line (h : Hosted) (mode : Mode) (o : Served h.σ) : String :=
  lineOf h mode o.request o.built o.exit o.state

/-- **One request on the Lean machine**, from the host's state `s`: its module built
(`Api.Author.build`), then run with the host's reactor at the execution budget (`Run.runWith`); its
outcome, and the host's state after it. A refused build is the build's located refusal, with the
request's entry named, and the state does not change. -/
def serve (h : Hosted) (budget : Api.Budget) (r : Request) (m : Module NativeOp) (s : h.σ) :
    Except CheckRefusal (Served h.σ) × h.σ :=
  match Api.Author.build m with
  | .error why => (.error ⟨some r.entry, why⟩, s)
  | .ok b =>
    let (run, next) := Run.runWith b h.reactor s (budget := budget)
    (.ok { request := r, built := b, exit := run.exit, state := next }, next)

/-- **A script on the Lean machine**: each request with its module, served from the state that the
request before it left; one outcome a request, in order. -/
def served (h : Hosted) (budget : Api.Budget) :
    List (Request × Module NativeOp) → h.σ → List (Except CheckRefusal (Served h.σ))
  | [], _ => []
  | (r, m) :: rest, s =>
    let (outcome, next) := serve h budget r m s
    outcome :: served h budget rest next

/-- The script's outcomes as lines, in a mode: `served`, each outcome printed (`Served.line`). -/
def runFrom (h : Hosted) (mode : Mode) (budget : Api.Budget)
    (script : List (Request × Module NativeOp)) (s : h.σ) : List (Except CheckRefusal String) :=
  (served h budget script s).map (·.map (Served.line h mode))

/-! ## The script and the options -/

/-- Why a request has no module, in words: no entry has its name, or its arguments are not one for
each of the entry's parameters. -/
def Request.unmatched (app : Application NativeOp) (r : Request) : String :=
  match app.entry? r.entry with
  | none => s!"no entry is named {r.entry}; the entries are {", ".intercalate app.entryNames}"
  | some e =>
    s!"the entry {e.name} takes the arguments ({", ".intercalate (e.params.map (·.1))}), " ++
      s!"and the request gives {r.args.length}"

/-- **The script against the application**: each request with its module (`Request.moduleOf?`);
or the first request that has none, by its place in the script, and why. -/
def modulesOf (app : Application NativeOp) (script : List Request) :
    Except String (List (Request × Module NativeOp)) :=
  script.zipIdx.mapM fun (r, i) =>
    match r.moduleOf? app with
    | some m => .ok (r, m)
    | none => .error s!"the request {i}, {requestText r}: {r.unmatched app}"

/-- **A literal argument from its JSON**: a string, a natural or a Boolean, and `null` for the
unit, as a result's value tree prints each literal (`litVal`). -/
def litOfJson : NatJson → Option Lit
  | .null => some .unit
  | .bool b => some (.bool b)
  | .nat n => some (.nat n)
  | .str s => some (.str s)
  | _ => none

/-- **A request from its JSON**: an object with the entry's name under `entry` and its literal
arguments under `args`, which a request with no argument may leave out; each key once, and no
other key. -/
def Request.ofJson (t : NatJson) : Except String Request := do
  let .obj fields := t | throw "a request is a JSON object"
  if let some (key, _) := fields.find? fun (k, _) => k != "entry" && k != "args" then
    throw s!"a request has no key {key}: its keys are entry and args"
  if (fields.filter (·.1 == "entry")).length > 1 || (fields.filter (·.1 == "args")).length > 1
  then throw "a request names each key once"
  let entry ← match t.at? [.key "entry"] with
    | some (.str e) => pure e
    | _ => throw "a request names its entry as a string under entry"
  let args ← match t.at? [.key "args"] with
    | none => pure []
    | some (.arr items) =>
      match items.mapM litOfJson with
      | some lits => pure lits
      | none => throw "a request's arguments are strings, naturals, Booleans or null"
    | some _ => throw "a request's args is an array"
  return { entry, args }

/-- **A script from its JSON**: an array of requests, in order; or the first that is none, by its
place in the script. -/
def scriptOf : NatJson → Except String (List Request)
  | .arr items => items.zipIdx.mapM fun (t, i) =>
    (Request.ofJson t).mapError (s!"the request {i}: " ++ ·)
  | _ => .error "a script is a JSON array of requests"

/-- **The options of `run`**: how a line is written, readable by default, the script's file, and
the execution budget, the fuel that every row of a run is played at (`Api.Budget.fuel`). The
value-tree line (`Mode.json`) is every outcome's reading in JSON, in the report's `json` and `md`
formats; `--json` is the report's flag (`Compiler.Main`). -/
structure RunOptions where
  mode : Mode := .text
  script : Option String := none
  budget : Api.Budget := {}

/-- Read the options of `run`, or name the argument that is none. -/
def RunOptions.read : List String → RunOptions → Except String RunOptions
  | [], o => .ok o
  | "--typed" :: rest, o => RunOptions.read rest { o with mode := .typed }
  | "--text" :: rest, o => RunOptions.read rest { o with mode := .text }
  | "--script" :: file :: rest, o => RunOptions.read rest { o with script := some file }
  | "--budget" :: n :: rest, o =>
    match n.toNat? with
    | some fuel => RunOptions.read rest { o with budget := { o.budget with fuel } }
    | none => .error s!"--budget {n} is no natural number"
  | [a], _ =>
    .error (if a == "--script" || a == "--budget" then s!"{a} takes a value" else s!"{a} is no option")
  | a :: _, _ => .error s!"{a} is no option"

end Compiler
