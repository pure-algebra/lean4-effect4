import Tools.Query
import Tools.JsonBridge
import Tools.Catalogue
import Effect4.Laws.Store.ShapeRead
import Effect4.Program.Typing.SourceSession
import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.SourceDocument
import Effect4.Laws.Program.SketchWire
import Effect4.Laws.Program.SketchAdmission
import Effect4.Api.RunnerDerived
import Effect4.Run.Live
import Effect4.Run.LiveRecord
import Effect4.Laws.Api.Live
import Effect4.Laws.Api.LiveRecord
import Effect4.Laws.Run.Tree
import Effect4.Run.Kit

/-!
# Tools.Session — the edit session as a tool: one request a line, one session held between lines

The query tool (`Tools.Query`) answers one request about a program and keeps nothing. This tool
keeps a versioned source document (`Doc`, `src/Effect4/Program/Typing/SourceDocument.lean`) over an
edit session of a sketch as written (`SourceSession`,
`src/Effect4/Program/Typing/SourceSession.lean`) between its lines, with the journal of its
edits. The session checks the sketch through its layer references, as program admission checks a
program, and shows the expansion's table at the source's addresses (decisions row 373 (7)).

A request is one JSON object; the answer is one JSON object, in the query tool's shape
(`Tools.Query.Answer`). Every carrier a request takes, a program, a filling, a hole table, a row
table or service declarations, travels as its canonical bytes in lowercase hex (`program`,
`holes`, …) or as its JSON print (`programJson`, `holesJson`, …), whose objects may come in any
order and whose lists may come as arrays. One function reads each way at every carrier
(`Tools.JsonBridge.valueFrom?`: the store's exact decoder, `Canonical.decode`, or
`Canonical.ofJsonAnyOrder`). Answers give JSON; a request with `"hex": true` gets the canonical
bytes beside it. An agent never needs them: a digest names the bytes where a name is wanted.

**The application travels with `open`** (decisions row 373 (10)): the row table, the
service declarations and the named types (`rows` or `rowsJson`, `services` or `servicesJson`,
`types` or `typesJson`). With none, the application is the empty one. The catalogue gives a row's
JSON form. An answer names the application: `empty`, or `sha256:` and the digest of the canonical
bytes of the triple. A digest names bytes; no answer assumes two applications with one digest are
one.

| Operation | Takes | Answers | The laws it names |
| --- | --- | --- | --- |
| `open` | `program` (hex) or `programJson`, and the hole table, the rows, the services and the types if any, each as hex or JSON | the view | `SourceSession.reached_view`; `ofLeanJson_num` and `Canonical.ofJsonAnyOrder_exact` for JSON |
| `inspect` | `path` | the target (`doc`, `revision`, `path`, `expected`), the typed focus, the entry, and any refusal | `SourceSession.reached_view`, `SourceSession.focusAt_typed` |
| `replace` | `path`, `replacement` (hex) or `replacementJson`, target (`docName`, `docGeneration`, `revision`, `expected` or `expectedJson`), `policy` | atomic checked replacement (`Doc.commit`): the new revision, the delta and the view, or a located refusal | `Doc.commit_sound`, `SourceSession.reached_view` |
| `fill` | `path`, `replacement` (hex) or `replacementJson` (and optional target) | with a target, `Doc.commit`; without, `Doc.draft` | `Doc.commit_sound` or the law the delta took, `SourceSession.feed_coherent`, `SourceSession.reached_view` |
| `omit` | `path`, `holeName` (and optional target) | with a target, `Doc.commit`; without, `Doc.draft` | the same |
| `draft` | `path`, and `replacement` / `replacementJson` or `holeName` | raw unchecked edit (`Doc.draft`) | the law the delta took, `SourceSession.feed_coherent`, `SourceSession.reached_view` |
| `fork` | `docName` (optional) | forks the open document with a fresh generation | none |
| `view` | `path`, or none | at an address, its entry and its focus; with none, the whole table | `SourceSession.reached_view`; `SourceSession.focusAt_typed` at an address |
| `undo` | nothing | the last fill taken back at a new revision (`Doc.undo`): the delta and the view | `SourceSession.feed_undo` |
| `journal` | nothing | each edit, its address and its delta | none |
| `sketch` | nothing | the sketch and the application as JSON, and as bytes with `hex` | `Sketch.decode_exact`, `Canonical.decode_exact` |
| `catalogue` | nothing; open or not | the program's forms, the atoms with their typing schemes, the application's rows by index (`Tools.Catalogue`) | `Canonical.ofJsonAnyOrder_exact`, `NativeAtom.atom_table_wf` |
| `start` | nothing | admits the sketch at `app.withHoles`, opens a `Live` session, feeds `.start`, and answers the live view | `Sketch.sourceCheck_of_admitted`, `Live.reached` |
| `receive` | `fiber`, `token` or `rowName`; `answer` or `answerJson` | feeds `.receive` into the live session and answers the verdict and live view | `Live.reached` |
| `apply` | `fiber`, `token` or `rowName` | feeds `.apply` and `.flush` into the live session and answers the verdict and live view | `Live.reached` |
| `liveView` | nothing | the live session's outcome, exit, and waiting calls with keys and checked instances | `Live.reached`, `Live.view_awaits`, `Live.view_checked` |
| `save` | `hex` (optional) | the live session saved as a `LiveRecord` (`recordJson` and `record`) | `LiveRecord.restore_save`, `LiveRecord.decode_encode` |
| `load` | `record` (hex) or `recordJson` | restores a `LiveRecord`, replacing the tool's live session, and answers the live view | `LiveRecord.restore_save`, `Live.reached` |
| `run` | `answers` (hex) or `answersJson`, a script of `(row, answer)` pairs, if any | the outcome, the exit (`ExitV`) and any waiting calls through `Live.feedAll`; `syncExit` (`Api.Built.runSync`) when closed | `Live.reached` |
| `settle` | `tapeJson`, the replies in call order as exits, if any; `limit` | the least budget whose call tree's run is not cut, and that run: `finished`, `waiting` or, past the limit, `unsettled` (`Tree.settle`) | `Tree.settle_sound`, `Tree.probe_stable` |
| `frames` | `tapeJson`, `limit` | the call tree's run at each budget from 0 to `limit` (`Tree.frames`) | `Tree.ofProgram_approx` |
| `explore` | `budget`, `width` | every path of the call tree at the budget, each reply drawn from its row's types, with its tape (`Kit.explore`) | `Tree.ofProgram_approx` |

**The delta names its law.** An edit of the sketch as written that moves the expansion at its
address alone is the expansion's own edit. A fill that splices names `Sketch.table_fill`, an
omission that splices names `Sketch.table_omit`, and an edit that checks again names
`Sketch.annotate_eq_table`, each at the expansion. A delta's addresses are the source's: those of
a copy are dropped (`Edit.Delta.atSource`).

**The focus at an address** is the sub-program as written, with the environment and the type the
table holds there: the expansion's focus (`SourceSession.focusAt_typed`).

**An undo of an omission** puts the program back, and keeps the hole row it declared: the law of
undo is stated for a fill.

**What it is not.** It is no MCP server: an MCP tool is a thin wrapper over `answerLine`. It
holds one session. It does not admit the application's signature (`admitSig`) at `open`: it shows
the checker's answers at that signature (the open part `sketch-admission` of R14), and `run`
admits the sketch at the application extended by its holes (`admitProgram`).
-/

namespace Tools.Session

open Lean (Json ToJson toJson)
open Effect4 (ServiceKey)
open Effect4.Program Effect4.Program.Wire Effect4.Store
open Tools.Query (Answer refused effTyJson refusalJson entryJson focusJson holeRow optField)
open Tools.JsonBridge (printJson valueFrom? toHex locate)

/-- **The tool's state**: the session, once opened, its document identity and revision, its
journal, the latest step first, the next opening generation, its persistent live session, and the
name of its application. -/
structure State where
  /-- the edit session of the sketch as written, once opened -/
  source : Option SourceSession := none
  /-- the journal, the latest step first -/
  journal : List Edit.Step := []
  /-- the application's name: `empty`, or the digest of its canonical bytes -/
  app : String := "empty"
  /-- the open document's identity -/
  docId : DocId := {}
  /-- the open document's revision -/
  revision : Nat := 0
  /-- the next generation counter allocated on `open` or `fork` -/
  generation : Nat := 0
  /-- the persistent live session, once started or loaded -/
  live : Option Effect4.Live := none

/-- **What the session shows, as an edit session**: the application, the sketch as written and
the table at the source's addresses (`SourceSession.shown`). The view tools draw it. -/
def State.session (st : State) : Option EditSession := st.source.map SourceSession.shown

/-- The open document (`Doc`), when a session is open. -/
def State.doc (st : State) : Option Doc :=
  st.source.map fun s => ⟨st.docId, s, st.revision⟩

/-- Store an updated document (`Doc`) in the tool state. -/
def State.withDoc (st : State) (d : Doc) : State :=
  { st with source := some d.session, docId := d.id, revision := d.revision }

/-- One request. -/
structure Request where
  op : String
  program : Option String := none
  holes : Option String := none
  path : List Nat := []
  replacement : Option String := none
  holeName : String := "h0"
  id : Option Json := none
  /-- the program as its JSON print, in place of `program` -/
  programJson : Option Json := none
  /-- the filling as its JSON print, in place of `replacement` -/
  replacementJson : Option Json := none
  /-- the application's row table, as its canonical bytes in hex -/
  rows : Option String := none
  /-- the application's service declarations, as their canonical bytes in hex -/
  services : Option String := none
  /-- the hole table as its JSON print, in place of `holes` -/
  holesJson : Option Json := none
  /-- the row table as its JSON print, in place of `rows` -/
  rowsJson : Option Json := none
  /-- the service declarations as their JSON print, in place of `services` -/
  servicesJson : Option Json := none
  /-- whether answers carry canonical bytes in hex beside the JSON; by default they do not -/
  hex : Bool := false
  /-- the host answers for `run`, as canonical bytes of `List (String × Api.HostSession.Answer)` in hex -/
  answers : Option String := none
  /-- the host answers for `run` as their JSON print, in place of `answers` -/
  answersJson : Option Json := none
  /-- the replies for `settle` and `frames`, in call order: the JSON print of a list of exits -/
  tapeJson : Option Json := none
  /-- the largest budget `settle` tries, and the last of `frames` -/
  limit : Nat := 256
  /-- the budget of `explore` -/
  budget : Nat := 64
  /-- the most paths `explore` answers -/
  width : Nat := 64
  /-- the application's named type declarations, as their canonical bytes in hex -/
  types : Option String := none
  /-- the named type declarations as their JSON print, in place of `types` -/
  typesJson : Option Json := none
  /-- the document name for `open`, `fork`, or an edit target -/
  docName : Option String := none
  /-- the document generation of an edit target -/
  docGeneration : Option Nat := none
  /-- the expected revision of an edit target -/
  revision : Option Nat := none
  /-- the expected sub-program at an edit target, as canonical bytes in hex -/
  expected : Option String := none
  /-- the expected sub-program at an edit target, as its JSON print -/
  expectedJson : Option Json := none
  /-- the validation policy for `Doc.commit`: `"keepExactType"` (default) or `"recheckSource"` -/
  policy : Option String := none
  /-- the fiber id of a call key or fiber selector for `receive` and `apply` -/
  fiber : Option Nat := none
  /-- the guard token of a call key selector for `receive` and `apply` -/
  token : Option Nat := none
  /-- the row spelling of a row selector for `receive` and `apply` -/
  rowName : Option String := none
  /-- one host answer for `receive`, as canonical bytes in hex -/
  answer : Option String := none
  /-- one host answer for `receive` as its JSON print, in place of `answer` -/
  answerJson : Option Json := none
  /-- a saved live record (`LiveRecord.Tuple`) for `load`, as canonical bytes in hex -/
  record : Option String := none
  /-- a saved live record (`LiveRecord.Tuple`) for `load`, as its JSON print -/
  recordJson : Option Json := none

/-- Whether a request supplies an explicit edit target (`revision`, `expected`, `docName`, or
`docGeneration`). -/
def Request.hasTarget (r : Request) : Bool :=
  r.revision.isSome || r.expected.isSome || r.expectedJson.isSome ||
    r.docName.isSome || r.docGeneration.isSome

/-- Read a request; a field of the wrong type is refused with its name. -/
def Request.fromJson? (j : Json) : Except String Request := do
  let op ← j.getObjValAs? String "op"
  let program ← optField j "program" (Lean.fromJson? (α := String))
  let holes ← optField j "holes" (Lean.fromJson? (α := String))
  let path ← optField j "path" (Lean.fromJson? (α := List Nat))
  let replacement ← optField j "replacement" (Lean.fromJson? (α := String))
  let holeName ← optField j "holeName" (Lean.fromJson? (α := String))
  let id := (j.getObjVal? "id").toOption
  let programJson := (j.getObjVal? "programJson").toOption
  let replacementJson := (j.getObjVal? "replacementJson").toOption
  let rows ← optField j "rows" (Lean.fromJson? (α := String))
  let services ← optField j "services" (Lean.fromJson? (α := String))
  let types ← optField j "types" (Lean.fromJson? (α := String))
  let hex ← optField j "hex" (Lean.fromJson? (α := Bool))
  let answers ← optField j "answers" (Lean.fromJson? (α := String))
  let limit ← optField j "limit" (Lean.fromJson? (α := Nat))
  let budget ← optField j "budget" (Lean.fromJson? (α := Nat))
  let width ← optField j "width" (Lean.fromJson? (α := Nat))
  let docName ← optField j "docName" (Lean.fromJson? (α := String))
  let docGeneration ← optField j "docGeneration" (Lean.fromJson? (α := Nat))
  let revision ← optField j "revision" (Lean.fromJson? (α := Nat))
  let expected ← optField j "expected" (Lean.fromJson? (α := String))
  let expectedJson := (j.getObjVal? "expectedJson").toOption
  let policy ← optField j "policy" (Lean.fromJson? (α := String))
  let fiber ← optField j "fiber" (Lean.fromJson? (α := Nat))
  let token ← optField j "token" (Lean.fromJson? (α := Nat))
  let rowName ← optField j "rowName" (Lean.fromJson? (α := String))
  let answer ← optField j "answer" (Lean.fromJson? (α := String))
  let answerJson := (j.getObjVal? "answerJson").toOption
  let record ← optField j "record" (Lean.fromJson? (α := String))
  let recordJson := (j.getObjVal? "recordJson").toOption
  return Request.mk op program holes (path.getD []) replacement (holeName.getD "h0") id
    programJson replacementJson rows services (j.getObjVal? "holesJson").toOption
    (j.getObjVal? "rowsJson").toOption (j.getObjVal? "servicesJson").toOption (hex.getD false)
    answers (j.getObjVal? "answersJson").toOption (j.getObjVal? "tapeJson").toOption
    (limit.getD 256) (budget.getD 64) (width.getD 64) types (j.getObjVal? "typesJson").toOption
    docName docGeneration revision expected expectedJson policy fiber token rowName answer
    answerJson record recordJson

/-- Write a request, as `Request.fromJson?` reads it. -/
def Request.toJson (r : Request) : Json :=
  Json.mkObj <|
    [("op", .str r.op), ("path", Lean.toJson r.path), ("holeName", .str r.holeName)] ++
    (r.program.map fun hex => ("program", Json.str hex)).toList ++
    (r.holes.map fun hex => ("holes", Json.str hex)).toList ++
    (r.replacement.map fun hex => ("replacement", Json.str hex)).toList ++
    (r.programJson.map fun j => ("programJson", j)).toList ++
    (r.replacementJson.map fun j => ("replacementJson", j)).toList ++
    (r.rows.map fun hex => ("rows", Json.str hex)).toList ++
    (r.services.map fun hex => ("services", Json.str hex)).toList ++
    (r.types.map fun hex => ("types", Json.str hex)).toList ++
    (r.holesJson.map fun j => ("holesJson", j)).toList ++
    (r.rowsJson.map fun j => ("rowsJson", j)).toList ++
    (r.servicesJson.map fun j => ("servicesJson", j)).toList ++
    (r.typesJson.map fun j => ("typesJson", j)).toList ++
    (r.answers.map fun hex => ("answers", Json.str hex)).toList ++
    (r.answersJson.map fun j => ("answersJson", j)).toList ++
    (r.tapeJson.map fun j => ("tapeJson", j)).toList ++
    (r.docName.map fun s => ("docName", Json.str s)).toList ++
    (r.docGeneration.map fun n => ("docGeneration", Lean.toJson n)).toList ++
    (r.revision.map fun n => ("revision", Lean.toJson n)).toList ++
    (r.expected.map fun hex => ("expected", Json.str hex)).toList ++
    (r.expectedJson.map fun j => ("expectedJson", j)).toList ++
    (r.policy.map fun s => ("policy", Json.str s)).toList ++
    (r.fiber.map fun n => ("fiber", Lean.toJson n)).toList ++
    (r.token.map fun n => ("token", Lean.toJson n)).toList ++
    (r.rowName.map fun s => ("rowName", Json.str s)).toList ++
    (r.answer.map fun hex => ("answer", Json.str hex)).toList ++
    (r.answerJson.map fun j => ("answerJson", j)).toList ++
    (r.record.map fun hex => ("record", Json.str hex)).toList ++
    (r.recordJson.map fun j => ("recordJson", j)).toList ++
    [("limit", Lean.toJson r.limit), ("budget", Lean.toJson r.budget), ("width", Lean.toJson r.width)] ++
    (if r.hex then [("hex", Json.bool true)] else []) ++
    (r.id.map fun id => ("id", id)).toList

/-- **A refusal of a carrier that does not read**: where its JSON was given and the walk finds
the place it leaves its shape (`Tools.JsonBridge.locate`), the answer's result names the place,
what the shape wants there and what stands there. -/
def unreadable {α : Type} [Canonical α] (op why : String) (json : Option Json)
    (id : Option Json) : Answer :=
  match json.bind (locate (α := α)) with
  | some miss => { op, ok := false, result := miss.toJson, error := some why, id }
  | none => refused op why id

/-- A list a request may leave out, which is then empty: its value, or `none` where what is given
does not read; with the laws its reading names. -/
def listFrom? {α : Type} [Canonical (List α)] (hex : Option String) (json : Option Json) :
    Option (List α) × List Lean.Name :=
  match valueFrom? hex json with
  | some (value, laws) => (value, laws)
  | none => (some [], [])

/-- **The application's name**: `empty` for the empty application, and otherwise `sha256:` and
the digest of the canonical bytes of its row table and its declarations. -/
def appName (app : SigApp) : String :=
  if app.rows.isEmpty && app.services.isEmpty && app.types.isEmpty then "empty"
  else "sha256:" ++ (sha256 (Canonical.encode (app.rows, app.services, app.types))).hex

/-- A document identity as JSON. -/
def docIdJson (id : DocId) : Json :=
  Json.mkObj [("name", .str id.name), ("generation", toJson id.generation)]

/-- An edit target as JSON. -/
def targetJson (t : EditTarget) (hex : Bool := false) : Json :=
  Json.mkObj <|
    [("doc", docIdJson t.doc), ("revision", toJson t.revision), ("path", toJson t.path),
      ("expectedJson", printJson t.expected)] ++
    if hex then [("expected", .str (toHex t.expected))] else []

/-- An atomic edit refusal (`Doc.Refusal`) as JSON. -/
def editRefusalJson (sig : Signature NativeOp) (prog : Option NativeEff) :
    Doc.Refusal → Json
  | .foreign expected =>
    Json.mkObj [("reason", .str "foreign"), ("expectedDoc", docIdJson expected)]
  | .stale current =>
    Json.mkObj [("reason", .str "stale"), ("currentRevision", toJson current)]
  | .moved =>
    Json.mkObj [("reason", .str "moved")]
  | .noFocus =>
    Json.mkObj [("reason", .str "noFocus")]
  | .refused why =>
    Json.mkObj [("reason", .str "refused"),
      ("refusals", Json.arr (why.map fun r => refusalJson r prog sig).toArray)]
  | .typeChanged old new =>
    Json.mkObj [("reason", .str "typeChanged"),
      ("old", match old with | some t => effTyJson t | none => .null),
      ("new", effTyJson new)]
  | .localChanged old new =>
    Json.mkObj [("reason", .str "localChanged"),
      ("old", match old with | some (_, t) => effTyJson t | none => .null),
      ("new", match new with | some (_, t) => effTyJson t | none => .null)]

/-- Parse the validation policy of `Doc.commit`. -/
def policyFrom? : Option String → Option Policy
  | none | some "keepExactType" => some .keepExactType
  | some "recheckSource" => some .recheckSource
  | _ => none

/-- What a delta says. -/
def deltaJson : Edit.Delta → Json
  | .unchanged => Json.mkObj [("kind", .str "unchanged")]
  | .spliced shown => Json.mkObj [("kind", .str "spliced"), ("shown", toJson shown)]
  | .rechecked => Json.mkObj [("kind", .str "rechecked")]

/-- The laws behind a delta, by the edit that made it: the law the expansion's edit session took,
and the law that keeps the session through the references. -/
def deltaLaws : Edit → Edit.Delta → List Lean.Name
  | .fill _ _, .spliced _ => [``Sketch.table_fill, ``SourceSession.feed_coherent]
  | .omitAt _ _, .spliced _ => [``Sketch.table_omit, ``SourceSession.feed_coherent]
  | _, .rechecked => [``Sketch.annotate_eq_table, ``SourceSession.feed_coherent]
  | _, .unchanged => []

/-- The session's view, in short: its type and its refusals, and how many entries it has. -/
def viewJson (l : SourceSession) : Json :=
  let v := l.view
  let sig := (l.app.withHoles l.sketch.holes).signature
  Json.mkObj [("type", match v.type with
      | some t => effTyJson t
      | none => .null),
    ("refusals",
      Json.arr (v.refusals.map fun r => refusalJson r (some l.sketch.program) sig).toArray),
    ("entries", toJson v.table.length)]

/-- One step of the journal. -/
def stepJson (s : Edit.Step) : Json :=
  Json.mkObj [("edit", .str (match s.edit with
      | .fill _ _ => "fill"
      | .omitAt _ _ => "omit")),
    ("path", toJson s.edit.path), ("delta", deltaJson s.delta)]

/-- A step of the call tree's run: a host call, or a cell operation. -/
def treeStepJson : Effect4.Run.Tree.Step → Json
  | .called row request answer =>
    Json.mkObj [("row", toJson row), ("request", printJson request), ("answer", printJson answer)]
  | .celled _ value => Json.mkObj [("cell", printJson value)]

/-- How the call tree's run stopped. -/
def treeStopJson : Effect4.Run.Tree.Stop → List (String × Json)
  | .finished exit => [("status", .str "finished"), ("exit", printJson exit)]
  | .cut => [("status", .str "cut")]
  | .waiting row request =>
    [("status", .str "waiting"),
      ("waiting", Json.mkObj [("row", toJson row), ("request", printJson request)])]

/-- A run of the call tree: how it stopped, its steps, and any further fields. -/
def treeRunJson (stop : Effect4.Run.Tree.Stop) (steps : List Effect4.Run.Tree.Step)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj (extra ++ treeStopJson stop ++ [("steps", Json.arr (steps.map treeStepJson).toArray)])

/-- Parse a call selector (`Effect4.Run.Sel`) from `req`'s `fiber`, `token`, or `rowName`. -/
def selFrom? (req : Request) : Option Effect4.Run.Sel :=
  match req.fiber, req.token, req.rowName with
  | some f, some t, _ => some (.key ⟨⟨f⟩, t⟩)
  | some f, none, _ => some (.fiber ⟨f⟩)
  | none, _, some r => some (.row r)
  | none, _, none => none

/-- A call's checked instance (`CallInstance NativeOp`) as JSON. -/
def callInstanceJson (c : CallInstance NativeOp) : Json :=
  Json.mkObj [("request", printJson c.request), ("answer", printJson c.answer),
    ("error", printJson c.error)]

/-- One waiting call (`Live.CallView`) as JSON, with its key and checked instance. -/
def callViewJson (s : Effect4.Run) (c : Effect4.Live.CallView) : Json :=
  let row := match s.rowOf c.await.op with
    | some r => r.spelling
    | none => ""
  Json.mkObj [("row", .str row),
    ("key", Json.mkObj [("fiber", toJson c.await.fiber.value), ("token", toJson c.await.token)]),
    ("fiber", toJson c.await.fiber.value),
    ("token", toJson c.await.token),
    ("request", printJson c.await.request),
    ("origin", match c.origin with | some p => toJson p | none => .null),
    ("checked", match c.checked with | some inst => callInstanceJson inst | none => .null)]

/-- The live session's view as JSON: outcome, exit, and waiting calls with keys and checked
instances. -/
def liveViewJson (l : Effect4.Live) : Json :=
  let v := l.view
  let waiting := v.awaiting.map (callViewJson l.run)
  Json.mkObj [("session", .str l.run.id),
    ("outcome", printJson v.outcome),
    ("exit", match v.exit with | some exit => printJson exit | none => .null),
    ("waiting", Json.arr waiting.toArray),
    ("steps", toJson v.steps),
    ("applied", toJson v.applied),
    ("funded", toJson v.funded),
    ("atRest", toJson v.atRest)]

/-- A live feed verdict (`Effect4.Run.Verdict`) as JSON. -/
def verdictJson : Effect4.Run.Verdict → Json
  | .played phases =>
    Json.mkObj [("kind", .str "played"), ("phases", Json.arr (phases.map printJson).toArray)]
  | .unresolved sel =>
    let selJson := match sel with
      | .key k =>
        Json.mkObj [("kind", .str "key"), ("fiber", toJson k.fiber.value), ("token", toJson k.token)]
      | .fiber f => Json.mkObj [("kind", .str "fiber"), ("fiber", toJson f.value)]
      | .row r => Json.mkObj [("kind", .str "row"), ("row", .str r)]
    Json.mkObj [("kind", .str "unresolved"), ("selector", selJson)]

/-- Feed one draft edit (`Doc.draft`), record it, and answer its delta and the view. -/
def feedAnswer (st : State) (d : Doc) (req : Request) (e : Edit)
    (readLaws : List Lean.Name := []) : State × Answer :=
  let (d', step) := d.draft e
  ({ (st.withDoc d') with journal := step :: st.journal },
    { op := req.op, app := st.app,
      laws := readLaws ++ deltaLaws e step.delta ++ [``SourceSession.reached_view],
      ok := true,
      result := Json.mkObj [("doc", docIdJson d'.id), ("revision", toJson d'.revision),
        ("delta", deltaJson step.delta), ("view", viewJson d'.session)],
      id := req.id })

/-- Run an atomic checked edit (`Doc.commit`) from `req`'s target and policy. -/
def commitAnswer (st : State) (d : Doc) (req : Request) (c : Change)
    (readLaws : List Lean.Name := []) : State × Answer :=
  match policyFrom? req.policy with
  | none => (st, refused req.op "unknown policy" req.id)
  | some policy =>
    let expected? : Option (Option NativeEff × List Lean.Name) :=
      match valueFrom? (α := NativeEff) req.expected req.expectedJson with
      | some p => some p
      | none =>
        match (Node.eff d.session.sketch.program).at_ req.path with
        | some (.eff q) => some (some q, [])
        | _ => some (none, [])
    match expected? with
    | none | some (none, _) =>
      if req.expected.isSome || req.expectedJson.isSome then
        (st, unreadable (α := NativeEff) req.op "the expected sub-program does not read"
          req.expectedJson req.id)
      else (st, refused req.op "no part of the sketch at the address" req.id)
    | some (some exp, expLaws) =>
      let targetDoc : DocId :=
        ⟨req.docName.getD d.id.name, req.docGeneration.getD d.id.generation⟩
      let targetRev : Nat := req.revision.getD d.revision
      let target : EditTarget := ⟨targetDoc, targetRev, req.path, exp⟩
      let sig := (d.session.app.withHoles d.session.sketch.holes).signature
      match d.commit target c policy with
      | .error why =>
        (st,
          { op := req.op, app := st.app, laws := readLaws ++ expLaws, ok := false,
            result := editRefusalJson sig (some d.session.sketch.program) why,
            error := some ("the atomic edit is refused: " ++ why.reason), id := req.id })
      | .ok d' =>
        let step : Edit.Step :=
          match d.editOf target c with
          | some e => (d.session.feedStep e).2
          | none => ⟨.fill req.path exp, some exp, .unchanged⟩
        ({ (st.withDoc d') with journal := step :: st.journal },
          { op := req.op, app := st.app,
            laws := (readLaws ++ expLaws ++ deltaLaws step.edit step.delta ++
              [``Doc.commit_sound, ``SourceSession.reached_view]).eraseDups,
            ok := true,
            result := Json.mkObj [("doc", docIdJson d'.id), ("revision", toJson d'.revision),
              ("delta", deltaJson step.delta), ("view", viewJson d'.session)],
            id := req.id })

/-- **Answer one request**, from the state before it, with the state after it. -/
def answer (st : State) (req : Request) : State × Answer :=
  let none' (why : String) : State × Answer := (st, refused req.op why req.id)
  match req.op with
  | "open" =>
    let (program?, programLaws) := ((valueFrom? (α := NativeEff) req.program req.programJson).getD
      (none, []))
    let (holes?, holeLaws) := listFrom? (α := Row) req.holes req.holesJson
    let (rows?, rowLaws) := listFrom? (α := Row) req.rows req.rowsJson
    let (services?, serviceLaws) := listFrom? (α := ServiceKey × Ty) req.services req.servicesJson
    let (types?, typeLaws) := listFrom? (α := String × Ty) req.types req.typesJson
    let readLaws := (programLaws ++ holeLaws ++ rowLaws ++ serviceLaws ++ typeLaws).eraseDups
    match program?, holes?, rows?, services?, types? with
    | none, _, _, _, _ =>
      (st, unreadable (α := NativeEff) req.op "the program does not read" req.programJson req.id)
    | _, none, _, _, _ =>
      (st, unreadable (α := RowTable) req.op "the hole table does not read" req.holesJson req.id)
    | _, _, none, _, _ =>
      (st, unreadable (α := RowTable) req.op "the row table does not read" req.rowsJson req.id)
    | _, _, _, none, _ =>
      (st, unreadable (α := List (ServiceKey × Ty)) req.op "the service declarations do not read"
        req.servicesJson req.id)
    | _, _, _, _, none =>
      (st, unreadable (α := TyDecls) req.op "the type declarations do not read"
        req.typesJson req.id)
    | some program, some holes, some rows, some services, some types =>
      let app : SigApp := ⟨rows, services, types⟩
      let name := appName app
      let docId : DocId := ⟨req.docName.getD "default", st.generation⟩
      let d := Doc.open app { program, holes } docId
      ({ source := some d.session, journal := [], app := name,
          docId := d.id, revision := d.revision, generation := st.generation + 1,
          live := st.live },
        Answer.mk req.op name (readLaws ++ [``SourceSession.reached_view]) true
          (viewJson d.session) none req.id)
  | "catalogue" =>
    let rows := (st.source.map (·.app.rows)).getD []
    (st, Answer.mk req.op st.app [``Canonical.ofJsonAnyOrder_exact, ``NativeAtom.atom_table_wf] true
      (Tools.Catalogue.catalogueJson rows) none req.id)
  | "receive" =>
    match st.live with
    | none => none' "no live session is open"
    | some live =>
      match selFrom? req with
      | none => none' "a call selector is required"
      | some sel =>
        match valueFrom? (α := Effect4.Api.HostSession.Answer) req.answer req.answerJson with
        | some (some ans, ansLaws) =>
          let (live', verdict) := live.feed (.receive sel ans)
          let ok := match verdict with | .played _ => true | .unresolved _ => false
          ({ st with live := some live' },
            { op := req.op, app := st.app,
              laws := (ansLaws ++ [``Effect4.Live.reached]).eraseDups,
              ok := ok,
              result := Json.mkObj [("verdict", verdictJson verdict), ("live", liveViewJson live')],
              error := if ok then none else some "the call selector is unresolved",
              id := req.id })
        | _ =>
          (st, unreadable (α := Effect4.Api.HostSession.Answer) req.op
            "the host answer does not read" req.answerJson req.id)
  | "apply" =>
    match st.live with
    | none => none' "no live session is open"
    | some live =>
      match selFrom? req with
      | none => none' "a call selector is required"
      | some sel =>
        let (live1, verdict) := live.feed (.apply sel)
        let (live', ok) := match verdict with
          | .played _ => ((live1.feed .flush).1, true)
          | .unresolved _ => (live1, false)
        ({ st with live := some live' },
          { op := req.op, app := st.app,
            laws := [``Effect4.Live.reached],
            ok := ok,
            result := Json.mkObj [("verdict", verdictJson verdict), ("live", liveViewJson live')],
            error := if ok then none else some "the call selector is unresolved",
            id := req.id })
  | "liveView" =>
    match st.live with
    | none => none' "no live session is open"
    | some live =>
      (st, Answer.mk req.op st.app
        [``Effect4.Live.reached, ``Effect4.Live.view_awaits, ``Effect4.Live.view_checked] true
        (liveViewJson live) none req.id)
  | "save" =>
    match st.live with
    | none => none' "no live session is open"
    | some live =>
      let saved := Effect4.LiveRecord.save live
      let result := Json.mkObj <|
        [("recordJson", printJson saved.toTuple)] ++
        if req.hex then [("record", .str (toHex saved.toTuple))] else []
      (st, Answer.mk req.op st.app
        [``Effect4.LiveRecord.restore_save, ``Effect4.LiveRecord.decode_encode] true result none
        req.id)
  | "load" =>
    match valueFrom? (α := Effect4.LiveRecord.Tuple) req.record req.recordJson with
    | some (some tuple, recLaws) =>
      let saved := Effect4.LiveRecord.ofTuple tuple
      match Effect4.LiveRecord.restore saved with
      | .error (.unsupportedVersion v) =>
        (st,
          { op := req.op, app := st.app,
            laws := (recLaws ++ [``Effect4.LiveRecord.restore_unsupportedVersion]).eraseDups,
            ok := false,
            result := Json.mkObj [("reason", .str "unsupportedVersion"), ("version", toJson v)],
            error := some s!"unsupported live record version {v}", id := req.id })
      | .error (.admission why) =>
        (st,
          { op := req.op, app := st.app, laws := recLaws, ok := false,
            result := Json.mkObj [("reason", .str "admission"), ("refusal", printJson why)],
            error := some "the saved live record failed program admission", id := req.id })
      | .ok live' =>
        let st' := { st with live := some live' }
        (st', Answer.mk req.op st.app
          (recLaws ++ [``Effect4.LiveRecord.restore_save, ``Effect4.Live.reached]).eraseDups true
          (liveViewJson live') none req.id)
    | _ =>
      (st, unreadable (α := Effect4.LiveRecord.Tuple) req.op "the live record does not read"
        req.recordJson req.id)
  | op =>
    match st.doc with
    | none => none' "no session is open"
    | some d =>
      let l := d.session
      let sig := (l.app.withHoles l.sketch.holes).signature
      match op with
      | "inspect" =>
        match d.inspect req.path with
        | none => none' "no part of the sketch at the address"
        | some ins =>
          let result := Json.mkObj
            [("target", targetJson ins.target req.hex),
              ("focus", focusJson ins.focus req.hex),
              ("entry", match ins.entry with
                | some e => entryJson e (some l.sketch.program) sig
                | none => .null),
              ("refusal", match ins.refusal with
                | some r => refusalJson r (some l.sketch.program) sig
                | none => .null)]
          (st, Answer.mk op st.app [``SourceSession.reached_view, ``SourceSession.focusAt_typed]
            true result none req.id)
      | "replace" | "commit" =>
        match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
        | some (some q, readLaws) => commitAnswer st d req (.fill q) readLaws
        | none => commitAnswer st d req (.omitHole req.holeName) []
        | _ =>
          (st, unreadable (α := NativeEff) req.op "the filling does not read" req.replacementJson req.id)
      | "fill" =>
        match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
        | some (some q, readLaws) =>
          if req.hasTarget then commitAnswer st d req (.fill q) readLaws
          else if (l.sketch.fillAt req.path q).isSome then feedAnswer st d req (.fill req.path q) readLaws
          else none' "no part of the sketch at the address"
        | _ =>
          (st, unreadable (α := NativeEff) req.op "the filling does not read" req.replacementJson req.id)
      | "omit" =>
        if req.hasTarget then commitAnswer st d req (.omitHole req.holeName) []
        else
          match l.focusAt req.path with
          | none => none' "no focus at the address"
          | some f => feedAnswer st d req (.omitAt req.path (holeRow req.holeName f))
      | "draft" =>
        match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
        | some (some q, readLaws) =>
          if (l.sketch.fillAt req.path q).isSome then feedAnswer st d req (.fill req.path q) readLaws
          else none' "no part of the sketch at the address"
        | none =>
          match l.focusAt req.path with
          | none => none' "no focus at the address"
          | some f => feedAnswer st d req (.omitAt req.path (holeRow req.holeName f))
        | _ =>
          (st, unreadable (α := NativeEff) req.op "the filling does not read" req.replacementJson req.id)
      | "fork" =>
        let newId : DocId := ⟨req.docName.getD d.id.name, st.generation⟩
        let d' := d.fork newId
        let st' := { (st.withDoc d') with generation := st.generation + 1 }
        let result := Json.mkObj [("doc", docIdJson d'.id), ("revision", toJson d'.revision),
          ("view", viewJson d'.session)]
        (st', Answer.mk op st.app [``SourceSession.reached_view] true result none req.id)
      | "view" =>
        if req.path.isEmpty then
          let result := Json.mkObj [("doc", docIdJson d.id), ("revision", toJson d.revision),
            ("view", viewJson l),
            ("table",
              Json.arr (l.table.map fun e => entryJson e (some l.sketch.program) sig).toArray)]
          (st, Answer.mk op st.app [``SourceSession.reached_view] true result none req.id)
        else
          let entry := match l.table.find? fun e => decide (e.path = req.path) with
            | some e => entryJson e (some l.sketch.program) sig
            | none => .null
          let result := Json.mkObj [("doc", docIdJson d.id), ("revision", toJson d.revision),
            ("entry", entry), ("focus", focusJson (l.focusAt req.path) req.hex)]
          (st, Answer.mk op st.app [``SourceSession.reached_view, ``SourceSession.focusAt_typed]
            true result none req.id)
      | "undo" =>
        match st.journal with
        | step :: rest =>
          match step.replaced with
          | some old =>
            let (d', back) := d.undo step.edit.path old
            ({ (st.withDoc d') with journal := rest },
              { op := op, app := st.app,
                laws := [``SourceSession.feed_undo, ``SourceSession.reached_view], ok := true,
                result := Json.mkObj [("doc", docIdJson d'.id), ("revision", toJson d'.revision),
                  ("delta", deltaJson back.delta), ("view", viewJson d'.session)],
                id := req.id })
          | none => none' "the last edit replaced no program"
        | [] => none' "the journal is empty"
      | "journal" =>
        let result := Json.arr (st.journal.reverse.map stepJson).toArray
        (st, Answer.mk op st.app [] true result none req.id)
      | "sketch" =>
        let result := Json.mkObj <|
          (if req.hex then
            [("program", .str (toHex l.sketch.program)), ("holes", .str (toHex l.sketch.holes)),
              ("rows", .str (toHex l.app.rows)), ("services", .str (toHex l.app.services)),
              ("types", .str (toHex l.app.types))]
          else []) ++
          [("programJson", printJson l.sketch.program), ("holesJson", printJson l.sketch.holes),
            ("rowsJson", printJson l.app.rows), ("servicesJson", printJson l.app.services),
            ("typesJson", printJson l.app.types)]
        (st, Answer.mk op st.app [``Sketch.decode_exact, ``Canonical.decode_exact] true result
          none req.id)
      | "start" =>
        let app := l.app.withHoles l.sketch.holes
        let sourceType := match l.view.type with
          | some t => effTyJson t
          | none => .null
        match Effect4.Program.admitProgram l.sketch.program app with
        | .error why =>
          let result := Json.mkObj [("status", .str "refused"), ("sourceType", sourceType),
            ("refusal", printJson why)]
          (st, Answer.mk op st.app [``Sketch.sourceCheck_of_admitted] true result none req.id)
        | .ok admitted =>
          let rowNames := app.rows.zipIdx.map fun (r, i) => (r.spelling, i)
          let b : Effect4.Api.Built := { app, program := l.sketch.program, admitted, rowNames }
          let (live', verdict) := (Effect4.Live.open b st.app).feed .start
          let st' := { st with live := some live' }
          let result := Json.mkObj [("status", .str "ok"), ("sourceType", sourceType),
            ("verdict", verdictJson verdict), ("live", liveViewJson live')]
          (st', Answer.mk op st.app [``Sketch.sourceCheck_of_admitted, ``Effect4.Live.reached] true
            result none req.id)
      | "run" =>
        let (answers?, answerLaws) :=
          listFrom? (α := String × Effect4.Api.HostSession.Answer) req.answers req.answersJson
        match answers? with
        | none =>
          (st, unreadable (α := List (String × Effect4.Api.HostSession.Answer)) req.op
            "the host answers do not read" req.answersJson req.id)
        | some answers =>
          let app := l.app.withHoles l.sketch.holes
          let sourceType := match l.view.type with
            | some t => effTyJson t
            | none => .null
          match Effect4.Program.admitProgram l.sketch.program app with
          | .error why =>
            let result := Json.mkObj [("status", .str "refused"), ("sourceType", sourceType),
              ("refusal", printJson why)]
            (st, Answer.mk op st.app answerLaws true result none req.id)
          | .ok admitted =>
            let b : Effect4.Api.Built := { app, program := l.sketch.program, admitted }
            let events : List Effect4.Run.Event :=
              [.start] ++
              answers.flatMap (fun (row, ans) => [.receive (.row row) ans, .apply (.row row)]) ++
              [.flush]
            let run := ((Effect4.Live.open b st.app).feedAll events).run
            let waiting := (Effect4.Run.live run).map fun c =>
              Json.mkObj [("row", .str c.row), ("request", printJson c.request)]
            let result := Json.mkObj <|
              [("status", .str "ok"), ("sourceType", sourceType),
                ("outcome", printJson run.inspect.outcome),
                ("exit", match run.exit with
                  | some exit => printJson exit
                  | none => .null),
                ("waiting", Json.arr waiting.toArray)] ++
              (if answers.isEmpty && app.rows.isEmpty then [("syncExit", printJson b.runSync)] else [])
            (st, Answer.mk op st.app (answerLaws ++ [``Effect4.Live.reached]) true result none
              req.id)
      | "settle" | "frames" | "explore" =>
        let app := l.app.withHoles l.sketch.holes
        let tape? : Option (List Effect4.Machine.ExitV) := match req.tapeJson with
          | some j => Tools.JsonBridge.read? j
          | none => some []
        match tape? with
        | none =>
          (st, unreadable (α := List Effect4.Machine.ExitV) req.op "the tape does not read" req.tapeJson req.id)
        | some tape =>
          let program := l.sketch.program
          let host := Effect4.Run.Tree.Host.tape
          match op with
          | "settle" =>
            let result := match Effect4.Run.Tree.settle app.rows req.limit host tape program with
              | some (k, o) => treeRunJson o.stop o.steps [("budget", toJson k)]
              | none => Json.mkObj [("status", .str "unsettled"), ("limit", toJson req.limit),
                  ("note", .str "cut at every budget up to the limit: a finite probe, not a divergence")]
            (st, Answer.mk op st.app [``Effect4.Run.Tree.settle_sound, ``Effect4.Run.Tree.probe_stable]
              true result none req.id)
          | "frames" =>
            let frames := Effect4.Run.Tree.frames app.rows req.limit host tape program
            let result := Json.arr (frames.map fun o => treeRunJson o.stop o.steps).toArray
            (st, Answer.mk op st.app [``Effect4.Run.Tree.ofProgram_approx] true result none req.id)
          | _ =>
            let paths := Effect4.Run.Kit.explore app req.budget req.width program
            let result := Json.arr (paths.map fun p =>
              let tape := p.steps.filterMap fun
                | .called _ _ answer => some answer
                | .celled _ _ => none
              treeRunJson p.stop p.steps [("tape", printJson tape)]).toArray
            (st, Answer.mk op st.app [``Effect4.Run.Tree.ofProgram_approx] true result none req.id)
      | other => none' s!"unknown operation {other}"

/-- **Answer one line**, with the state after it. -/
def answerLine (st : State) (line : String) : State × String :=
  match Json.parse line with
  | .error why => (st, (toJson (refused "parse" s!"no JSON: {why}")).compress)
  | .ok j =>
    match Request.fromJson? j with
    | .error why => (st, (toJson (refused "request" why)).compress)
    | .ok req =>
      let (st', a) := answer st req
      (st', (toJson a).compress)

end Tools.Session
