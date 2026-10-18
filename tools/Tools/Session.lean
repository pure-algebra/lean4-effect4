import Tools.Query
import Tools.JsonBridge
import Tools.Catalogue
import Effect4.Laws.Store.ShapeRead
import Effect4.Program.Typing.SourceSession
import Effect4.Program.Typing.SourceDocument
import Effect4.Program.Typing.CheckCache
import Effect4.Program.Typing.FillSet
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.SourceDocument
import Effect4.Laws.Program.Typing.CheckCache
import Effect4.Laws.Program.FillSet
import Effect4.Laws.Program.SketchWire
import Effect4.Laws.Program.SketchAdmission
import Effect4.Api.RunnerDerived
import Effect4.Run.Live
import Effect4.Run.LiveRecord
import Effect4.Laws.Api.Live
import Effect4.Laws.Api.LiveRecord
import Effect4.Laws.Run.Tree
import Effect4.Run.Kit
import Effect4.Run.Preview
import Effect4.Laws.Api.Preview

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
| `replace` (also `fill`, `commit`) | `path`, `replacement` (hex) or `replacementJson`, the whole target (`docName`, `docGeneration`, `revision`, and `expected` or `expectedJson`), `policy` | atomic checked replacement (`Doc.step`): the new revision, the delta and the view, or a located refusal; a request without its replacement or any part of its target is refused | `Doc.commit_sound`, `SourceSession.reached_view` |
| `omit` | `path`, `holeName`, the whole target, `policy` | atomic checked omission (`Doc.step`): a hole row of the focus's type in the program's place | the same |
| `draft` | `path`, and `replacement` / `replacementJson` or `holeName` | the one unchecked edit (`Doc.draft`) | the law the delta took, `SourceSession.feed_coherent`, `SourceSession.reached_view` |
| `suggest` | `path`, `candidates` or `candidatesJson`, `limit`, `cursor` | candidate fillings at the focus, each with its cached or computed verdict (`CheckCache.suggest`) | `sketchSigData_signature`, `Check.Oracle.eq_uncached`, `Check.run_part_extends` |
| `fills.add` | `fills` or `fillsJson`, or `path` with `replacement` / `replacementJson` | each fill's outcome at the set's base (`FillSet.add`): applied, collapsed or refused at its address; a set opened at an earlier revision refuses | `FillSet.add_wf` |
| `fills.view` | nothing | the set's fills in the base's address order, its revision, and whether the document has moved past it | `ordered_congr` |
| `fills.reset` | nothing | a new set at the document's current revision, and the fills discarded | none |
| `fills.materialize` | nothing | the set published as one new revision (`FillSet.publication`), journaled as one edit at the root, or a refusal | `FillSet.add_wf`, `materialize_congr`, `ordered_compose`, `materialize_refFree` |
| `fork` | `docName` (optional) | forks the open document with a fresh generation | none |
| `view` | `path`, or none | at an address, its entry and its focus; with none, the whole table | `SourceSession.reached_view`; `SourceSession.focusAt_typed` at an address |
| `undo` | nothing | the last journaled edit taken back at a new revision (`Doc.step`): a checked or draft edit, or a published fill set; the delta and the view | `SourceSession.feed_undo` |
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

**A fill set follows the document while it is empty.** Once it holds a fill, it keeps the base its
fills were certified at. After any other edit it refuses new fills until `fills.reset`, and
`fills.materialize` refuses it as stale.

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
  document : Option Doc := none
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
  /-- the certified in-process memo across candidate searches -/
  cache : Check.Memo := Check.Memo.empty
  /-- the fixed-base fill set (`FillSet`) for parallel fills -/
  fills : Option FillSet := none

/-- **What the session shows, as an edit session**: the application, the sketch as written and
the table at the source's addresses (`SourceSession.shown`). The view tools draw it. -/
def State.session (st : State) : Option EditSession := st.source.map SourceSession.shown

/-- The open document (`Doc`), when a session is open. -/
def State.doc (st : State) : Option Doc :=
  st.document

/-- Store an updated document (`Doc`) in the tool state. -/
def State.withDoc (st : State) (d : Doc) : State :=
  { st with document := some d, source := some d.session, docId := d.id, revision := d.revision }

/-- The fill set the fill operations read: the stored one while it holds a fill, and otherwise a
new one at the open document's current revision. So an empty set follows the document, and a set
that holds fills keeps the base its fills were certified at. -/
def State.fillsFor (st : State) (d : Doc) : FillSet :=
  match st.fills with
  | some fs => if fs.entries.isEmpty then FillSet.open_ d else fs
  | none => FillSet.open_ d

/-- Whether a fill set was opened at another document or another revision than `d`'s current one:
its fills were certified at a base the document no longer holds. -/
def fillsStale (fs : FillSet) (d : Doc) : Bool :=
  fs.anchor.doc != d.id || fs.anchor.revision != d.revision || fs.base != d.session.sketch || fs.app != d.session.app

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
  /-- the validation policy for `Doc.step`: `"keepExactType"` (default) or `"recheckSource"` -/
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
  /-- the pagination cursor for `suggest` -/
  cursor : Nat := 0
  /-- optional extra candidate programs for `suggest`, as canonical bytes of `List NativeEff` in hex -/
  candidates : Option String := none
  /-- optional extra candidate programs for `suggest`, as their JSON print -/
  candidatesJson : Option Json := none
  /-- batch of `(path, filling)` pairs for `fills.add`, as canonical bytes in hex -/
  fills : Option String := none
  /-- batch of `(path, filling)` pairs for `fills.add`, as their JSON print -/
  fillsJson : Option Json := none

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
  let cursor ← optField j "cursor" (Lean.fromJson? (α := Nat))
  let candidates ← optField j "candidates" (Lean.fromJson? (α := String))
  let candidatesJson := (j.getObjVal? "candidatesJson").toOption
  let fills ← optField j "fills" (Lean.fromJson? (α := String))
  let fillsJson := (j.getObjVal? "fillsJson").toOption
  return Request.mk op program holes (path.getD []) replacement (holeName.getD "h0") id
    programJson replacementJson rows services (j.getObjVal? "holesJson").toOption
    (j.getObjVal? "rowsJson").toOption (j.getObjVal? "servicesJson").toOption (hex.getD false)
    answers (j.getObjVal? "answersJson").toOption (j.getObjVal? "tapeJson").toOption
    (limit.getD 256) (budget.getD 64) (width.getD 64) types (j.getObjVal? "typesJson").toOption
    docName docGeneration revision expected expectedJson policy fiber token rowName answer
    answerJson record recordJson (cursor.getD 0) candidates candidatesJson fills fillsJson

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
    (r.candidates.map fun hex => ("candidates", Json.str hex)).toList ++
    (r.candidatesJson.map fun j => ("candidatesJson", j)).toList ++
    (r.fills.map fun hex => ("fills", Json.str hex)).toList ++
    (r.fillsJson.map fun j => ("fillsJson", j)).toList ++
    [("limit", Lean.toJson r.limit), ("budget", Lean.toJson r.budget),
      ("width", Lean.toJson r.width), ("cursor", Lean.toJson r.cursor)] ++
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
def targetJson (snap : Snap) (path : List Nat) (expected : NativeEff) (hex : Bool := false) : Json :=
  Json.mkObj <| [("doc", docIdJson snap.doc), ("revision", toJson snap.revision),
    ("path", toJson path), ("expectedJson", printJson expected)] ++
    if hex then [("expected", .str (toHex expected))] else []

def localContextJson : Option (TyEnv × EffTy) → Json
  | none => .null
  | some (env,ty) => Json.mkObj [("env",printJson env),("type",effTyJson ty)]

def feedRefusalFields (sig : Signature NativeOp) (prog : Option NativeEff) :
    FeedRefusal → List (String × Json)
  | .noProgram path => [("reason",.str "noProgram"),("path",toJson path)]
  | .noFocus path => [("reason",.str "noFocus"),("path",toJson path)]
  | .notKept (env,expected) verdict => [("reason",.str "notKept"),
      ("env",printJson env),("expected",effTyJson expected),
      ("verdict",Tools.Query.checkJson verdict none sig)]
  | .refused why => [("reason",.str "refused"),
      ("refusals",Json.arr (why.map (fun r => refusalJson r prog sig)).toArray)]
  | .typeChanged old new => [("reason",.str "typeChanged"),
      ("old",match old with | none => .null | some ty => effTyJson ty),("new",effTyJson new)]
  | .localChanged old new => [("reason",.str "localChanged"),
      ("old",localContextJson old),("new",localContextJson new)]

def placeRefusalFields : PlaceRefusal → List (String × Json)
  | .outOfRange index => [("reason",.str "outOfRange"),("index",toJson index)]
  | .absent index => [("reason",.str "absent"),("index",toJson index)]
  | .repeated index paths => [("reason",.str "repeated"),("index",toJson index),("paths",toJson paths)]
  | .moved path => [("reason",.str "moved"),("path",toJson path)]

def editRefusalJson (sig : Signature NativeOp) (prog : Option NativeEff) : DocRefusal → Json
  | .foreign expected => Json.mkObj [("reason",.str "foreign"),("expectedDoc",docIdJson expected)]
  | .stale now => Json.mkObj [("reason",.str "stale"),("currentRevision",toJson now.revision),
      ("doc",docIdJson now.doc)]
  | .empty => Json.mkObj [("reason",.str "empty")]
  | .noEntry entry => Json.mkObj [("reason",.str "noEntry"),("entry",toJson entry)]
  | .place item why => Json.mkObj (("item",toJson item) :: placeRefusalFields why)
  | .feed item why => Json.mkObj (("item",toJson item) :: feedRefusalFields sig prog why)

def policyFrom? : Option String → Option FeedPolicy
  | none | some "keepExactType" => some .keepExact
  | some "recheckSource" => some .recheck
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

/-- A reply admission fault (`Kit.ReplyFault`) as JSON. -/
def replyFaultJson : Effect4.Run.Kit.ReplyFault → Json
  | .answerType expected =>
    Json.mkObj [("kind", .str "answerType"), ("expected", printJson expected)]
  | .errorType expected =>
    Json.mkObj [("kind", .str "errorType"), ("expected", printJson expected)]
  | .reservedDefect =>
    Json.mkObj [("kind", .str "reservedDefect")]

/-- A rejected tape entry (`Preview.Rejected`) as JSON. -/
def rejectedJson (r : Effect4.Run.Preview.Rejected) : Json :=
  Json.mkObj [("row", toJson r.row), ("exit", printJson r.exit), ("fault", replyFaultJson r.fault)]

/-- A preview profile refusal (`Preview.Refusal`) as JSON. -/
def previewRefusalJson : Effect4.Run.Preview.Refusal → Json
  | .admission why =>
    Json.mkObj [("reason", .str "admission"), ("refusal", printJson why)]
  | .outsideTree path =>
    Json.mkObj [("reason", .str "outsideTree"), ("path", toJson path)]
  | .genericRow path row =>
    Json.mkObj [("reason", .str "genericRow"), ("path", toJson path), ("row", toJson row)]
  | .handleAnswer path row =>
    Json.mkObj [("reason", .str "handleAnswer"), ("path", toJson path), ("row", toJson row)]

/-- A part signature tag (`PartSig`) as JSON. -/
def partSigJson : PartSig → Json
  | .root => Json.mkObj [("kind", .str "root")]
  | .block decls =>
    Json.mkObj [("kind", .str "block"), ("decls", printJson decls)]
  | .body decls params =>
    Json.mkObj [("kind", .str "body"), ("decls", printJson decls), ("params", printJson params)]

/-- Contextual signature data (`SigData`) as JSON. -/
def sigDataJson (d : SigData) : Json :=
  Json.mkObj [("app", .str (appName d.app)), ("rows", printJson d.app.rows),
    ("services", printJson d.app.services), ("types", printJson d.app.types),
    ("holes", printJson d.holes), ("part", partSigJson d.part)]

/-- Candidate contextual evidence (`CheckCache.Evidence`) as JSON. -/
def evidenceJson (sig : Signature NativeOp) (prog : Option NativeEff) :
    CheckCache.Evidence → Json
  | .exactFit ty =>
    Json.mkObj [("kind", .str "exactFit"), ("type", effTyJson ty)]
  | .typeMismatch expected actual =>
    Json.mkObj [("kind", .str "typeMismatch"), ("expected", effTyJson expected),
      ("actual", effTyJson actual)]
  | .refused why =>
    Json.mkObj [("kind", .str "refused"), ("refusal", refusalJson why prog sig)]
  | .feedRefused why => Json.mkObj [("kind",.str "feedRefused"),("refusal",Json.mkObj (feedRefusalFields sig none why))]
  | .differentEnv sourceEnv targetEnv =>
    Json.mkObj [("kind", .str "differentEnv"), ("sourceEnv", printJson sourceEnv),
      ("targetEnv", printJson targetEnv)]

/-- One candidate suggestion (`CheckCache.Suggestion`) as JSON. -/
def suggestionJson (sig : Signature NativeOp) (s : CheckCache.Suggestion)
    (hex : Bool := false) : Json :=
  Json.mkObj <|
    [("programJson", printJson s.program),
      ("sourcePath", match s.sourcePath with | some p => toJson p | none => .null),
      ("env", printJson (match s.key with | .part _ env _ => env | .module .. => [])),
      ("evidence", evidenceJson sig (some s.program) s.evidence)] ++
    if hex then [("program", .str (toHex s.program))] else []

/-- A bounded candidate search response (`CheckCache.SuggestResult`) as JSON. -/
def suggestResultJson (res : CheckCache.SuggestResult) (hex : Bool := false) : Json :=
  let sig := res.sig.signature
  Json.mkObj [("doc", docIdJson res.doc),
    ("revision", toJson res.revision),
    ("path", toJson res.path),
    ("bounds", Json.mkObj [("cursor", toJson res.cursor), ("limit", toJson res.limit),
      ("total", toJson res.total),
      ("nextCursor", match res.nextCursor with | some n => toJson n | none => .null)]),
    ("context", sigDataJson res.sig),
    ("env", printJson res.env),
    ("expected", effTyJson res.expected),
    ("suggestions", Json.arr (res.suggestions.map fun s => suggestionJson sig s hex).toArray)]

/-- A fill addition refusal (`AddRefusal`) as JSON. -/
def addRefusalJson : AddRefusal → Json
  | .root => Json.mkObj [("reason", .str "root")]
  | .unknownAddress => Json.mkObj [("reason", .str "unknownAddress")]
  | .notCertified => Json.mkObj [("reason", .str "notCertified")]
  | .conflict => Json.mkObj [("reason", .str "conflict")]
  | .overlap existing =>
    Json.mkObj [("reason", .str "overlap"), ("existing", toJson existing)]

/-- One fill addition outcome (`AddOutcome`) as JSON. -/
def addOutcomeJson : AddOutcome → Json
  | .applied path => Json.mkObj [("outcome", .str "applied"), ("path", toJson path)]
  | .collapsed path => Json.mkObj [("outcome", .str "collapsed"), ("path", toJson path)]
  | .refused path why =>
    Json.mkObj [("outcome", .str "refused"), ("path", toJson path), ("refusal", addRefusalJson why)]

/-- One `(path, program)` fill entry as JSON. -/
def fillEntryJson (entry : List Nat × NativeEff) (hex : Bool := false) : Json :=
  Json.mkObj <|
    [("path", toJson entry.1), ("programJson", printJson entry.2)] ++
    if hex then [("program", .str (toHex entry.2))] else []

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
  let checked := d.step (st.cache.oracle (Check.HitRule.exact.or Check.extension)) d.snap (.draft e)
  let learned := { st with cache := st.cache.learn checked }
  match checked.value with
  | .error why => (learned, {
      op := req.op, app := st.app, ok := false,
      result := editRefusalJson (d.session.app.withHoles d.session.sketch.holes).signature (some d.session.sketch.program) why,
      error := some "the draft is refused", id := req.id })
  | .ok (next,receipt) =>
    let step := receipt.steps.headD ⟨e,none,.unchanged⟩
    ({ (learned.withDoc next) with journal := step :: st.journal },
      { op := req.op, app := st.app, laws := readLaws ++ [``SourceSession.reached_view], ok := true,
        result := Json.mkObj [("doc",docIdJson next.id),("revision",toJson next.revision),
          ("delta",deltaJson step.delta),("view",viewJson next.session)], id := req.id })

def commitAnswer (st : State) (d : Doc) (req : Request) (change : Change)
    (readLaws : List Lean.Name := []) : State × Answer :=
  let noTarget : State × Answer := (st,refused req.op "a checked edit needs its snapshot and expected program" req.id)
  match policyFrom? req.policy, req.docName, req.docGeneration, req.revision with
  | none,_,_,_ => (st,refused req.op "unknown policy" req.id)
  | some _,none,_,_ | some _,_,none,_ | some _,_,_,none => noTarget
  | some policy,some name,some generation,some revision =>
    match valueFrom? (α := NativeEff) req.expected req.expectedJson with
    | none => noTarget
    | some (none,_) => (st,unreadable (α := NativeEff) req.op "the expected program does not read" req.expectedJson req.id)
    | some (some expected,expLaws) =>
      let snap : Snap := ⟨⟨name,generation⟩,revision⟩
      let checked := d.step (st.cache.oracle (Check.HitRule.exact.or Check.extension)) snap
        (.commit [(.at_ req.path expected,change)] policy)
      let learned := { st with cache := st.cache.learn checked }
      match checked.value with
      | .error why => (learned,{
          op := req.op, app := st.app, laws := readLaws ++ expLaws, ok := false,
          result := editRefusalJson (d.session.app.withHoles d.session.sketch.holes).signature (some d.session.sketch.program) why,
          error := some "the atomic edit is refused", id := req.id })
      | .ok (next,receipt) =>
        let step := receipt.steps.headD ⟨.fill req.path expected,some expected,.unchanged⟩
        ({ (learned.withDoc next) with journal := step :: st.journal },
          { op := req.op, app := st.app, laws := readLaws ++ expLaws ++ [``Doc.commit_sound], ok := true,
            result := Json.mkObj [("doc",docIdJson next.id),("revision",toJson next.revision),
              ("delta",deltaJson step.delta),("view",viewJson next.session)], id := req.id })

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
      let opened := Doc.open_ ⟨docId,app,{ program,holes }⟩
      let d := opened.value
      ({ document := some d, source := some d.session, journal := [], app := name,
          docId := d.id, revision := d.revision, generation := st.generation + 1,
          live := st.live, cache := st.cache.learn opened, fills := some (FillSet.open_ d) },
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
        match (Node.eff l.sketch.program).at_ req.path with
        | none => none' "no part of the sketch at the address"
        | some (.stmt _) | some (.stmts _) | some (.effs _) | some (.action _) | some (.layer _) | some (.layers _) => none' "no program at the address"
        | some (.eff expected) =>
          let entry := l.table.find? fun e => decide (e.path = req.path)
          let refusal := entry.bind fun e => e.result.bind Checker.refusal
          let result := Json.mkObj
            [("target", targetJson d.snap req.path expected req.hex),
              ("context", sigDataJson (sketchSigData l.sketch l.app req.path)),
              ("focus", focusJson (l.focusAt req.path) req.hex),
              ("entry", match entry with
                | some e => entryJson e (some l.sketch.program) sig
                | none => .null),
              ("refusal", match refusal with
                | some r => refusalJson r (some l.sketch.program) sig
                | none => .null)]
          (st, Answer.mk op st.app
            [``SourceSession.reached_view, ``SourceSession.focusAt_typed, ``sketchSigData_signature]
            true result none req.id)
      | "suggest" =>
        let (supplied?, supLaws) := listFrom? (α := NativeEff) req.candidates req.candidatesJson
        match supplied? with
        | none =>
          (st, unreadable (α := List NativeEff) req.op "the candidate programs do not read"
            req.candidatesJson req.id)
        | some supplied =>
          let checked := CheckCache.suggest (st.cache.oracle (Check.HitRule.exact.or Check.extension))
            d req.path req.limit req.cursor supplied
          let learned := st.cache.learn checked
          match checked.value with
          | none => none' "no typed focus at the address"
          | some res =>
            let st' := { st with cache := learned }
            (st', Answer.mk op st.app
              (supLaws ++ [``sketchSigData_signature, ``Check.Oracle.eq_uncached]).eraseDups
              true (suggestResultJson res req.hex) none req.id)
      | "fills.add" =>
        let fs0 := st.fillsFor d
        if fillsStale fs0 d then
          none' s!"the fill set was opened at revision {fs0.anchor.revision} of {fs0.anchor.doc.name}; the document is at revision {d.revision} of {d.id.name}; `fills.reset` discards the set"
        else
        let items? : Option (Option (List (List Nat × NativeEff)) × List Lean.Name) :=
          if req.fills.isSome || req.fillsJson.isSome then
            let (batch?, laws) := listFrom? (α := List Nat × NativeEff) req.fills req.fillsJson
            some (batch?, laws)
          else
            match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
            | some (some q, laws) => some (some [(req.path, q)], laws)
            | some (none, laws) => some (none, laws)
            | none => none
        match items? with
        | none => none' "no fills supplied"
        | some (none, _) =>
          if req.fills.isSome || req.fillsJson.isSome then
            (st, unreadable (α := List (List Nat × NativeEff)) req.op "the fills do not read"
              req.fillsJson req.id)
          else
            (st, unreadable (α := NativeEff) req.op "the filling does not read"
              req.replacementJson req.id)
        | some (some items, readLaws) =>
          let checked := fs0.add (st.cache.oracle (Check.HitRule.exact.or Check.extension)) items
          let (fs',outs) := checked.value
          let allOk := outs.all fun o => match o with | .refused _ _ => false | _ => true
          let st' := { st with fills := some fs', cache := st.cache.learn checked }
          let result := Json.mkObj
            [("doc", docIdJson fs'.anchor.doc),
              ("revision", toJson fs'.anchor.revision),
              ("outcomes", Json.arr (outs.map addOutcomeJson).toArray),
              ("fills", Json.arr (fs'.pending.map fun e => fillEntryJson e req.hex).toArray)]
          (st',
            { op := op, app := st.app,
              laws := (readLaws ++ [``FillSet.add_wf]).eraseDups,
              ok := allOk,
              result := result,
              error := if allOk then none else some "one or more fills were refused",
              id := req.id })
      | "fills.view" =>
        let fs := st.fillsFor d
        let result := Json.mkObj
          [("doc", docIdJson fs.anchor.doc),
            ("revision", toJson fs.anchor.revision),
            ("stale", toJson (fillsStale fs d)),
            ("fills", Json.arr (fs.pending.map fun e => fillEntryJson e req.hex).toArray)]
        (st, Answer.mk op st.app [``ordered_congr] true result none req.id)
      | "fills.reset" =>
        let fs := st.fillsFor d
        let fresh := FillSet.open_ d
        let result := Json.mkObj
          [("doc", docIdJson fresh.anchor.doc),
            ("revision", toJson fresh.anchor.revision),
            ("discarded", Json.arr (fs.pending.map fun e => fillEntryJson e req.hex).toArray)]
        ({ st with fills := some fresh }, Answer.mk op st.app [] true result none req.id)
      | "fills.materialize" =>
        let fs := st.fillsFor d
        match d.check fs.anchor with
        | .error why => (st, {
            op := op, app := st.app, ok := false,
            result := editRefusalJson sig (some l.sketch.program) why,
            error := some "the fill anchor is stale", id := req.id })
        | .ok () =>
          if fs.base != d.session.sketch || fs.app != d.session.app then
            none' "the fill anchor holds another base or application"
          else
            match fs.publication with
            | .error .empty => none' "the fill set holds no fill"
            | .ok action =>
              let checked := d.step (st.cache.oracle (Check.HitRule.exact.or Check.extension)) fs.anchor action
              let learned := { st with cache := st.cache.learn checked }
              match checked.value with
              | .error why => (learned, {
                  op := op, app := st.app, ok := false,
                  result := editRefusalJson sig (some l.sketch.program) why,
                  error := some "the publication is refused", id := req.id })
              | .ok (next,receipt) =>
                let updated := { (learned.withDoc next) with
                  journal := receipt.steps.reverse ++ st.journal,
                  fills := some (FillSet.open_ next) }
                (updated,Answer.mk op st.app [``FillSet.add_wf,``SourceSession.reached_view] true
                  (Json.mkObj [("doc",docIdJson next.id),("revision",toJson next.revision),
                    ("view",viewJson next.session)]) none req.id)
      | "replace" | "commit" | "fill" =>
        match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
        | some (some q, readLaws) => commitAnswer st d req (.fill q) readLaws
        | none => none' "a checked replacement needs its program (`replacement` or `replacementJson`); `omit` declares a hole"
        | some (none, _) =>
          (st, unreadable (α := NativeEff) req.op "the filling does not read" req.replacementJson req.id)
      | "omit" => commitAnswer st d req (.omitHole req.holeName) []
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
        let opened := Doc.open_ ⟨newId,d.session.app,d.session.sketch⟩
        let d' := opened.value
        let st' := { (st.withDoc d') with generation := st.generation + 1, cache := st.cache.learn opened, fills := some (FillSet.open_ d') }
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
        if d.history.isEmpty then none' "the history is empty"
        else
          let checked := d.step (st.cache.oracle (Check.HitRule.exact.or Check.extension)) d.snap
            (.revert (d.history.length - 1))
          let learned := { st with cache := st.cache.learn checked }
          match checked.value with
          | .error why => (learned, {
              op := op, app := st.app, ok := false,
              result := editRefusalJson sig (some l.sketch.program) why,
              error := some "the revert is refused", id := req.id })
          | .ok (next,receipt) =>
            ({ (learned.withDoc next) with journal := receipt.steps.reverse ++ st.journal },
              Answer.mk op st.app [``Doc.revert_program] true
                (Json.mkObj [("doc",docIdJson next.id),("revision",toJson next.revision),
                  ("view",viewJson next.session)]) none req.id)
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
        let program := l.sketch.program
        match Effect4.Run.Preview.admit app program with
        | .error why =>
          (st,
            { op := op, app := st.app, laws := [``Effect4.Run.Preview.checkedTape_admits],
              ok := false, result := previewRefusalJson why,
              error := some "preview refused by profile", id := req.id })
        | .ok _ =>
          let tape? : Option (List Effect4.Machine.ExitV) := match req.tapeJson with
            | some j => Tools.JsonBridge.read? j
            | none => some []
          match tape? with
          | none =>
            (st, unreadable (α := List Effect4.Machine.ExitV) req.op "the tape does not read" req.tapeJson req.id)
          | some tape =>
            let host := Effect4.Run.Preview.checkedTape app
            match op with
            | "settle" =>
              let result := match Effect4.Run.Tree.settle app.rows req.limit host tape program with
                | some (k, o) =>
                  treeRunJson o.stop o.steps [("budget", toJson k),
                    ("rejected", match Effect4.Run.Preview.rejected app o with
                      | some r => rejectedJson r
                      | none => .null)]
                | none => Json.mkObj [("status", .str "unsettled"), ("limit", toJson req.limit),
                    ("note", .str "cut at every budget up to the limit: a finite probe, not a divergence")]
              (st, Answer.mk op st.app
                [``Effect4.Run.Preview.checkedTape_admits,
                  ``Effect4.Run.Preview.checkedTape_success_externalValue,
                  ``Effect4.Run.Tree.settle_sound, ``Effect4.Run.Tree.probe_stable]
                true result none req.id)
            | "frames" =>
              let frames := Effect4.Run.Tree.frames app.rows req.limit host tape program
              let result := Json.arr (frames.map fun o =>
                treeRunJson o.stop o.steps
                  [("rejected", match Effect4.Run.Preview.rejected app o with
                    | some r => rejectedJson r
                    | none => .null)]).toArray
              (st, Answer.mk op st.app
                [``Effect4.Run.Preview.checkedTape_admits,
                  ``Effect4.Run.Preview.checkedTape_success_externalValue,
                  ``Effect4.Run.Tree.ofProgram_approx]
                true result none req.id)
            | _ =>
              let paths := Effect4.Run.Kit.explore app req.budget req.width program
              let result := Json.arr (paths.map fun p =>
                let tape := p.steps.filterMap fun
                  | .called _ _ answer => some answer
                  | .celled _ _ => none
                treeRunJson p.stop p.steps [("tape", printJson tape)]).toArray
              (st, Answer.mk op st.app
                [``Effect4.Run.Preview.checkedTape_admits, ``Effect4.Run.Tree.ofProgram_approx]
                true result none req.id)
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
