import Tools.Query
import Tools.JsonBridge
import Tools.Catalogue
import Effect4.Laws.Store.ShapeRead
import Effect4.Program.Typing.SourceSession
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.SketchWire
import Effect4.Api.RunnerDerived
import Effect4.Run.Live
import Effect4.Laws.Api.Live

/-!
# Tools.Session — the edit session as a tool: one request a line, one session held between lines

The query tool (`Tools.Query`) answers one request about a program and keeps nothing. This tool
keeps an edit session of a sketch as written (`SourceSession`,
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

**The application travels with `open`** (decisions row 373 (10)): the row table and the
service declarations (`rows` or `rowsJson`, `services` or `servicesJson`). With neither, the
application is the empty one. The catalogue gives a row's JSON form. An answer names the
application: `empty`, or `sha256:` and the digest of the canonical bytes of the pair. A digest
names bytes; no answer assumes two applications with one digest are one.

| Operation | Takes | Answers | The laws it names |
| --- | --- | --- | --- |
| `open` | `program` (hex) or `programJson`, and the hole table, the rows and the services if any, each as hex or JSON | the view | `SourceSession.reached_view`; `ofLeanJson_num` and `Canonical.ofJsonAnyOrder_exact` for JSON |
| `fill` | `path`, `replacement` (hex) or `replacementJson` | the delta and the view; refused where the path is no part of the sketch | the law the delta took, `SourceSession.feed_coherent`, and `SourceSession.reached_view` |
| `omit` | `path`, `holeName` | the delta and the view; the hole row declares the focus's type | the same |
| `view` | `path`, or none | at an address, its entry and its focus; with none, the whole table | `SourceSession.reached_view`; `SourceSession.focusAt_typed` at an address |
| `undo` | nothing | the last fill taken back: the delta and the view | `SourceSession.feed_undo` |
| `journal` | nothing | each edit, its address and its delta | none |
| `sketch` | nothing | the sketch and the application as JSON, and as bytes with `hex` | `Sketch.decode_exact`, `Canonical.decode_exact` |
| `catalogue` | nothing; open or not | the program's forms, the atoms with their typing schemes, the application's rows by index (`Tools.Catalogue`) | `Canonical.ofJsonAnyOrder_exact`, `NativeAtom.atom_table_wf` |
| `run` | `answers` (hex) or `answersJson`, a script of `(row, answer)` pairs, if any | the outcome, the exit (`ExitV`) and any waiting calls through `Live.feedAll`; `syncExit` (`Api.Built.runSync`) when closed | `Live.reached` |

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
admits the sketch at its rows (`admitProgram`).
-/

namespace Tools.Session

open Lean (Json ToJson toJson)
open Effect4 (ServiceKey)
open Effect4.Program Effect4.Program.Wire Effect4.Store
open Tools.Query (Answer refused effTyJson refusalJson entryJson focusJson holeRow optField)
open Tools.JsonBridge (printJson valueFrom? toHex locate)

/-- **The tool's state**: the session, once opened, its journal, the latest step first, and the
name of its application. -/
structure State where
  /-- the edit session of the sketch as written, once opened -/
  source : Option SourceSession := none
  /-- the journal, the latest step first -/
  journal : List Edit.Step := []
  /-- the application's name: `empty`, or the digest of its canonical bytes -/
  app : String := "empty"

/-- **What the session shows, as an edit session**: the application, the sketch as written and
the table at the source's addresses (`SourceSession.shown`). The view tools draw it. -/
def State.session (st : State) : Option EditSession := st.source.map SourceSession.shown

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
  let hex ← optField j "hex" (Lean.fromJson? (α := Bool))
  let answers ← optField j "answers" (Lean.fromJson? (α := String))
  return Request.mk op program holes (path.getD []) replacement (holeName.getD "h0") id
    programJson replacementJson rows services (j.getObjVal? "holesJson").toOption
    (j.getObjVal? "rowsJson").toOption (j.getObjVal? "servicesJson").toOption (hex.getD false)
    answers (j.getObjVal? "answersJson").toOption

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
    (r.holesJson.map fun j => ("holesJson", j)).toList ++
    (r.rowsJson.map fun j => ("rowsJson", j)).toList ++
    (r.servicesJson.map fun j => ("servicesJson", j)).toList ++
    (r.answers.map fun hex => ("answers", Json.str hex)).toList ++
    (r.answersJson.map fun j => ("answersJson", j)).toList ++
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
  if app.rows.isEmpty && app.services.isEmpty then "empty"
  else "sha256:" ++ (sha256 (Canonical.encode (app.rows, app.services))).hex

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

/-- Feed one edit, record it, and answer its delta and the view. -/
def feedAnswer (st : State) (l : SourceSession) (req : Request) (e : Edit)
    (readLaws : List Lean.Name := []) : State × Answer :=
  let (l', step) := l.feedStep e
  ({ st with source := some l', journal := step :: st.journal },
    { op := req.op, app := st.app,
      laws := readLaws ++ deltaLaws e step.delta ++ [``SourceSession.reached_view],
      ok := true,
      result := Json.mkObj [("delta", deltaJson step.delta), ("view", viewJson l')],
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
    let readLaws := (programLaws ++ holeLaws ++ rowLaws ++ serviceLaws).eraseDups
    match program?, holes?, rows?, services? with
    | none, _, _, _ => (st, unreadable (α := NativeEff) req.op "the program does not read" req.programJson req.id)
    | _, none, _, _ => (st, unreadable (α := RowTable) req.op "the hole table does not read" req.holesJson req.id)
    | _, _, none, _ => (st, unreadable (α := RowTable) req.op "the row table does not read" req.rowsJson req.id)
    | _, _, _, none =>
      (st, unreadable (α := List (ServiceKey × Ty)) req.op "the service declarations do not read"
        req.servicesJson req.id)
    | some program, some holes, some rows, some services =>
      let app : SigApp := ⟨rows, services⟩
      let name := appName app
      let l := SourceSession.open app { program, holes }
      ({ source := some l, journal := [], app := name },
        Answer.mk req.op name (readLaws ++ [``SourceSession.reached_view]) true (viewJson l) none
          req.id)
  | "catalogue" =>
    let rows := (st.source.map (·.app.rows)).getD []
    (st, Answer.mk req.op st.app [``Canonical.ofJsonAnyOrder_exact, ``NativeAtom.atom_table_wf] true
      (Tools.Catalogue.catalogueJson rows) none req.id)
  | op =>
    match st.source with
    | none => none' "no session is open"
    | some l =>
      let sig := (l.app.withHoles l.sketch.holes).signature
      match op with
      | "fill" =>
        match valueFrom? (α := NativeEff) req.replacement req.replacementJson with
        | some (some q, readLaws) =>
          if (l.sketch.fillAt req.path q).isSome then feedAnswer st l req (.fill req.path q) readLaws
          else none' "no part of the sketch at the address"
        | _ =>
          (st, unreadable (α := NativeEff) req.op "the filling does not read" req.replacementJson req.id)
      | "omit" =>
        match l.focusAt req.path with
        | none => none' "no focus at the address"
        | some f => feedAnswer st l req (.omitAt req.path (holeRow req.holeName f))
      | "view" =>
        if req.path.isEmpty then
          let result := Json.mkObj [("view", viewJson l),
            ("table",
              Json.arr (l.table.map fun e => entryJson e (some l.sketch.program) sig).toArray)]
          (st, Answer.mk op st.app [``SourceSession.reached_view] true result none req.id)
        else
          let entry := match l.table.find? fun e => decide (e.path = req.path) with
            | some e => entryJson e (some l.sketch.program) sig
            | none => .null
          let result := Json.mkObj [("entry", entry), ("focus", focusJson (l.focusAt req.path) req.hex)]
          (st, Answer.mk op st.app [``SourceSession.reached_view, ``SourceSession.focusAt_typed]
            true result none req.id)
      | "undo" =>
        match st.journal with
        | step :: rest =>
          match step.replaced with
          | some old =>
            let (l', back) := l.feedStep (.fill step.edit.path old)
            ({ st with source := some l', journal := rest },
              { op := op, app := st.app,
                laws := [``SourceSession.feed_undo, ``SourceSession.reached_view], ok := true,
                result := Json.mkObj [("delta", deltaJson back.delta), ("view", viewJson l')],
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
              ("rows", .str (toHex l.app.rows)), ("services", .str (toHex l.app.services))]
          else []) ++
          [("programJson", printJson l.sketch.program), ("holesJson", printJson l.sketch.holes),
            ("rowsJson", printJson l.app.rows), ("servicesJson", printJson l.app.services)]
        (st, Answer.mk op st.app [``Sketch.decode_exact, ``Canonical.decode_exact] true result
          none req.id)
      | "run" =>
        let (answers?, answerLaws) :=
          listFrom? (α := String × Effect4.Api.HostSession.Answer) req.answers req.answersJson
        match answers? with
        | none =>
          (st, unreadable (α := List (String × Effect4.Api.HostSession.Answer)) req.op
            "the host answers do not read" req.answersJson req.id)
        | some answers =>
          let rows := (l.app.withHoles l.sketch.holes).rows
          match Effect4.Program.admitProgram l.sketch.program ⟨rows, []⟩ with
          | .error why =>
            let result := Json.mkObj [("status", .str "refused"), ("refusal", printJson why)]
            (st, Answer.mk op st.app answerLaws true result none req.id)
          | .ok admitted =>
            let b : Effect4.Api.Built := { table := rows, program := l.sketch.program, admitted }
            let events : List Effect4.Run.Event :=
              [.start] ++
              answers.flatMap (fun (row, ans) => [.receive (.row row) ans, .apply (.row row)]) ++
              [.flush]
            let run := ((Effect4.Live.open b st.app).feedAll events).run
            let waiting := (Effect4.Run.live run).map fun c =>
              Json.mkObj [("row", .str c.row), ("request", printJson c.request)]
            let result := Json.mkObj <|
              [("status", .str "ok"), ("outcome", printJson run.inspect.outcome),
                ("exit", match run.exit with
                  | some exit => printJson exit
                  | none => .null),
                ("waiting", Json.arr waiting.toArray)] ++
              (if answers.isEmpty && rows.isEmpty then [("syncExit", printJson b.runSync)] else [])
            (st, Answer.mk op st.app (answerLaws ++ [``Effect4.Live.reached]) true result none
              req.id)
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
