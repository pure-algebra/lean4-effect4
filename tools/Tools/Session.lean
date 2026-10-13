import Tools.Query
import Tools.JsonBridge
import Tools.Catalogue
import Effect4.Laws.Store.ShapeRead
import Effect4.Program.Typing.SourceSession
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.SketchWire

/-!
# Tools.Session — the edit session as a tool: one request a line, one session held between lines

The query tool (`Tools.Query`) answers one request about a program and keeps nothing. This tool
keeps an edit session of a sketch as written (`SourceSession`,
`src/Effect4/Program/Typing/SourceSession.lean`) between its lines, with the journal of its
edits. The session checks the sketch through its layer references, as program admission checks a
program, and shows the expansion's table at the source's addresses (decisions row 373 (7)).

A request is one JSON object; the answer is one JSON object, in the query tool's shape
(`Tools.Query.Answer`). Programs, fillings and hole tables travel as their canonical bytes in
lowercase hex, as in the query tool (`Wire.encodeProgram`, `Wire.encodeHoles`), or as their JSON
print, whose objects may come in any order and whose lists may come as arrays
(`Canonical.ofJsonAnyOrder`, `src/Effect4/Store/Domain/ShapeRead.lean`). Answers give a program
as both.

**The application travels with `open`** (decisions row 373 (10)): the row table and the
service declarations, each as its canonical bytes in hex (`rows`, `services`), read by the
store's exact decoder (`Canonical.decode`). With neither, the application is the empty one. An
answer names the application: `empty`, or `sha256:` and the digest of the canonical bytes of the
pair. A digest names bytes; no answer assumes two applications with one digest are one.

| Operation | Takes | Answers | The laws it names |
| --- | --- | --- | --- |
| `open` | `program` (hex) or `programJson`, and `holes`, `rows`, `services` if any | the view | `SourceSession.reached_view`; `ofLeanJson_num` and `Canonical.ofJsonAnyOrder_exact` for JSON |
| `fill` | `path`, `replacement` (hex) or `replacementJson` | the delta and the view | the law the delta took, `SourceSession.feed_coherent`, and `SourceSession.reached_view` |
| `omit` | `path`, `holeName` | the delta and the view; the hole row declares the focus's type | the same |
| `view` | `path`, or none | at an address, its entry and its focus; with none, the whole table | `SourceSession.reached_view`; `SourceSession.focusAt_typed` at an address |
| `undo` | nothing | the last fill taken back: the delta and the view | `SourceSession.feed_undo` |
| `journal` | nothing | each edit, its address and its delta | none |
| `sketch` | nothing | the bytes of the sketch and of the application | `Sketch.decode_exact`, `Canonical.decode_exact` |
| `catalogue` | nothing; open or not | the program's forms, the atoms with their typing schemes, the application's rows by index (`Tools.Catalogue`) | `Canonical.ofJsonAnyOrder_exact`, `NativeAtom.atom_table_wf` |

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
holds one session. It does not admit the application's signature (`admitSig`): it shows the
checker's answers at that signature (the open part `sketch-admission` of R14). It runs nothing.
-/

namespace Tools.Session

open Lean (Json ToJson toJson)
open Effect4 (ServiceKey)
open Effect4.Program Effect4.Program.Wire Effect4.Store
open Tools.Query (Answer refused effTyJson refusalJson entryJson focusJson holeRow optField)
open Tools.JsonBridge (printJson)

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
  return Request.mk op program holes (path.getD []) replacement (holeName.getD "h0") id
    programJson replacementJson rows services

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
    (r.id.map fun id => ("id", id)).toList

/-- A program from its hex bytes. -/
def programOfHex (hex : String) : Option NativeEff := (bytesOfHex hex.toList).bind decodeProgram

/-- A program from its JSON print, its objects in any order and its lists as arrays or as their
cases (`Canonical.ofJsonAnyOrder`). -/
def programOfJson (j : Json) : Option NativeEff :=
  (Tools.JsonBridge.ofLeanJson 4096 j).bind Canonical.ofJsonAnyOrder

/-- A program from its hex bytes or, where there are none, its JSON print; with the laws its
reading names. -/
def programFrom? (hex : Option String) (json : Option Json) : Option NativeEff × List Lean.Name :=
  match hex, json with
  | some h, _ => (programOfHex h, [])
  | none, some j =>
    (programOfJson j, [``Tools.JsonBridge.ofLeanJson_num, ``Canonical.ofJsonAnyOrder_exact])
  | none, none => (none, [])

/-- A hole table from its hex bytes. -/
def holesOfHex (hex : String) : Option RowTable := (bytesOfHex hex.toList).bind decodeHoles

/-- An application's row table from its hex bytes: the store's exact decoder at `RowTable`. -/
def rowsOfHex (hex : String) : Option RowTable :=
  (bytesOfHex hex.toList).bind (Canonical.decode (α := RowTable))

/-- An application's service declarations from their hex bytes: the store's exact decoder. -/
def servicesOfHex (hex : String) : Option (List (ServiceKey × Ty)) :=
  (bytesOfHex hex.toList).bind (Canonical.decode (α := List (ServiceKey × Ty)))

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
  Json.mkObj [("type", match v.type with
      | some t => effTyJson t
      | none => .null),
    ("refusals", Json.arr (v.refusals.map refusalJson).toArray),
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
    let (program?, readLaws) := programFrom? req.program req.programJson
    match program?, (req.holes.map holesOfHex).getD (some []),
        (req.rows.map rowsOfHex).getD (some []), (req.services.map servicesOfHex).getD (some []) with
    | none, _, _, _ => none' "the program does not read"
    | _, none, _, _ => none' "the hole table's bytes do not decode"
    | _, _, none, _ => none' "the row table's bytes do not decode"
    | _, _, _, none => none' "the service declarations' bytes do not decode"
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
      match op with
      | "fill" =>
        match programFrom? req.replacement req.replacementJson with
        | (none, _) => none' "the filling does not read"
        | (some q, readLaws) => feedAnswer st l req (.fill req.path q) readLaws
      | "omit" =>
        match l.focusAt req.path with
        | none => none' "no focus at the address"
        | some f => feedAnswer st l req (.omitAt req.path (holeRow req.holeName f))
      | "view" =>
        if req.path.isEmpty then
          let result := Json.mkObj [("view", viewJson l),
            ("table", Json.arr (l.table.map entryJson).toArray)]
          (st, Answer.mk op st.app [``SourceSession.reached_view] true result none req.id)
        else
          let entry := match l.table.find? fun e => decide (e.path = req.path) with
            | some e => entryJson e
            | none => .null
          let focus := l.focusAt req.path
          let result := Json.mkObj [("entry", entry), ("focus", focusJson focus),
            ("programJson", match focus with
              | some f => printJson f.program
              | none => .null)]
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
        let result := Json.mkObj [("program", .str (hexString (encodeProgram l.sketch.program))),
          ("holes", .str (hexString (encodeHoles l.sketch.holes))),
          ("rows", .str (hexString (Canonical.encode l.app.rows))),
          ("services", .str (hexString (Canonical.encode l.app.services))),
          ("programJson", printJson l.sketch.program), ("holesJson", printJson l.sketch.holes)]
        (st, Answer.mk op st.app [``Sketch.decode_exact, ``Canonical.decode_exact] true result
          none req.id)
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
