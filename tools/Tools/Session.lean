import Tools.Query
import Effect4.Program.Edit
import Effect4.Laws.Program.Edit
import Effect4.Laws.Program.SketchWire

/-!
# Tools.Session — the edit session as a tool: one request a line, one session held between lines

The query tool (`Tools.Query`) answers one request about a program and keeps nothing. This tool
keeps an edit session (`EditSession`, `src/Effect4/Program/Edit.lean`) between its lines, with
the journal of its edits. A request is one JSON object; the answer is one JSON object, in the
query tool's shape (`Tools.Query.Answer`). Programs, fillings and hole tables travel as their
canonical bytes in lowercase hex, as in the query tool (`Wire.encodeProgram`,
`Wire.encodeHoles`).

| Operation | Takes | Answers | The laws it names |
| --- | --- | --- | --- |
| `open` | `program`, and `holes` if any | the view | `EditSession.reached_view` |
| `fill` | `path`, `replacement` | the delta and the view | the splice law the delta took, and `EditSession.reached_view` |
| `omit` | `path`, `holeName` | the delta and the view; the hole row declares the focus's type | the same |
| `view` | `path`, or none | at an address, its entry; with none, the whole table | `EditSession.reached_view`; `Table.typedAt_table` at an address |
| `undo` | nothing | the last fill taken back: the delta and the view | `EditSession.feed_undo` |
| `journal` | nothing | each edit, its address and its delta | none |
| `sketch` | nothing | the sketch's bytes: its program's and its hole table's | `Sketch.decode_exact` |

**The delta names its law.** A fill that splices names `Sketch.table_fill` and
`EditSession.feed_repaint`; an omission that splices names `Sketch.table_omit`; an edit that
checks again names `Sketch.annotate_eq_table`. Each view names `EditSession.reached_view`: what it
shows is the checker's answer on the sketch.

**An undo of an omission** puts the program back, and keeps the hole row it declared: the law of
undo is stated for a fill.

**What it is not.** It is no MCP server: an MCP tool is a thin wrapper over `answerLine`. It
holds one session. The application is the empty one, as in the query tool.
-/

namespace Tools.Session

open Lean (Json ToJson toJson)
open Effect4.Program Effect4.Program.Wire Effect4.Store
open Tools.Query (Answer refused effTyJson refusalJson entryJson focusJson holeRow optField)

/-- **The tool's state**: the session, once opened, and its journal, the latest step first. -/
structure State where
  session : Option EditSession := none
  journal : List Edit.Step := []

/-- One request. -/
structure Request where
  op : String
  program : Option String := none
  holes : Option String := none
  path : List Nat := []
  replacement : Option String := none
  holeName : String := "h0"
  id : Option Json := none

/-- Read a request; a field of the wrong type is refused with its name. -/
def Request.fromJson? (j : Json) : Except String Request := do
  let op ← j.getObjValAs? String "op"
  let program ← optField j "program" (Lean.fromJson? (α := String))
  let holes ← optField j "holes" (Lean.fromJson? (α := String))
  let path ← optField j "path" (Lean.fromJson? (α := List Nat))
  let replacement ← optField j "replacement" (Lean.fromJson? (α := String))
  let holeName ← optField j "holeName" (Lean.fromJson? (α := String))
  let id := (j.getObjVal? "id").toOption
  return Request.mk op program holes (path.getD []) replacement (holeName.getD "h0") id

/-- Write a request, as `Request.fromJson?` reads it. -/
def Request.toJson (r : Request) : Json :=
  Json.mkObj <|
    [("op", .str r.op), ("path", Lean.toJson r.path), ("holeName", .str r.holeName)] ++
    (r.program.map fun hex => ("program", Json.str hex)).toList ++
    (r.holes.map fun hex => ("holes", Json.str hex)).toList ++
    (r.replacement.map fun hex => ("replacement", Json.str hex)).toList ++
    (r.id.map fun id => ("id", id)).toList

/-- A program from its hex bytes. -/
def programOfHex (hex : String) : Option NativeEff := (bytesOfHex hex.toList).bind decodeProgram

/-- A hole table from its hex bytes. -/
def holesOfHex (hex : String) : Option RowTable := (bytesOfHex hex.toList).bind decodeHoles

/-- What a delta says. -/
def deltaJson : Edit.Delta → Json
  | .unchanged => Json.mkObj [("kind", .str "unchanged")]
  | .spliced shown => Json.mkObj [("kind", .str "spliced"), ("shown", toJson shown)]
  | .rechecked => Json.mkObj [("kind", .str "rechecked")]

/-- The laws behind a delta, by the edit that made it. -/
def deltaLaws : Edit → Edit.Delta → List Lean.Name
  | .fill _ _, .spliced _ => [``Sketch.table_fill, ``EditSession.feed_repaint]
  | .omitAt _ _, .spliced _ => [``Sketch.table_omit]
  | _, .rechecked => [``Sketch.annotate_eq_table]
  | _, .unchanged => []

/-- The session's view, in short: its type and its refusals, and how many entries it has. -/
def viewJson (l : EditSession) : Json :=
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
def feedAnswer (st : State) (l : EditSession) (req : Request) (e : Edit) : State × Answer :=
  let (l', step) := l.feedStep e
  ({ session := some l', journal := step :: st.journal },
    { op := req.op, laws := deltaLaws e step.delta ++ [``EditSession.reached_view], ok := true,
      result := Json.mkObj [("delta", deltaJson step.delta), ("view", viewJson l')],
      id := req.id })

/-- **Answer one request**, from the state before it, with the state after it. -/
def answer (st : State) (req : Request) : State × Answer :=
  let none' (why : String) : State × Answer := (st, refused req.op why req.id)
  match req.op with
  | "open" =>
    match req.program.bind programOfHex, (req.holes.map holesOfHex).getD (some []) with
    | none, _ => none' "the program's bytes do not decode"
    | _, none => none' "the hole table's bytes do not decode"
    | some program, some holes =>
      let l := EditSession.open {} { program, holes }
      ({ session := some l, journal := [] },
        { op := req.op, laws := [``EditSession.reached_view], ok := true, result := viewJson l,
          id := req.id })
  | op =>
    match st.session with
    | none => none' "no session is open"
    | some l =>
      match op with
      | "fill" =>
        match req.replacement.bind programOfHex with
        | none => none' "the filling's bytes do not decode"
        | some q => feedAnswer st l req (.fill req.path q)
      | "omit" =>
        match l.sketch.focusAt l.app req.path with
        | none => none' "no focus at the address"
        | some f => feedAnswer st l req (.omitAt req.path (holeRow req.holeName f))
      | "view" =>
        if req.path.isEmpty then
          let result := Json.mkObj [("view", viewJson l),
            ("table", Json.arr (l.table.map entryJson).toArray)]
          (st, Answer.mk op "empty" [``EditSession.reached_view] true result none req.id)
        else
          let entry := match l.table.find? fun e => decide (e.path = req.path) with
            | some e => entryJson e
            | none => .null
          let result := Json.mkObj [("entry", entry),
            ("focus", focusJson (l.sketch.focusAt l.app req.path))]
          (st, Answer.mk op "empty" [``EditSession.reached_view, ``Table.typedAt_table] true
            result none req.id)
      | "undo" =>
        match st.journal with
        | step :: rest =>
          match step.replaced with
          | some old =>
            let (l', back) := l.feedStep (.fill step.edit.path old)
            ({ session := some l', journal := rest },
              { op := op, laws := [``EditSession.feed_undo, ``EditSession.reached_view], ok := true,
                result := Json.mkObj [("delta", deltaJson back.delta), ("view", viewJson l')],
                id := req.id })
          | none => none' "the last edit replaced no program"
        | [] => none' "the journal is empty"
      | "journal" =>
        let result := Json.arr (st.journal.reverse.map stepJson).toArray
        (st, Answer.mk op "empty" [] true result none req.id)
      | "sketch" =>
        let result := Json.mkObj [("program", .str (hexString (encodeProgram l.sketch.program))),
          ("holes", .str (hexString (encodeHoles l.sketch.holes)))]
        (st, Answer.mk op "empty" [``Sketch.decode_exact] true result none req.id)
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

/-- The answers to a list of lines, from a fresh state. -/
def answerLines (lines : List String) : List String :=
  (lines.foldl (fun (st, out) line =>
    let (st', a) := answerLine st line
    (st', a :: out)) (({} : State), [])).2.reverse

/-- **A transcript replays**: the answers to the recorded requests, in order from a fresh state,
are the recorded answers. -/
def replays (requests answers : String) : Bool :=
  answerLines (Tools.Query.fixtureLines requests) == Tools.Query.fixtureLines answers

end Tools.Session
