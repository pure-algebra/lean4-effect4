import Tools.Session.Snapshot
import Tools.Session
import Tools.View.Flow
import Tools.View.Output

/-! Experimental MCP 2026-07-28 preview adapter.
Every request carries a canonical program and hole table.
The process caches only its last explicitly supplied snapshot.
It publishes no root and runs no application code.
The input schemas derive from the existing Shape alphabet.
This bounded prototype is not the proposed stable MCP server.
-/

namespace LiveGraphPreview
open Lean (Json toJson)
open Effect4.Program Effect4.Store Tools.Session

inductive Op where
  | inspect | fill | omit | render
  deriving DecidableEq

def Op.all : List Op := [.inspect, .fill, .omit, .render]
def Op.name : Op → String
  | .inspect => "effect4.inspect"
  | .fill => "effect4.fillPreview"
  | .omit => "effect4.omitPreview"
  | .render => "effect4.renderPreview"
def Op.description : Op → String
  | .inspect => "Inspect the checked view at an explicit canonical snapshot."
  | .fill => "Preview a replacement at a snapshot. Returns new bytes; publishes nothing."
  | .omit => "Preview a typed hole at a snapshot. Returns new bytes; publishes nothing."
  | .render => "Render an explicit snapshot as SVG with its checked lines and structural flow."
def Op.fields (op : Op) : List (String × Shape) :=
  [("program", .bytes), ("holes", .bytes), ("path", .list .nat)] ++
    match op with
    | .fill => [("replacement", .bytes)]
    | .omit => [("holeName", .string)]
    | _ => []

/-- The finite shape profile used by this prototype. Unsupported shapes refuse generation. -/
def fieldSchema : Shape → Option Json
  | .bytes => some (Json.mkObj [("type", .str "string"),
      ("pattern", .str "^([0-9a-f]{2})*$"),
      ("not", Json.mkObj [("pattern", .str "[^0-9a-f]")])])
  | .string => some (Json.mkObj [("type", .str "string")])
  | .nat => some (Json.mkObj [("type", .str "integer"), ("minimum", toJson (0 : Nat)),
      ("maximum", toJson (9007199254740991 : Nat))])
  | .list item => (fieldSchema item).map fun s =>
      Json.mkObj [("type", .str "array"), ("items", s)]
  | _ => none

def tool (op : Op) : Option Json := do
  let props ← (op.fields).mapM fun (name, s) => (fieldSchema s).map (name, ·)
  return Json.mkObj [("name", .str op.name), ("description", .str op.description),
    ("inputSchema", Json.mkObj [("type", .str "object"),
      ("properties", Json.mkObj props), ("additionalProperties", .bool false),
      ("required", toJson (op.fields.map (·.1)))]),
    ("annotations", Json.mkObj [("readOnlyHint", .bool true), ("openWorldHint", .bool false)])]

def version : String := "2026-07-28"
def resultMeta : Json := Json.mkObj [("io.modelcontextprotocol/serverInfo",
  Json.mkObj [("name", .str "effect4-snapshot-preview"), ("version", .str "0.1-probe")])]
def complete (fields : List (String × Json)) : Json :=
  Json.mkObj ([("resultType", .str "complete"), ("_meta", resultMeta)] ++ fields)
def success (id result : Json) : Json :=
  Json.mkObj [("jsonrpc", .str "2.0"), ("id", id), ("result", result)]
/-- Integral decimal notation has the same value as integer notation.
Stop when a nonzero decimal digit remains, without constructing a power of ten. -/
def decimalInteger? : Nat → Int → Option Int
  | 0, m => some m
  | n + 1, m =>
    if m == 0 then some 0
    else if m % 10 == 0 then decimalInteger? n (m / 10)
    else none

def jsonInteger? : Json → Option Int
  | .num n => decimalInteger? n.exponent n.mantissa
  | _ => none

def pathIndex? (j : Json) : Option Nat := do
  let n ← jsonInteger? j
  if 0 ≤ n && n ≤ 9007199254740991 then some n.toNat else none

def idValid : Json → Bool
  | .str _ => true
  | j => (jsonInteger? j).isSome

def error (id : Option Json) (code : Int) (message : String)
    (data : Option Json := none) : Json :=
  Json.mkObj ([("jsonrpc", .str "2.0"),
    ("error", Json.mkObj ([("code", toJson code), ("message", .str message)] ++
      (data.map ("data", ·)).toList))] ++
    ((id.filter idValid).map ("id", ·)).toList)

/-- Read only this prototype's finite shape profile, matching the emitted field schema. -/
def fieldValid : Shape → Json → Bool
  | .bytes, .str s => (canonicalHex? s).isSome
  | .string, .str _ => true
  | .nat, j => (pathIndex? j).isSome
  | .list item, .arr xs => xs.all (fieldValid item)
  | _, _ => false

def argsValid (op : Op) (j : Json) : Bool :=
  match j.getObj? with
  | .error _ => false
  | .ok obj =>
    obj.toArray.size == op.fields.length &&
    op.fields.all fun (name, s) =>
      match j.getObjVal? name with
      | .ok value => fieldValid s value
      | .error _ => false

def readArgs (op : Op) (args : Json) : Except String ((Bytes × Bytes) × Request) := do
  if !argsValid op args then throw "arguments do not match this tool's input schema"
  let program ← args.getObjValAs? String "program"
  let holes ← args.getObjValAs? String "holes"
  let pathJson ← args.getObjVal? "path"
  let pathArray ← pathJson.getArr?
  let path ← pathArray.toList.mapM fun j =>
    match pathIndex? j with
    | some n => pure n
    | none => throw "path must contain safe nonnegative integers"
  let some pb := canonicalHex? program | throw "program bytes do not read"
  let some hb := canonicalHex? holes | throw "hole bytes do not read"
  let req ← match op with
    | .fill => do
      let replacement ← args.getObjValAs? String "replacement"
      pure { op := "fill", path, replacement := some replacement }
    | .omit => do
      let holeName ← args.getObjValAs? String "holeName"
      pure { op := "omit", path, holeName }
    | .inspect | .render => pure { op := "view", path }
  return ((pb, hb), req)

def render (l : EditSession) (path : List Nat) : String :=
  let base := Tools.View.Program.sessionPage l (some path) "Snapshot preview" "" "" ""
  let page := { base with
    graph := some { title := "program", laid := Tools.View.Flow.ofPage l.sketch.program base }
    code := Tools.View.Program.codePanel l.sketch.program (l.app.withHoles l.sketch.holes).rows (l.sketch.holes.map (·.name)) }
  let (w, h) := Tools.View.pageSize 1280 page
  Tools.View.svg {} w.toNat h.toNat 1 (Tools.View.lowerAll 1 (Tools.View.pageCalls {} 1280 page))

def toolResult (value : Json) (bad : Bool := false) : Json :=
  complete [("structuredContent", value), ("content", Json.arr #[Json.mkObj
    [("type", .str "text"), ("text", .str value.compress)]]), ("isError", .bool bad)]

def call (cache : Option Snapshot.Cache) (op : Op) (args : Json) :
    Option Snapshot.Cache × Except String Json :=
  match readArgs op args with
  | .error why => (cache, .error why)
  | .ok (bytes, req) =>
    match Snapshot.resolve bytes cache with
    | none => (cache, .ok (toolResult (Json.mkObj [("refused", .str "snapshot does not decode")]) true))
    | some l =>
      let nextCache := some (Snapshot.Cache.mk bytes l)
      let (st, ans) := answer { session := some l } req
      match st.session with
      | none => (nextCache, .ok (toolResult (toJson ans) true))
      | some out =>
        let encoded := out.sketch.encode
        let fields := [("answer", toJson ans),
          ("snapshot", Json.mkObj [("program", .str (hexString encoded.1)),
            ("holes", .str (hexString encoded.2))]),
          ("path", toJson req.path), ("published", .bool false)] ++
          (if op == .render then [("svg", .str (render out req.path))] else [])
        (nextCache, .ok (toolResult (Json.mkObj fields) (!ans.ok)))

/-- One self-contained request; notifications have no reply and change no cache. -/
def dispatch (cache : Option Snapshot.Cache) (j : Json) : Option Snapshot.Cache × Option Json :=
  let id := (j.getObjVal? "id").toOption
  let refused (code : Int) (why : String) := (cache, some (error id code why))
  if (j.getObjValAs? String "jsonrpc").toOption != some "2.0" then
    (cache, some (error none (-32600) "jsonrpc must be 2.0"))
  else match (j.getObjValAs? String "method").toOption with
  | none => (cache, some (error id (-32600) "method must be a string"))
  | some method =>
    match id with
    | none => (cache, none)
    | some rid =>
      if !idValid rid then (cache, some (error none (-32600) "id must be a string or integer"))
      else match (j.getObjVal? "params").toOption with
      | none => refused (-32602) "params and per-request metadata are required"
      | some params =>
        let checked : Except String String := do
          let m ← params.getObjVal? "_meta"
          let v ← m.getObjValAs? String "io.modelcontextprotocol/protocolVersion"
          let capabilities ← m.getObjVal? "io.modelcontextprotocol/clientCapabilities"
          let _ ← capabilities.getObj?
          return v
        match checked with
        | .error _ => refused (-32602) "missing or malformed per-request metadata"
        | .ok v =>
          if v != version then
            (cache, some (error id (-32022) "unsupported protocol version"
              (some (Json.mkObj [("supported", toJson [version]), ("requested", .str v)]))))
          else match method with
          | "server/discover" =>
            (cache, some (success rid (complete [("supportedVersions", toJson [version]),
              ("capabilities", Json.mkObj [("tools", Json.mkObj [])]),
              ("ttlMs", toJson (0 : Nat)), ("cacheScope", .str "public"),
              ("instructions", .str "Experimental snapshot previews. Every call carries canonical program and hole bytes. No root is published. Empty application profile only.")])))
          | "ping" => (cache, some (success rid (complete [])))
          | "tools/list" =>
            if (params.getObjVal? "cursor").isOk then refused (-32602) "this fixed tool list has no cursor"
            else (cache, some (success rid (complete [("tools", Json.arr (Op.all.filterMap tool).toArray),
              ("ttlMs", toJson (0 : Nat)), ("cacheScope", .str "public")])))
          | "tools/call" =>
            match (params.getObjValAs? String "name").toOption,
                (params.getObjVal? "arguments").toOption with
            | some name, some args =>
              match Op.all.find? (fun op => op.name == name) with
              | none => refused (-32602) "unknown tool"
              | some op =>
                let (cache', result) := call cache op args
                match result with
                | .error why => (cache', some (error id (-32602) why))
                | .ok value => (cache', some (success rid value))
            | _, _ => refused (-32602) "name and arguments are required"
          | _ => refused (-32601) "unknown method"

end LiveGraphPreview

/-- Stdio probe driver. Stdout contains JSON-RPC responses only. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut cache : Option Tools.Session.Snapshot.Cache := none
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    if !line.trimAscii.toString.isEmpty then
      if line.utf8ByteSize > 1048576 then
        IO.println ((LiveGraphPreview.error none (-32600) "probe request exceeds 1 MiB").compress)
      else
        match Lean.Json.parse line with
        | .error _ => IO.println ((LiveGraphPreview.error none (-32700) "invalid JSON").compress)
        | .ok j =>
          let (next, reply) := LiveGraphPreview.dispatch cache j
          cache := next
          if let some response := reply then IO.println response.compress
      stdout.flush
