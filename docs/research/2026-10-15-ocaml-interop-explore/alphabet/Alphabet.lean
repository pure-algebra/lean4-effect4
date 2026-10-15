import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Test.Dogfood.Scenario.Todo

/-!
# The RPC message alphabet, read from Effect and derived from the rows: a probe

Exploration probe (2026-10-15). Run: `lake env lean` on this file from the repository root.

1. `repOf` reads rc.112's `SchemaRepresentation` JSON (`vendored/effect-rpc-rc112.json`, written
   by `export.ts` from Effect's own schemas) into the tree's `Representation`. A node it does not
   read yet is refused by its tag.
2. Each of Effect's schemas for the to-do RPC group goes through the existing reader
   `Bridge.ofSchema`, as it stands, and through a probe-only pre-normalisation (`widen`). Each is
   compared with the type the to-do rows declare (`TodoRepo.rows`).
3. The alphabet is derived from the rows (`fromServer`, `fromClient`) and checked against the
   wire messages recorded in `../rpc/server.log`, with the existing codec (`Schema.decode`).

Each `#eval` prints what it finds; nothing here is a theorem.
-/

open Effect4 Effect4.Program Effect4.Schema

namespace Explore.Alphabet

/-! ## 1. rc.112's representation JSON as the tree's `Representation` -/

def float64Of (n : Lean.JsonNumber) : Float64 := ⟨n.toFloat.toBits⟩

def entries (kvs : Std.TreeMap.Raw String Lean.Json compare) : List (String × Lean.Json) :=
  kvs.toList

def jsonOf : Nat → Lean.Json → Except String Json
  | 0, _ => .error "too deep"
  | _ + 1, .null => pure .null
  | _ + 1, .bool b => pure (.bool b)
  | _ + 1, .num n => pure (.number (float64Of n))
  | _ + 1, .str s => pure (.str s)
  | f + 1, .arr xs => .arr <$> xs.toList.mapM (jsonOf f)
  | f + 1, .obj kvs => .obj <$> (entries kvs).mapM fun (k, v) => do pure (k, ← jsonOf f v)

def annotationsOf (f : Nat) (j : Lean.Json) : Except String Annotations :=
  match j.getObjVal? "annotations" with
  | .error _ => pure none
  | .ok (.obj kvs) => some <$> (entries kvs).mapM fun (k, v) => do
      pure { key := k, payload := ← jsonOf f v }
  | .ok _ => .error "annotations: not an object"

def literalOf (j : Lean.Json) : Except String LiteralValue := do
  match ← j.getObjValAs? String "type" with
  | "string" => .string <$> j.getObjValAs? String "value"
  | "boolean" => .boolean <$> j.getObjValAs? Bool "value"
  | "number" => (.number ∘ float64Of) <$> j.getObjValAs? Lean.JsonNumber "value"
  | other => .error s!"literal type {other} is not read yet"

def arr (j : Lean.Json) (k : String) : Except String (List Lean.Json) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => pure xs.toList
  | .ok _ => .error s!"{k}: not an array"
  | .error _ => pure []

mutual
def repOf : Nat → Lean.Json → Except String Representation
  | 0, _ => .error "too deep"
  | f + 1, j => do
    let tag ← j.getObjValAs? String "_tag"
    let ann ← annotationsOf f j
    let checks ← (← arr j "checks").mapM (checkOf f)
    match tag with
    | "String" => pure (.string ann checks)
    | "Number" => pure (.number ann checks)
    | "Boolean" => pure (.boolean ann checks)
    | "Null" => pure (.null ann checks)
    | "Undefined" => pure (.undefined ann checks)
    | "Void" => pure (.void ann checks)
    | "Never" => pure (.never ann checks)
    | "Unknown" => pure (.unknown ann checks)
    | "Any" => pure (.any ann checks)
    | "Literal" => pure (.literal ann checks (← literalOf (← j.getObjVal? "literal")))
    | "Reference" => pure (.reference ⟨← j.getObjValAs? String "$ref"⟩)
    | "Declaration" => do
      let r ← j.getObjVal? "representation"
      let payload ← jsonOf f (r.getObjValD "payload")
      let params ← (← arr j "typeParameters").mapM (repOf f)
      pure (.declaration ⟨← r.getObjValAs? String "id", payload⟩ ann params checks)
    | "Union" => do
      let types ← (← arr j "types").mapM (repOf f)
      let mode ← match ← j.getObjValAs? String "mode" with
        | "anyOf" => pure UnionMode.anyOf
        | "oneOf" => pure UnionMode.oneOf
        | other => Except.error s!"union mode {other}"
      pure (.union ann checks types mode)
    | "Objects" => do
      let props ← (← arr j "propertySignatures").mapM (propOf f)
      let idx ← (← arr j "indexSignatures").mapM (indexOf f)
      pure (.objects ann checks props idx)
    | "Arrays" => do
      let elements ← (← arr j "elements").mapM (elementOf f)
      let rest ← (← arr j "rest").mapM (repOf f)
      pure (.arrays ann checks elements rest)
    | other => .error s!"the node {other} is not read yet"
def checkOf : Nat → Lean.Json → Except String Check
  | 0, _ => .error "too deep"
  | f + 1, j => do
    let ann ← annotationsOf f j
    match ← j.getObjValAs? String "_tag" with
    | "Filter" => do
      let r ← j.getObjVal? "representation"
      let payload ← jsonOf f (r.getObjValD "payload")
      pure (.filter ⟨← r.getObjValAs? String "id", payload, none⟩ ann
        ((j.getObjValAs? Bool "aborted").toOption.getD false))
    | other => .error s!"the check {other} is not read yet"
def propOf : Nat → Lean.Json → Except String PropertySignature
  | 0, _ => .error "too deep"
  | f + 1, j => do
    let name ← (← j.getObjVal? "name").getObjValAs? String "value"
    pure { name := .string name, type := ← repOf f (← j.getObjVal? "type"),
           isOptional := ← j.getObjValAs? Bool "isOptional", isMutable := ← j.getObjValAs? Bool "isMutable",
           annotations := ← annotationsOf f j }
def elementOf : Nat → Lean.Json → Except String Element
  | 0, _ => .error "too deep"
  | f + 1, j => do
    pure { isOptional := ← j.getObjValAs? Bool "isOptional", type := ← repOf f (← j.getObjVal? "type"),
           annotations := ← annotationsOf f j }
def indexOf : Nat → Lean.Json → Except String IndexSignature
  | 0, _ => .error "too deep"
  | f + 1, j => do
    pure { parameter := ← repOf f (← j.getObjVal? "parameter"), type := ← repOf f (← j.getObjVal? "type") }
end

/-- A document: the root and its references table. -/
def documentOf (j : Lean.Json) : Except String (Representation × List (String × Representation)) := do
  let root ← repOf 64 (← j.getObjVal? "representation")
  let refs ← match j.getObjVal? "references" with
    | .ok (.obj kvs) => (entries kvs).mapM fun (k, v) => do pure (k, ← repOf 64 v)
    | _ => pure []
  pure (root, refs)

/-! ## 2. The probe-only widening: what `Bridge.ofSchema` would need -/

/-- Resolve `$ref`s, drop the `~identifier` annotation rc.112 puts on a tagged error, read a
one-member union as its member and an n-member union as nested binary unions. Probe only: each
step is a candidate change to the reader, recorded in the note. -/
def widen (refs : List (String × Representation)) : Nat → Representation → Representation
  | 0, r => r
  | f + 1, r =>
    let w := widen refs f
    let dropId : Annotations → Annotations := fun
      | none => none
      | some es => match es.filter (·.key != "~identifier") with | [] => none | rest => some rest
    match r with
    | .reference ⟨k⟩ => match refs.lookup k with | some t => w t | none => r
    | .union ann checks [one] _ => if checks.isEmpty && dropId ann = none then w one else r
    | .union ann checks (a :: b :: c :: rest) mode =>
      w (.union ann checks [a, .union none [] (b :: c :: rest) mode] mode)
    | .union ann checks ts mode => .union (dropId ann) checks (ts.map w) mode
    | .objects ann checks props idx =>
      .objects (dropId ann) checks (props.map fun p => { p with type := w p.type }) idx
    | .declaration rep ann params checks => .declaration rep ann (params.map w) checks
    | .arrays ann checks els rest => .arrays ann checks (els.map fun e => { e with type := w e.type }) (rest.map w)
    | other => other

def readTy (j : Lean.Json) (widened : Bool) : Except String (Option Ty) := do
  let (root, refs) ← documentOf j
  pure (Bridge.ofSchema (if widened then widen refs 64 root else root))

/-! ## 3. The alphabet, derived from the rows -/

open Test.Dogfood.Scenario.Todo in
def todoRows : List Row := TodoRepo.rows.map (·.row)

/-- Effect's request id: a string or a number. The probe reads a number as `int`. -/
def idTy : Ty := .union .string .int

def unionAll : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: ts => .union t (unionAll ts)

def method (row : Row) : String := (row.spelling.splitOn ".").getLast!

def msg (tag : String) (fields : List (String × Ty)) : Ty :=
  .record (("_tag", false, .lit tag) :: fields.map fun (n, t) => (n, false, t))

/-- What the server may send, for a table: one `Exit` per row at the row's own answer and error,
then `Pong` and `Defect`. -/
def fromServer (rows : List Row) : Ty :=
  unionAll (rows.map (fun row => msg "Exit" [("requestId", idTy), ("exit", .exitOf row.answer row.error)])
    ++ [msg "Pong" [], msg "Defect" [("defect", .unknown)]])

/-- What the client may send, for a table: one `Request` per row with its tag and payload type. -/
def fromClient (rows : List Row) : Ty :=
  unionAll (rows.map (fun row => msg "Request"
      [("id", idTy), ("tag", .lit (method row)), ("payload", row.request),
       ("headers", .list (.prod .string .string))])
    ++ [msg "Ack" [("requestId", idTy)], msg "Interrupt" [("requestId", idTy)], msg "Ping" [], msg "Eof" []])

/-! ## The runs -/

def readFile (path : String) : IO Lean.Json := do
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError e)

def showTy (r : Except String (Option Ty)) : String :=
  match r with
  | .error e => s!"unread: {e}"
  | .ok none => "refused by ofSchema"
  | .ok (some t) => reprStr t

def here : String := "docs/research/2026-10-15-ocaml-interop-explore/alphabet/"

-- Effect's schemas for the to-do group, read as they are and widened, beside the rows' types.
#eval show IO Unit from do
  let doc ← readFile (here ++ "vendored/effect-rpc-rc112.json")
  let rpcs := (doc.getObjValAs? (Array Lean.Json) "rpcs").toOption.getD #[]
  for rpc in rpcs do
    let tag := (rpc.getObjValAs? String "tag").toOption.getD "?"
    let row := todoRows.find? (method · == tag)
    IO.println s!"── {tag}  (row {row.map (·.spelling) |>.getD "none"})"
    for (part, mine) in [("payload", row.map (·.request)), ("success", row.map (·.answer)),
        ("error", row.map (·.error)), ("exit", row.map fun r => .exitOf r.answer r.error)] do
      let j := (rpc.getObjVal? part).toOption.getD .null
      let raw := readTy j false
      let wide := readTy j true
      let agree := match wide, mine with | .ok (some t), some m => t == m | _, _ => false
      IO.println s!"   {part}: ofSchema {showTy raw}"
      IO.println s!"   {part}: widened  {showTy wide}"
      IO.println s!"   {part}: the row  {mine.map reprStr |>.getD "none"}   agree: {agree}"
  let env := (doc.getObjVal? "envelope").toOption.getD .null
  IO.println s!"── the envelope: ofSchema {showTy (readTy env false)}"
  IO.println s!"── the envelope: widened  {showTy (readTy env true)}"

-- The derived alphabet against the wire: each recorded server message, decoded at `fromServer`.
#eval show IO Unit from do
  let log ← IO.FS.lines (here ++ "../rpc/server.log")
  let lines := log.toList.filterMap fun l =>
    match l.splitOn "  reply " with
    | [_, j] => if j.startsWith "[" then none else some j
    | _ => none
  let t := fromServer todoRows
  let mut admitted := 0
  for line in lines.take 9 do
    match Lean.Json.parse line >>= jsonOf 64 with
    | .error e => IO.println s!"unparsed {e}"
    | .ok j =>
      let ok := (Schema.decode t j).isSome
      if ok then admitted := admitted + 1
      IO.println s!"   {if ok then "admitted" else "REFUSED "}  {line.take 110}"
  IO.println s!"── {admitted} of {min 9 lines.length} recorded server messages admitted by the derived alphabet"

-- The derived client alphabet: a well-typed request, and the red control of a mistyped payload.
#eval show IO Unit from do
  let t := fromClient todoRows
  for line in ["{\"_tag\":\"Request\",\"id\":0,\"tag\":\"insert\",\"payload\":\"milk\",\"headers\":[]}",
               "{\"_tag\":\"Request\",\"id\":1,\"tag\":\"insert\",\"payload\":42,\"headers\":[]}",
               "{\"_tag\":\"Interrupt\",\"requestId\":6}", "{\"_tag\":\"Ping\"}"] do
    match Lean.Json.parse line >>= jsonOf 64 with
    | .error e => IO.println s!"unparsed {e}"
    | .ok j => IO.println s!"   {if (Schema.decode t j).isSome then "admitted" else "refused "}  {line}"
  -- the derived alphabet goes back to rc.112's representation through the existing writer
  IO.println s!"── fromClient round trip through Bridge.schema and ofSchema: {Bridge.ofSchema (Bridge.schema t) == some t}"
  IO.println s!"── fromServer round trip through Bridge.schema and ofSchema: {Bridge.ofSchema (Bridge.schema (fromServer todoRows)) == some (fromServer todoRows)}"

end Explore.Alphabet
