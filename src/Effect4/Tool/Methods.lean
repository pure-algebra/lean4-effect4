import Effect4.Tool.ToolDerived

/-!
# Tool.Methods — the tool's methods, as an agent's tool table

An agent drives the tool through a tool table: one entry per method, with what the method does
and the JSON Schema of its arguments (an MCP server's `tools/list`). The table is derived here
from the request's own shape document (`shape Request`), so nothing names a request by hand:

- each case of `Request` (`act`, `ask`) holds one field, an `Action` or a `Query`; each case of
  that sum is one method;
- a method's arguments are its case's fields, and their schema is `schemaIn` of each field's
  shape, with the definitions they reach (`reachable`) under `$defs`;
- the one hand input is `descriptions`: for each case, its wire name (`Request.method`'s) and what
  it does. `Test/Program/ToolMethodsControls.lean` holds it to `supportedMethods`, in order.

`schemaIn` reads a shape as the tools print it (`Canonical.printArrays`, `CodecProfile`): a
structure is an object of its fields; a sum is a string when no case has a field, an array when it
is a list family (`listItem?`), and otherwise an object whose `_tag` names the case; a list is an
array; an option is `null` or its item; a pair is a
two-element array; a natural is an integer up to `CodecProfile.natLimit`; bytes and digests are
lower-case hex. Every object refuses extra properties, as the exact reader does.

The schema is built as text, not as `Effect4.Json`: the native shell reads this table through the
generated code, where a binary64 number does not lower exactly. Nothing here traverses a string
(a character walk neither lowers nor stays inside the axiom ceiling): a JSON string is its text
between quotes, so every name and description must need no escape, which the controls check.
-/

set_option autoImplicit false

namespace Effect4.Tool.Methods

open Effect4.Store

/-- **One method as an agent calls it**: its wire name, what it does, the case of `Request` it
builds (`kind`, holding its argument object under `field`), the `Action` or `Query` case it names,
and the JSON Schema of its arguments, as JSON text. -/
structure Entry where
  name : String
  description : String
  kind : String
  field : String
  caseName : String
  schema : String

/-- **Each method's case, wire name and what it does**, for an agent: the table's one hand input.
The wire name is `Request.method`'s for the case. -/
def descriptions : List (String × String × String) := [
  ("open_", "open", "Open a document: a program with holes (the sketch: the program and its hole table) at \
an application (its host rows, services and types), under a name. It replaces the open document \
and drops pending fills. Answers the document's view: its snapshot, the program's type or the \
located refusals of Lean's checker, and every hole with its address and typed focus."),
  ("edit", "edit", "Apply one document action at the snapshot you read (`at_`): a commit of several \
changes under one feed policy, one draft edit, or the revert of an accepted entry. A moved \
document refuses `stale` and changes nothing. Answers the new view and a receipt of what each \
change did."),
  ("fill", "fill", "Add pending fills at a snapshot: each item puts a program at an address, and each is \
certified alone against the snapshot's typed source (kept exact). Answers one outcome per item: \
applied, already there, or refused with its reason. Nothing changes the document until `publish`."),
  ("publish", "publish", "Publish the pending fills as one commit at the snapshot they were certified at. \
Refuses when no fill is pending or the document moved since."),
  ("reset", "reset", "Drop the pending fills. Answers the fillings it dropped."),
  ("start", "start", "Admit the document's program at its application and start a live run on the \
machine, under a budget. Answers the run's id, where it came from, and the run's view: its \
state, outcome, the host calls it waits on, and its internal waits."),
  ("restore", "restore", "Restore a saved run record (from `run` with form `record`): it reruns admission \
and replays the record's journal, so the restored run is the saved one. Answers the new run id \
and its view."),
  ("play", "play", "Feed host events to a run in order: control decisions, holding a call, receiving \
and applying a reply. An event whose call selector does not resolve refuses the whole list and \
changes nothing. Answers each event's verdict and the run's view."),
  ("doc", "doc", "Read the document's view; with an address, also inspect it: the sub-program there, \
its signature context, its typed focus, its table entry and any refusal there."),
  ("history", "history", "Read the document's accepted actions, oldest first."),
  ("fills", "fills", "Read the pending fills and the snapshot they are anchored at."),
  ("suggest", "suggest", "Suggest programs for a place (a hole by index, or an address with the program \
expected there): your supplied candidates, the variables in scope, unit requests of the rows and \
typed sub-programs elsewhere, each checked at the place as a fill would be, with its evidence \
(fits exactly, type mismatch, refused, another scope). Paged by cursor and limit; the answer \
gives the next cursor."),
  ("run", "run", "Read a run (by id) in one form: its view, its saved record (for `restore`), or its \
ordered journal."),
  ("preview", "preview", "Run the document's program in the call tree, without starting a run: settle it \
under a reply tape at the least budget that does not cut it, answer its runs at every budget up \
to a limit (frames), or explore its paths with replies drawn from the rows' types."),
  ("dry", "dry", "Answer an action as if it were applied, and change nothing."),
  ("discover", "discover", "List the supported methods and their versions."),
  ("table", "table", "Read the program's whole address table: for every address, the typing environment \
there and, at a program, Lean's checker answer."),
  ("addresses", "addresses", "List every address of the program as written, in the table's order."),
  ("slots", "slots", "Read the term slots of the node at an address (one named slot, or every slot): \
each slot's term, the environment it reads and its type there.")]

/-! ## JSON text -/

/-- A JSON string literal of text that needs no escape (no `"`, `\\` or control character). -/
def quote (s : String) : String := "\"" ++ s ++ "\""

/-- A JSON object from its entries' keys and value texts. -/
def object (entries : List (String × String)) : String :=
  "{" ++ ",".intercalate (entries.map fun (k, v) => quote k ++ ":" ++ v) ++ "}"

/-- A JSON array from its items' texts. -/
def array (items : List String) : String :=
  "[" ++ ",".intercalate items ++ "]"

/-- Lower-case hex of whole bytes. -/
def hexPattern : String := quote "^([0-9a-f][0-9a-f])*$"

/-- Thirty-two bytes of lower-case hex. -/
def digestPattern : String := quote "^[0-9a-f]{64}$"

/-! ## Shapes as JSON Schema -/

mutual
/-- **The JSON Schema of a shape**, as the JSON profile prints it. -/
def schemaIn : Shape → String
  | .unit => object [("type", quote "null")]
  | .bool => object [("type", quote "boolean")]
  | .nat => object [("type", quote "integer"), ("minimum", "0"),
      ("maximum", "9007199254740991")]
  | .string => object [("type", quote "string")]
  | .bytes => object [("type", quote "string"), ("pattern", hexPattern)]
  | .digest => object [("type", quote "string"), ("pattern", digestPattern)]
  | .list item => object [("type", quote "array"), ("items", schemaIn item)]
  | .option item => object [("anyOf", array [object [("type", quote "null")], schemaIn item])]
  | .pair a b => object [("type", quote "array"), ("prefixItems", array [schemaIn a, schemaIn b]),
      ("minItems", "2"), ("maxItems", "2")]
  | .struct _ fields => objectSchema [] (schemaFields fields)
  | .sum _ cases =>
    let tagged :=
      if allNullary cases then object [("enum", array (cases.map fun c => quote c.1))]
      else object [("oneOf", array (schemaCases cases))]
    -- the list rule (`listItem?`): the tools print a list family as an array
    match cases with
    | [(n0, t0, []), (n1, t1, [(k0, head), (k1, _)])] =>
      if n0 = "nil" ∧ n1 = "cons" ∧ k0 = "head" ∧ k1 = "tail" ∧ t0 ≠ t1 then
        object [("type", quote "array"), ("items", schemaIn head)]
      else tagged
    | _ => tagged
  | .ref _ => object [("type", quote "string"), ("pattern", digestPattern)]
  | .anyRef => objectSchema [] [("kind", object [("type", quote "string")]),
      ("address", object [("type", quote "string"), ("pattern", digestPattern)])]
  | .named name => object [("$ref", quote ("#/$defs/" ++ name))]
  | .value => object []

/-- Each field's name and schema. -/
def schemaFields : List (String × Shape) → List (String × String)
  | [] => []
  | (name, s) :: rest => (name, schemaIn s) :: schemaFields rest

/-- One object schema per case, its `_tag` the case's name. -/
def schemaCases : List (String × Nat × List (String × Shape)) → List String
  | [] => []
  | (name, _, fields) :: rest =>
    objectSchema [("_tag", object [("const", quote name)])] (schemaFields fields) :: schemaCases rest

/-- An object with exactly these properties, all required. -/
def objectSchema (tag : List (String × String)) (fields : List (String × String)) : String :=
  let all := tag ++ fields
  object [("type", quote "object"), ("properties", object all),
    ("required", array (all.map fun f => quote f.1)), ("additionalProperties", "false")]
end

mutual
/-- The definitions a shape names directly. -/
def namesIn : Shape → List String
  | .list s | .option s => namesIn s
  | .pair a b => namesIn a ++ namesIn b
  | .struct _ fields => namesFields fields
  | .sum _ cases => namesCases cases
  | .named name => [name]
  | _ => []

/-- The definitions a list of fields names directly. -/
def namesFields : List (String × Shape) → List String
  | [] => []
  | (_, s) :: rest => namesIn s ++ namesFields rest

/-- The definitions a list of cases names directly. -/
def namesCases : List (String × Nat × List (String × Shape)) → List String
  | [] => []
  | (_, _, fields) :: rest => namesFields fields ++ namesCases rest
end

/-- **The definitions reachable from some names**, each once: one more round for each definition
the table holds, which is enough to close it. -/
def reachable (defs : List (String × Shape)) (start : List String) : List String :=
  go (defs.length + 1) start.eraseDups
where
  go : Nat → List String → List String
    | 0, found => found
    | fuel + 1, found =>
      let next := (found ++ found.flatMap fun n =>
        ((defs.lookup n).map namesIn).getD []).eraseDups
      if next.length = found.length then found else go fuel next

/-- **A method's argument schema**: an object of its case's fields, with the definitions they reach
under `$defs`. -/
def argumentSchema (defs : List (String × Shape)) (fields : List (String × Shape)) : String :=
  let used := reachable defs (namesFields fields)
  let base := [("type", quote "object"), ("properties", object (schemaFields fields)),
    ("required", array (fields.map fun f => quote f.1)), ("additionalProperties", "false")]
  object (if used.isEmpty then base
    else base ++ [("$defs", object (used.filterMap fun n => (defs.lookup n).map fun s => (n, schemaIn s)))])

/-- **The tool table**: one entry per case of each sum a `Request` case holds, in case order. -/
def entries : List Entry :=
  let doc := shape Request
  match headShape doc.defs doc.root with
  | .sum _ kinds => kinds.flatMap fun (kind, _, fields) =>
    match fields with
    | [(field, sub)] =>
      match headShape doc.defs sub with
      | .sum _ cases => cases.map fun (caseName, _, args) =>
        let (name, description) := (descriptions.lookup caseName).getD (caseName, "")
        ⟨name, description, kind, field, caseName, argumentSchema doc.defs args⟩
      | _ => []
    | _ => []
  | _ => []

end Effect4.Tool.Methods
