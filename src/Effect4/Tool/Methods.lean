import Effect4.Tool.ToolDerived

/-!
# Tool.Methods — the tool's methods, as an agent's tool table

An agent drives the tool through a tool table: one entry per method, with what the method does
and the JSON Schema of its arguments (an MCP server's `tools/list`). The table is derived here
from the request's own shape document (`shape Request`), so nothing names a request by hand:

- each case of `Request` (`act`, `ask`) holds one field, an `Action` or a `Query`; each case of
  that sum is one method;
- a method's arguments are its case's fields, and their schema is `schemaIn` of each field's
  shape, with the definitions they reach (`definitionsOf`) under `$defs`;
- the one hand input is `descriptions`: for each case, its wire name (`Request.method`'s) and what
  it does. `Test/Program/ToolMethodsControls.lean` holds it to `supportedMethods`, in order.

`schemaIn` reads a shape as the tools print it (`Canonical.printArrays`, `CodecProfile`): a
structure is an object of its fields; a sum is a string when no case has a field, an array when it
is a list family (`listItem?`), and otherwise an object whose `_tag` names the case, the cases
with no field sharing one branch; a list is an array; an option is `null` or its item; a pair is a
two-element array; a natural is an integer up to `CodecProfile.natLimit`; bytes and digests are
lower-case hex. Every object refuses extra properties, as the exact reader does.

The table is what an agent pays for on every connection, so each schema says a thing once:

- a structure or a sum met in more than one place is written once under `$defs`, by its name;
- the shape document's table (the program's grammar: programs, types, terms, values, all
  recursive) is spelled by the `describe` tool, one schema document per definition, and a method's
  schema names each such definition it reaches with a pointer to `describe` (`onDemand`);
- `dry`'s action is one of the action tools' calls, so its schema names their cases and leaves
  their arguments to their own schemas.

So a method's schema is exact up to those names: with each `describe` answer put in place of its
pointer, and each action tool's schema in place of `dry`'s case, it accepts what the exact reader
accepts.

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

/-- What `describe` does, for an agent. -/
def describeText : String :=
  "Answer the JSON Schema of one definition that the tools' schemas name under `$defs` and leave \
to this tool: the program's grammar (programs, types, terms, values). The answer is a schema \
document of its own, with every definition it reaches. Ask for a definition before you write one."

/-- What a schema says where it leaves a definition to `describe`. -/
def onDemandText : String := "Its schema is the answer of `describe` for this definition's name."

/-- What a schema says of a sum whose cases are the tools: `dry`'s action. -/
def toolCallText : String :=
  "One tool's call: `_tag` is the tool's case (open_ for open), and the other fields are that \
tool's arguments, as its own schema spells them."

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

/-- A pointer to a definition under `$defs`. -/
def ref (name : String) : String := object [("$ref", quote ("#/$defs/" ++ name))]

/-- The keywords of an object with exactly these properties, all required. -/
def exactly (fields : List (String × String)) : List (String × String) :=
  [("properties", object fields), ("required", array (fields.map fun f => quote f.1)),
    ("additionalProperties", "false")]

/-- An object with exactly these properties, all required. -/
def objectSchema (fields : List (String × String)) : String :=
  object (("type", quote "object") :: exactly fields)

/-- The `_tag` of one case, or of several cases sharing a branch. -/
def tagOf : List String → String
  | [name] => object [("const", quote name)]
  | names => object [("enum", array (names.map quote))]

/-! ## Shapes as JSON Schema -/

/-- **How a schema writes the shapes it meets**: the structures and sums it writes once under
`$defs` and points to (`shared`), and the sums whose cases are the tools (`tools`), written as a
call of one of them. -/
structure Plan where
  shared : List String := []
  tools : List String := []

mutual
/-- **The JSON Schema of a shape**, as the JSON profile prints it, under a plan. -/
def schemaIn (p : Plan) : Shape → String
  | .unit => object [("type", quote "null")]
  | .bool => object [("type", quote "boolean")]
  | .nat => object [("type", quote "integer"), ("minimum", "0"),
      ("maximum", "9007199254740991")]
  | .string => object [("type", quote "string")]
  | .bytes => object [("type", quote "string"), ("pattern", hexPattern)]
  | .digest => object [("type", quote "string"), ("pattern", digestPattern)]
  | .list item => object [("type", quote "array"), ("items", schemaIn p item)]
  | .option item => object [("anyOf", array [object [("type", quote "null")], schemaIn p item])]
  | .pair a b => object [("type", quote "array"), ("prefixItems", array [schemaIn p a, schemaIn p b]),
      ("minItems", "2"), ("maxItems", "2")]
  | .struct name fields => if p.shared.contains name then ref name else objectSchema (schemaFields p fields)
  | .sum name cases =>
    let bare := (cases.filter (·.2.2.isEmpty)).map (·.1)
    let tagged :=
      if allNullary cases then object [("enum", array (cases.map fun c => quote c.1))]
      else object [("type", quote "object"), ("oneOf", array
        ((if bare.isEmpty then [] else [object (exactly [("_tag", tagOf bare)])]) ++ schemaCases p cases))]
    if p.shared.contains name then ref name
    else if p.tools.contains name then
      object [("type", quote "object"), ("properties", object [("_tag", tagOf (cases.map (·.1)))]),
        ("required", array [quote "_tag"]), ("description", quote toolCallText)]
    else
    -- the list rule (`listItem?`): the tools print a list family as an array
    match cases with
    | [(n0, t0, []), (n1, t1, [(k0, head), (k1, _)])] =>
      if n0 = "nil" ∧ n1 = "cons" ∧ k0 = "head" ∧ k1 = "tail" ∧ t0 ≠ t1 then
        object [("type", quote "array"), ("items", schemaIn p head)]
      else tagged
    | _ => tagged
  | .ref _ => object [("type", quote "string"), ("pattern", digestPattern)]
  | .anyRef => objectSchema [("kind", object [("type", quote "string")]),
      ("address", object [("type", quote "string"), ("pattern", digestPattern)])]
  | .named name => ref name
  | .value => object []

/-- Each field's name and schema. -/
def schemaFields (p : Plan) : List (String × Shape) → List (String × String)
  | [] => []
  | (name, s) :: rest => (name, schemaIn p s) :: schemaFields p rest

/-- One branch per case with a field, its `_tag` the case's name; the sum's object says it is an
object, and its cases with no field share one branch. -/
def schemaCases (p : Plan) : List (String × Nat × List (String × Shape)) → List String
  | [] => []
  | (_, _, []) :: rest => schemaCases p rest
  | (name, _, fields@(_ :: _)) :: rest =>
    object (exactly (("_tag", tagOf [name]) :: schemaFields p fields)) :: schemaCases p rest
end

/-- **A shape's own schema** where its name is shared: its definition under `$defs`. -/
def spell (p : Plan) (name : String) (s : Shape) : String :=
  schemaIn { p with shared := p.shared.erase name } s

/-! ## What a schema defines -/

mutual
/-- The definitions a shape names, outside the sums whose cases are tools. -/
def namesIn (tools : List String) : Shape → List String
  | .list s | .option s => namesIn tools s
  | .pair a b => namesIn tools a ++ namesIn tools b
  | .struct _ fields => namesFields tools fields
  | .sum name cases => if tools.contains name then [] else namesCases tools cases
  | .named name => [name]
  | _ => []

/-- The definitions a list of fields names. -/
def namesFields (tools : List String) : List (String × Shape) → List String
  | [] => []
  | (_, s) :: rest => namesIn tools s ++ namesFields tools rest

/-- The definitions a list of cases names. -/
def namesCases (tools : List String) : List (String × Nat × List (String × Shape)) → List String
  | [] => []
  | (_, _, fields) :: rest => namesFields tools fields ++ namesCases tools rest
end

mutual
/-- **The structures and sums directly under a shape**, each with its name: a structure or a sum
is itself one, and what its fields hold is under it, not here. -/
def under : Shape → List (String × Shape)
  | .list s | .option s => under s
  | .pair a b => under a ++ under b
  | .struct name fields => [(name, .struct name fields)]
  | .sum name cases => [(name, .sum name cases)]
  | _ => []

/-- The structures and sums directly under a list of fields. -/
def underFields : List (String × Shape) → List (String × Shape)
  | [] => []
  | (_, s) :: rest => under s ++ underFields rest

/-- The structures and sums directly under a list of cases. -/
def underCases : List (String × Nat × List (String × Shape)) → List (String × Shape)
  | [] => []
  | (_, _, fields) :: rest => underFields fields ++ underCases rest
end

/-- The structures and sums directly under a structure's fields or a sum's cases; none under a sum
whose cases are tools, which a schema does not open. -/
def inside (tools : List String) : Shape → List (String × Shape)
  | .struct _ fields => underFields fields
  | .sum name cases => if tools.contains name then [] else underCases cases
  | s => under s

mutual
/-- **Every structure and sum in a shape**, at any depth, outside the sums whose cases are tools. -/
def nested (tools : List String) : Shape → List (String × Shape)
  | .list s | .option s => nested tools s
  | .pair a b => nested tools a ++ nested tools b
  | .struct name fields => (name, .struct name fields) :: nestedFields tools fields
  | .sum name cases =>
    (name, .sum name cases) :: if tools.contains name then [] else nestedCases tools cases
  | _ => []

/-- Every structure and sum in a list of fields. -/
def nestedFields (tools : List String) : List (String × Shape) → List (String × Shape)
  | [] => []
  | (_, s) :: rest => nested tools s ++ nestedFields tools rest

/-- Every structure and sum in a list of cases. -/
def nestedCases (tools : List String) : List (String × Nat × List (String × Shape)) → List (String × Shape)
  | [] => []
  | (_, _, fields) :: rest => nestedFields tools fields ++ nestedCases tools rest
end

/-- **The definitions reachable from some names**, each once, following what `follow` says each
definition names: one more round for each definition the table holds, which is enough to close
it. -/
def reachable (defs : List (String × Shape)) (follow : Shape → List String) (start : List String) :
    List String :=
  go (defs.length + 1) start.eraseDups
where
  go : Nat → List String → List String
    | 0, found => found
    | fuel + 1, found =>
      let next := (found ++ found.flatMap fun n => ((defs.lookup n).map follow).getD []).eraseDups
      if next.length = found.length then found else go fuel next

/-- **Whether a table definition is left to `describe`**: one a schema writes as an object, a
structure or a sum with a field that is no list family. A list family or a scalar is spelled where
it is named; it costs less than a pointer. -/
def onDemand : Shape → Bool
  | .struct .. => true
  | .sum _ cases => !allNullary cases && (listItem? cases).isNone
  | _ => false

/-- **The definitions of a schema of some fields**, and the plan the fields are written by:

- every table definition the fields reach, spelled, or, when `lazy`, a pointer to `describe` where
  the definition is an object (`onDemand`), whose own reach the schema then leaves out;
- every structure or sum written in more than one place: each is spelled once, a structure or sum
  under it counting once whatever its holder's count, so one written in one place stays there.

(Each list built here holds pairs: the OCaml route types the one empty array a function starts its
lists from at a single item type.) -/
def definitionsOf (defs : List (String × Shape)) (tools : List String) (lazy : Bool)
    (fields : List (String × Shape)) : Plan × List (String × String) :=
  let left (s : Shape) := lazy && onDemand s
  let table := (reachable defs (fun s => if left s then [] else namesIn tools s)
    (namesFields tools fields)).filterMap fun n => (defs.lookup n).map ((n, ·))
  let met := nestedFields tools fields ++
    (table.filter fun d => !left d.2).flatMap fun d => nested tools d.2
  let distinct := (met.map (·.1)).eraseDups.filterMap fun n => (met.lookup n).map ((n, ·))
  let places := (underFields fields ++ distinct.flatMap fun d => inside tools d.2).map (·.1)
  let shared := (distinct.filter fun d => (places.filter (· == d.1)).length ≥ 2).map (·.1)
  let plan : Plan := { shared, tools }
  (plan, table.map (fun (n, s) =>
      (n, if left s then object [("type", quote "object"), ("description", quote onDemandText)]
        else spell plan n s)) ++
    (distinct.filter fun d => shared.contains d.1).map fun (n, s) => (n, spell plan n s))

/-- **A method's argument schema**: an object of its case's fields, with what they define under
`$defs`. -/
def argumentSchema (defs : List (String × Shape)) (tools : List String)
    (fields : List (String × Shape)) : String :=
  let (plan, ds) := definitionsOf defs tools true fields
  object (("type", quote "object") :: exactly (schemaFields plan fields) ++
    (if ds.isEmpty then [] else [("$defs", object ds)]))

/-- **A table definition's schema document**: a pointer to it, with everything it reaches spelled
under `$defs`. -/
def definitionSchema (defs : List (String × Shape)) (name : String) : String :=
  object [("$ref", quote ("#/$defs/" ++ name)),
    ("$defs", object (definitionsOf defs [] false [(name, .named name)]).2)]

/-- **The request's groups of methods**: each case of `Request` that holds one sum (`act` an
`Action`, `ask` a `Query`), with its field, the sum's name and its cases. -/
def groups : List (String × String × String × List (String × Nat × List (String × Shape))) :=
  let doc := shape Request
  match headShape doc.defs doc.root with
  | .sum _ kinds => kinds.filterMap fun (kind, _, fields) =>
    match fields with
    | [(field, sub)] =>
      match headShape doc.defs sub with
      | .sum name cases => some (kind, field, name, cases)
      | _ => none
    | _ => none
  | _ => []

/-- **The tool table**: one entry per case of each group's sum, in case order. A sum a group holds
is a call of one of its methods wherever an argument holds it (`dry`'s action). -/
def entries : List Entry :=
  let tools := groups.map fun (_, _, name, _) => name
  groups.flatMap fun (kind, field, _, cases) => cases.map fun (caseName, _, args) =>
    let (name, description) := (descriptions.lookup caseName).getD (caseName, "")
    ⟨name, description, kind, field, caseName, argumentSchema (shape Request).defs tools args⟩

/-- **The `describe` tool**: the schema of each table definition the methods' schemas leave to it
(`onDemand`). It is no method of the protocol: the server answers a call from `answers`, one schema
document per definition, in the table's order. -/
structure Describe where
  name : String
  description : String
  schema : String
  answers : List (String × String)

/-- The `describe` tool at the request's shape document. -/
def describe : Describe :=
  let defs := (shape Request).defs
  let names := (defs.map (·.1)).eraseDups.filter fun n => ((defs.lookup n).map onDemand).getD false
  { name := "describe"
    description := describeText
    schema := objectSchema [("name", object [("enum", array (names.map quote))])]
    answers := names.map fun n => (n, definitionSchema defs n) }

end Effect4.Tool.Methods
