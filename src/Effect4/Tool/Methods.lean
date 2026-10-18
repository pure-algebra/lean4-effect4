import Effect4.Tool.ToolDerived

/-!
# Tool.Methods — the tool's methods, as an agent's tool table

An agent drives the tool through a tool table: one entry per method, with what the method does,
the JSON Schema of its arguments and of its result, and its behaviour hints (an MCP server's
`tools/list`). The table's one owner is the method descriptor (`methodDescriptor`), a function of
the method key (`MethodKey`, read off the cases of `Action` and `Query`, `Tool/Protocol.lean`), so
nothing names a request by hand:

- each key is one method, in the keys' order, the actions first;
- its name, kind and versions are the key's, the same ones `Request.method` and `supportedMethods`
  read (`method_name_agrees`, `supportedMethods_descriptors`, `Laws/Tool/Wire.lean`);
- its arguments are its case's fields in the request's shape document (`shape Request`), found by
  the case's name (`caseOf_isSome`), and their schema is `schemaIn` of each field's shape, with
  the definitions they reach (`definitionsOf`) under `$defs`;
- its result is the reply in its envelope (`Wire.Envelope Reply`), the structured content of every
  call, and its schema is closed: every definition it reaches is spelled under its own `$defs`;
- what it does and its hints are exhaustive functions of the key (`MethodKey.description`,
  `MethodKey.hints`): a new case is no method until both name it;
- `readOnly` is the query classification's, the law behind it `hinted_readOnly`
  (`Laws/Tool/Serve.lean`).

`describe` is the one tool that is no method: it has its own listing, with the schemas of its
arguments and of its result, and its hints.

`schemaIn` reads a shape as the tools print it (`Canonical.printArrays`, `CodecProfile`): a
structure is an object of its fields; a sum is a string when no case has a field, an array when it
is a list family (`listItem?`), and otherwise an object whose `_tag` names the case, the cases
with no field sharing one branch; a list is an array; an option is `null` or its item; a pair is a
two-element array; a natural is an integer up to `CodecProfile.natLimit`; bytes and digests are
lower-case hex. Every object refuses extra properties, as the exact reader does.

The table is what an agent pays for on every connection, so each argument schema says a thing
once:

- a structure or a sum met in more than one place is written once under `$defs`, by its name;
- the shape document's table (the program's grammar: programs, types, terms, values, all
  recursive) is spelled by the `describe` tool, one schema document per definition, and a method's
  schema names each such definition it reaches with a pointer to `describe` (`onDemand`);
- `dry`'s action is one of the action tools' calls, so its schema names their cases and leaves
  their arguments to their own schemas.

So a method's argument schema is exact up to those names: with each `describe` answer put in
place of its pointer, and each action tool's schema in place of `dry`'s case, it accepts what the
exact reader accepts. A result schema names nothing outside itself: MCP reads it alone, to check a
call's structured content.

The schema is built as text, not as `Effect4.Json`: the native shell reads this table through the
generated code, where a binary64 number does not lower exactly. Nothing here traverses a string
(a character walk neither lowers nor stays inside the axiom ceiling): a JSON string is its text
between quotes, so every name and description must need no escape, which the controls check.
-/

set_option autoImplicit false

namespace Effect4.Tool

open Effect4.Store

/-! ## What each method does, and its hints -/

/-- **What each method does**, for an agent. Exhaustive over the keys: a case with no description
is no method, and the build fails at its key, with no empty fallback. -/
def MethodKey.description : MethodKey → String
  | .open_ => "Open a document: a program with holes (the sketch: the program and its hole table) at \
an application (its host rows, services and types), under a name. It replaces the open document \
and drops pending fills. Answers the document's view: its snapshot, the program's type or the \
located refusals of Lean's checker, every hole occurrence with its address and typed focus, and \
every declared hole with the exact program that performs it (with n application rows, hole k is \
external row n + k) and whether the program performs it."
  | .edit => "Apply one document action at the snapshot you read (`at_`): a commit of several \
changes under one feed policy, one draft edit, or the revert of an accepted entry. A moved \
document refuses `stale` and changes nothing. A refused change names its item and its reason, \
located at the program's own address; a kept-exact commit at a document whose root does not type \
refuses `rootRefused`, and a draft edit repairs it. Answers the new view and a receipt of what \
each change did."
  | .fill => "Add pending fills at a snapshot: each item puts a program at an address, and each is \
certified alone against the snapshot's typed source (kept exact). Answers one outcome per item: \
applied, already there, or refused with its reason, a refused certification with the feed's own \
refusal at the program's address. Nothing changes the document until `publish`."
  | .publish => "Publish the pending fills as one commit at the snapshot they were certified at. \
Refuses when no fill is pending or the document moved since."
  | .reset => "Drop the pending fills. Answers the fillings it dropped."
  | .start => "Admit the document's program at its application and start a live run on the \
machine, under a budget. A program that does not type is refused with the checker's refusal at \
its address. Answers the run's id, where it came from, and the run's view: its state, outcome, \
the host calls it waits on, and its internal waits."
  | .restore => "Restore a saved run record (from `run` with form `record`): it reruns admission \
and replays the record's journal, so the restored run is the saved one. Answers the new run id \
and its view."
  | .play => "Feed host events to a run in order: control decisions, holding a call, receiving \
and applying a reply. An event whose call selector does not resolve refuses the whole list and \
changes nothing. Answers each event's verdict and the run's view."
  | .doc => "Read the document's view: its type or its located refusals, its hole occurrences, \
and every declared hole with its exact `perform` program; with an address, also inspect it: the \
sub-program there, its signature context, its typed focus, its table entry and any refusal there."
  | .history => "Read the document's accepted actions, oldest first."
  | .fills => "Read the pending fills and the snapshot they are anchored at."
  | .suggest => "Suggest programs for a place (a hole by index, or an address with the program \
expected there): your supplied candidates, the variables in scope, unit requests of the rows and \
typed sub-programs elsewhere, each checked at the place as a fill would be, with its evidence \
(fits exactly, type mismatch, refused at its address, another scope). The place's own program \
and the programs that enclose the place are not offered. Paged by cursor and limit; the answer \
gives the next cursor."
  | .run => "Read a run (by id) in one form: its view, its saved record (for `restore`), or its \
ordered journal."
  | .preview => "Run the document's program in the call tree, without starting a run: settle it \
under a reply tape at the least budget that does not cut it, answer its runs at every budget up \
to a limit (frames), or explore its paths with replies drawn from the rows' types."
  | .dry => "Answer an action as if it were applied, and change nothing."
  | .discover => "List the supported methods and their versions."
  | .table => "Read the program's whole address table: for every address, the typing environment \
there and, at a program, Lean's checker answer."
  | .addresses => "List every address of the program as written, in the table's order."
  | .slots => "Read the term slots of the node at an address (one named slot, or every slot): \
each slot's term, the environment it reads and its type there."

/-- **A method's behaviour hints beside `readOnly`**, as an MCP client reads them (2025-06-18
`ToolAnnotations`). Each is set by hand for each method, never inferred from the query
classification, and no law states them. Their environment is the tool's state: the open document,
its pending fills and the runs. -/
structure MethodHints where
  /-- the method may discard what the state held: `open` replaces the document and drops the
  pending fills, and `reset` drops them. An edit is no discard: the history keeps it, and a revert
  undoes it -/
  destructive : Bool
  /-- a second call with the same arguments changes nothing more: a change at a snapshot refuses
  `stale` the second time, a fill already pending collapses, a second `reset` finds nothing to
  drop, and a query changes nothing; `open`, `start`, `restore` and `play` act again -/
  idempotent : Bool
  /-- the method reaches outside the tool's state: none does, as a host's events and replies
  arrive as the arguments of `play` -/
  openWorld : Bool

/-- **Each method's hints**. Exhaustive over the keys: a case with no hints is no method. -/
def MethodKey.hints : MethodKey → MethodHints
  | .open_ => ⟨true, false, false⟩
  | .edit => ⟨false, true, false⟩
  | .fill => ⟨false, true, false⟩
  | .publish => ⟨false, true, false⟩
  | .reset => ⟨true, true, false⟩
  | .start => ⟨false, false, false⟩
  | .restore => ⟨false, false, false⟩
  | .play => ⟨false, false, false⟩
  | .doc | .history | .fills | .suggest | .run | .preview | .dry | .discover | .table
  | .addresses | .slots => ⟨false, true, false⟩

namespace Methods

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

/-- **The schema of an object of some fields**, with the definitions they reach under `$defs`.
`lazy` leaves each table definition written as an object to `describe` (a method's arguments);
otherwise the schema is closed, every definition spelled (a method's result). -/
def fieldsSchema (defs : List (String × Shape)) (tools : List String) (lazy : Bool)
    (fields : List (String × Shape)) : String :=
  let (plan, ds) := definitionsOf defs tools lazy fields
  object (("type", quote "object") :: exactly (schemaFields plan fields) ++
    (if ds.isEmpty then [] else [("$defs", object ds)]))

/-- **The schema of a shape document** whose value is a JSON object: a structure's object of
fields (`fieldsSchema`), or any other root under `allOf`, beside its definitions. -/
def docSchema (tools : List String) (lazy : Bool) (doc : ShapeDoc) : String :=
  match headShape doc.defs doc.root with
  | .struct _ fields => fieldsSchema doc.defs tools lazy fields
  | root =>
    let (plan, ds) := definitionsOf doc.defs tools lazy [("", root)]
    object ([("type", quote "object"), ("allOf", array [schemaIn plan root])] ++
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

/-- **A method's case in the request's shape document**: the case of `Request` that holds it, that
case's field, and the method's argument fields, found by the key's case name. -/
def caseOf (k : MethodKey) : Option (String × String × List (String × Shape)) :=
  groups.findSome? fun (kind, field, _, cases) =>
    (cases.find? fun c => c.1 == k.caseName).map fun c => (kind, field, c.2.2)

/-- **Every key finds its case**: the derived shape document and the keys are both read off the
constructors of `Action` and `Query`, and the kernel decides the lookup for each key. -/
theorem caseOf_isSome (k : MethodKey) : (caseOf k).isSome = true := by
  cases k <;> decide

/-- A method's case, found (`caseOf_isSome`). -/
def caseFor (k : MethodKey) : String × String × List (String × Shape) :=
  (caseOf k).get (caseOf_isSome k)

end Methods

/-! ## The method table -/

/-- **One method's descriptor**: its wire name, its kind, its versions, the shapes of its arguments
and of its result, what it does, whether it changes no state, and its hints. -/
structure MethodDescriptor where
  name : String
  kind : MethodKind
  versions : List Nat
  /-- the arguments: an object of the case's fields, over the request's definitions -/
  arguments : ShapeDoc
  /-- what every call answers: the reply in its envelope -/
  result : ShapeDoc
  description : String
  readOnly : Bool
  hints : MethodHints

/-- **The method table's one owner**: a key's descriptor. A method is read-only exactly when it is
a query (`query_hint`, `hinted_readOnly`, `Laws/Tool/Serve.lean`). -/
def methodDescriptor (k : MethodKey) : MethodDescriptor :=
  { name := k.name, kind := k.kind, versions := k.versions,
    arguments := ⟨.struct k.caseName (Methods.caseFor k).2.2, (shape Request).defs⟩,
    result := shape (Wire.Envelope Reply),
    description := k.description, readOnly := k.kind == .query, hints := k.hints }

namespace Methods

/-- **One tool as `tools/list` shows it**: its name, what it does, the JSON Schema of its arguments
and of its result, as JSON text, and its four behaviour hints. -/
structure Listing where
  name : String
  description : String
  inputSchema : String
  outputSchema : String
  readOnly : Bool
  destructive : Bool
  idempotent : Bool
  openWorld : Bool

/-- **One method as an agent calls it**: its listing, and the request it builds: the case of
`Request` (`kind`), holding its argument object under `field`, and the `Action` or `Query` case it
names. -/
structure Entry where
  listing : Listing
  kind : String
  field : String
  caseName : String

/-- **What every method answers**: the closed schema of the reply in its envelope, the structured
content of a call (`eff mcp`), rendered once for the table. -/
def replySchema : String := docSchema [] false (shape (Wire.Envelope Reply))

/-- **The listing of a descriptor**: its arguments' schema leaves the table's object definitions
to `describe` and each sum of `tools` to its tools' own schemas. Its result's closed schema is
`output`, which the table renders once: every method answers one envelope
(`listing_outputSchema`, `Laws/Tool/Wire.lean`). -/
def listingOf (tools : List String) (output : String) (d : MethodDescriptor) : Listing :=
  { name := d.name, description := d.description,
    inputSchema := docSchema tools true d.arguments, outputSchema := output,
    readOnly := d.readOnly, destructive := d.hints.destructive,
    idempotent := d.hints.idempotent, openWorld := d.hints.openWorld }

/-- The tool table at the sums whose cases are tools and the reply's schema, each read once. -/
def entriesAt (tools : List String) (output : String) : List Entry :=
  MethodKey.all.map fun k =>
    let (kind, field, _) := caseFor k
    ⟨listingOf tools output (methodDescriptor k), kind, field, k.caseName⟩

/-- **The tool table**: one entry per method key, in the keys' order, each its descriptor's
listing, with the request it builds. A sum a group holds is a call of one of its methods wherever
an argument holds it (`dry`'s action). -/
def entries : List Entry :=
  entriesAt (groups.map fun (_, _, name, _) => name) replySchema

/-- **The `describe` tool**: the schema of each table definition the methods' schemas leave to it
(`onDemand`). It is no method of the protocol: the server answers a call from `answers`, one schema
document per definition, in the table's order. -/
structure Describe where
  listing : Listing
  answers : List (String × String)

/-- The `describe` tool at the request's shape document. Its answer is one schema document, a
pointer and its definitions. It reads the table and changes nothing: read-only, idempotent and
closed-world. -/
def describe : Describe :=
  let defs := (shape Request).defs
  let names := (defs.map (·.1)).eraseDups.filter fun n => ((defs.lookup n).map onDemand).getD false
  { listing :=
      { name := "describe", description := describeText,
        inputSchema := objectSchema [("name", object [("enum", array (names.map quote))])],
        outputSchema := objectSchema [("$ref", object [("type", quote "string")]),
          ("$defs", object [("type", quote "object")])],
        readOnly := true, destructive := false, idempotent := true, openWorld := false }
    answers := names.map fun n => (n, definitionSchema defs n) }

end Methods

end Effect4.Tool
