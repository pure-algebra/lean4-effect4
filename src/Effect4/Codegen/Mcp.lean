import Effect4.Surface.Agent
import Effect4.Codegen.JsonSchema

/-!
# Surface.Agent.Emit: the toolkit module and the MCP list payloads

Implements the projections of `docs/research/2026-09-04-surface-library-plan.md`
§4.5, and the `ofMcpToolsList` row of §4.8. Two rules of the census
(`Effect4/Surface/Emit.lean`) live here and every definition that is one carries
its tag:

| rule | id | what it emits |
| --- | --- | --- |
| `Rule.mcpToolkit` | `surface.mcp.toolkit` | the rc.112 toolkit module |
| `Rule.mcpToolsList` | `surface.mcp.toolsList` | the `tools/list`, `resources/list` and `prompts/list` payloads |

Both are `emitted`, not `modeled`: no host receipt has landed, and
`Rule.modeled_has_receipt` keeps the stance honest.

## The spellings, pinned

Paths are relative to `node_modules/effect/src` at `effect` 4.0.0-rc.112.

| emitted | pin |
| --- | --- |
| `Tool.make("<name>", { description, parameters, success, failure })` | `unstable/ai/Tool.ts:1204-1246` (the options record, in this key order) |
| `Toolkit.make(<tool>, ...)` | `unstable/ai/Toolkit.ts:496-498` (variadic) |
| `McpServer.toolkit(<toolkit>)` | `unstable/ai/McpServer.ts:1609-1612` |
| `McpServer.resource({ uri, name, description, mimeType, content })` | `unstable/ai/McpServer.ts:1894-1909` (the plain, non-template overload) |
| `McpServer.prompt({ name, description, parameters, content })` | `unstable/ai/McpServer.ts:2106-2126` |
| `{ tools: [{ name, description, inputSchema }] }` | `unstable/ai/McpSchema.ts:1559-1596` (`Tool`), `:1604-1610` (`ListToolsResult`) |
| `{ resources: [{ uri, name, description, mimeType }] }` | `unstable/ai/McpSchema.ts:875-916` (`Resource`), `:1031-1037` (`ListResourcesResult`) |
| `{ prompts: [{ name, description, arguments: [{ name, required }] }] }` | `unstable/ai/McpSchema.ts:1218-1239` (`Prompt`), `:1196-1210` (`PromptArgument`), `:1382-1388` (`ListPromptsResult`) |
| `inputSchema` = the parameters' JSON Schema, with `$defs` when it has definitions | `unstable/ai/Tool.ts:1719-1744` (`getJsonSchemaFromSchema` into `getJsonSchemaFromSchemaWith`) |

Every emitted key is a *required* or a *present optional* field of the cited
class, and no key is emitted that the class does not declare. An optional field
the carrier does not have is left out rather than emitted as `null`, which is
what `Schema.optional` reads (`McpSchema.ts:1561`, `:1570`, and so on).

| | |
| --- | --- |
| Carrier | none of its own; `TypeScript.Module` is the target package's and `Json` is the estate's |
| Operations | `toolkitModule`, `toolsListJson`, `resourcesListJson`, `promptsListJson`, `ofMcpToolsList` |
| Laws | none proved. The round trip is a `#guard` on the fixture, up to the quotient named below, and the host receipt is owed |
| Structure | four partial functions out of one carrier, plus one partial function back on the `tools/list` fragment |
| Payoff | the toolkit module, the three list payloads and the ingest all read one carrier, so a description cannot differ between the module and the wire |
| Anti-vacuity | the `#guard`s at the end: the three payloads on the fixture, the rendered module lines, the round trip, and one refusal each |
| Generation | this module *is* generation; nothing generates it |

## The quotient the round trip is up to

`toolsListJson` then `ofMcpToolsList` is **not** the identity on `Tool`, and
the drop is named here the way `Effect4/Surface/JsonSchema.lean` names its own:

* `success` and `failure` are not on the `tools/list` wire in the fragment
  emitted here, so the decoded tool carries `success := Schema.unknown` and
  `failure := none`;
* the only annotations the decoded tool carries are `identifier`, set to the
  tool name, and `description`, when the wire has one. Every other entry of the
  original bag is gone;
* `parameters` survives exactly, because `toJsonSchema` and `ofJsonSchema`
  agree on an annotation-free struct of admitted property types. A parameter
  object whose nodes carry `description` or `title` is emitted with those
  keywords and then **refused** on the way back, because §4.3's ingest fragment
  admits no annotation keyword; lifting that is `JsonSchema.lean`'s row, not
  this one.

So the `#guard` below compares `(name, parameters.rep, descriptionOf)`, which
is exactly the part of a tool the fragment carries both ways.

## The refusals, by name

* a tool whose name is not a legal generated binding (`get-user` is a legal MCP
  name and not a legal TypeScript identifier): the module refuses rather than
  inventing a mangling, because a mangled constant is a second spelling of the
  tool's identity;
* a server, resource or prompt name that is not a legal binding, for the same
  reason;
* a server that is not `McpServer.WellFormed`;
* a schema `Effect4/Surface/Spell.lean` refuses, or that `toJsonSchema` refuses;
* on ingest: a payload that is not `{ tools: [...] }`, an entry that is not an
  object, a missing or non-string `name`, a missing `inputSchema`, an
  `inputSchema` outside §4.3's fragment (including one carrying `$defs`), and an
  `inputSchema` that is not `Kind.struct` under the table.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
open TypeScript (Expr)

/-! ## Reachable definitions

`getJsonSchemaFromSchemaWith` (`unstable/ai/Tool.ts:1725-1744`) compiles the
parameters to a document and, when that document has definitions, hangs them on
the root as `$defs`. rc.112's document collects a definition only for a
reference it actually meets, so the definitions emitted here are the references
reachable from the parameters, not the whole domain.
-/

/-- The reference keys occurring syntactically in a representation, in
document order, fuel-bounded. References are not followed, so this terminates
on a cyclic table. -/
def referenceKeys : Nat → Representation → List String
  | 0, _ => []
  | fuel + 1, representation =>
    match representation with
    | .reference key => [key.value]
    | .declaration _ _ typeParameters _ => typeParameters.flatMap (referenceKeys fuel)
    | .suspend _ _ thunk => referenceKeys fuel thunk
    | .templateLiteral _ _ parts => parts.flatMap (referenceKeys fuel)
    | .arrays _ _ elements rest =>
      elements.flatMap (fun element => referenceKeys fuel element.type) ++
        rest.flatMap (referenceKeys fuel)
    | .objects _ _ properties indexes =>
      properties.flatMap (fun property => referenceKeys fuel property.type) ++
        indexes.flatMap (fun index =>
          referenceKeys fuel index.parameter ++ referenceKeys fuel index.type)
    | .union _ _ types _ => types.flatMap (referenceKeys fuel)
    | _ => []

/-- Drop repeats, keeping the first occurrence of each name. -/
def dedupeNames (seen : List String) : List String → List String
  | [] => []
  | first :: rest =>
    if seen.contains first then dedupeNames seen rest
    else first :: dedupeNames (seen ++ [first]) rest

/-- One step of the reachability closure: every key already present, plus every
key its entry mentions. -/
def growKeys (refs : List ReferenceEntry) (keys : List String) : List String :=
  keys.foldl
    (fun acc key =>
      match refs.find? (·.key == key) with
      | some entry =>
        acc ++ (referenceKeys 64 entry.representation).filter fun found => !acc.contains found
      | none => acc)
    keys

/-- The closure of `growKeys`, run once per table entry, which is enough
because each round adds at least one key or none at all. -/
def closeKeys (refs : List ReferenceEntry) : Nat → List String → List String
  | 0, keys => keys
  | fuel + 1, keys =>
    let grown := growKeys refs keys
    if grown.length == keys.length then keys else closeKeys refs fuel grown

/-- Every reference key reachable from a representation under a table, in the
order they were first met. -/
def reachableKeys (refs : List ReferenceEntry) (representation : Representation) :
    List String :=
  closeKeys refs refs.length (dedupeNames [] (referenceKeys 64 representation))

/-- The `$defs` entries for a representation: the reachable definitions, in the
table's own order, each compiled by §4.3. `none` when one of them is outside
that fragment. -/
def reachableDefinitions (refs : List ReferenceEntry) (representation : Representation) :
    Option (List (String × Json)) :=
  let wanted := reachableKeys refs representation
  compile (refs.filter fun entry => wanted.contains entry.key)
where
  /-- Compile a table slice, refusing as soon as one entry refuses. -/
  compile : List ReferenceEntry → Option (List (String × Json))
    | [] => some []
    | entry :: rest =>
      match toJsonSchema refs entry.representation, compile rest with
      | some compiled, some tail => some ((entry.key, compiled) :: tail)
      | _, _ => none

/-! ## The list payloads -/

/-- Collect a list of options, refusing as soon as one refuses. -/
def optionList {A : Type} : List (Option A) → Option (List A)
  | [] => some []
  | first :: rest =>
    match first, optionList rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/--
The `inputSchema` of one tool: the parameters' JSON Schema, with the reachable
definitions hung on the root as `$defs` when there are any.

Pin: `unstable/ai/Tool.ts:1725-1744`.

surface: rule.surface.mcp.toolsList -/
def toolInputSchema {refs : List ReferenceEntry} (tool : Tool refs) : Option Json :=
  match toJsonSchema refs tool.parameters.rep with
  | none => none
  | some root =>
    match reachableDefinitions refs tool.parameters.rep with
    | none => none
    | some [] => some root
    | some definitions =>
      match root with
      | .obj fields => some (.obj (objSet fields "$defs" (.obj definitions)))
      | other => some other

/-- One entry of `tools/list`: `name`, `description` when the tool has one, and
`inputSchema`, in `McpSchema.Tool`'s own field order (`:1559-1596`).

surface: rule.surface.mcp.toolsList -/
def toolListEntry {refs : List ReferenceEntry} (tool : Tool refs) : Option Json :=
  match toolInputSchema tool with
  | none => none
  | some inputSchema =>
    some (.obj
      ([("name", .str tool.name)] ++
        (match tool.descriptionOf with
          | some text => [("description", .str text)]
          | none => []) ++
        [("inputSchema", inputSchema)]))

/--
The `tools/list` result payload (`unstable/ai/McpSchema.ts:1604-1610`).

`none` when one tool's parameters fall outside §4.3's fragment.

surface: rule.surface.mcp.toolsList -/
def toolsListJson (dom : Domain) (server : McpServer dom.refs) : Option Json :=
  (optionList (server.tools.map toolListEntry)).map fun entries =>
    .obj [("tools", .arr entries)]

/--
The `resources/list` result payload (`unstable/ai/McpSchema.ts:1031-1037`),
whose entries are `McpSchema.Resource`'s `uri`, `name`, `description` and
`mimeType` in that order (`:875-916`).

Total, unlike `toolsListJson`: no field of a resource is compiled, so nothing
can fall outside a fragment.

surface: rule.surface.mcp.toolsList -/
def resourcesListJson (dom : Domain) (server : McpServer dom.refs) : Json :=
  .obj
    [("resources", .arr (server.resources.map fun resource =>
      .obj
        ([("uri", .str resource.uri), ("name", .str resource.name)] ++
          (match resource.descriptionOf with
            | some text => [("description", .str text)]
            | none => []) ++
          (match resource.mimeType with
            | some text => [("mimeType", .str text)]
            | none => []))))]

/--
The `prompts/list` result payload (`unstable/ai/McpSchema.ts:1382-1388`), whose
entries are `McpSchema.Prompt`'s `name`, `description` and `arguments`
(`:1218-1239`), each argument being `McpSchema.PromptArgument`'s `name` and
`required` (`:1196-1210`).

surface: rule.surface.mcp.toolsList -/
def promptsListJson (dom : Domain) (server : McpServer dom.refs) : Json :=
  .obj
    [("prompts", .arr (server.prompts.map fun prompt =>
      .obj
        ([("name", .str prompt.name)] ++
          (match prompt.descriptionOf with
            | some text => [("description", .str text)]
            | none => []) ++
          [("arguments", .arr (prompt.arguments.map fun argument =>
            .obj [("name", .str argument.1), ("required", .bool argument.2)]))])))]

/-! ## The toolkit module -/

/--
Qualify an entity constant with the namespace the generated module imports it
under.

`Effect4/Surface/Spell.lean` spells a `reference` as the bare identifier of the
entity, because it does not know how the referring module names the entity
module. Here it is `import * as Entities from "./entities.generated"`, so every
bare identifier that is a key of the table becomes `Entities.<Name>`. The walk
covers exactly the `Expr` formers `spell` produces; anything else is returned
unchanged.
-/
def qualifyEntities (refs : List ReferenceEntry) (namespaceName : String) :
    Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    match expression with
    | .ident name =>
      if (refs.find? (·.key == name)).isSome then .ident (namespaceName ++ "." ++ name)
      else .ident name
    | .call callee arguments =>
      .call (qualifyEntities refs namespaceName fuel callee)
        (arguments.map (qualifyEntities refs namespaceName fuel))
    | .method target name arguments =>
      .method (qualifyEntities refs namespaceName fuel target) name
        (arguments.map (qualifyEntities refs namespaceName fuel))
    | .arr items => .arr (items.map (qualifyEntities refs namespaceName fuel))
    | .objectQuoted fields =>
      .objectQuoted (fields.map fun field =>
        (field.1, qualifyEntities refs namespaceName fuel field.2))
    | other => other

/-- The constructor spelling of a schema as this module writes it: `spell`, with
entity references qualified. -/
def spellQualified (refs : List ReferenceEntry) (representation : Representation) :
    Option Expr :=
  (spell refs representation).map (qualifyEntities refs "Entities" 64)

/-- Whether a slot spells as a bare entity constant, and therefore needs no
`Schema.` former. -/
def isBareReference : Representation → Bool
  | .reference _ => true
  | _ => false

/-- Every representation the module spells, in emission order. -/
def schemaSlots {refs : List ReferenceEntry} (server : McpServer refs) :
    List Representation :=
  server.tools.flatMap fun tool =>
    [tool.parameters.rep, tool.success.rep] ++
      (match tool.failure with | some schema => [schema.rep] | none => [])

/-- One tool's declaration. `none` when the tool name is not a legal binding or
one of its schemas has no constructor spelling.

Pin: `unstable/ai/Tool.ts:1204-1246`. -/
def toolDecl {refs : List ReferenceEntry} (tool : Tool refs) : Option TypeScript.Decl :=
  if !identifier tool.name then none
  else
    match spellQualified refs tool.parameters.rep, spellQualified refs tool.success.rep,
        optionList ((match tool.failure with
          | some schema => [schema.rep]
          | none => []).map (spellQualified refs)) with
    | some parameters, some success, some failures =>
      some (.const
        { doc := []
          name := tool.name
          value :=
            .call (.ident "Tool.make")
              [ .str tool.name
              , .objectML
                  ((match tool.descriptionOf with
                    | some text => [("description", Expr.str text)]
                    | none => []) ++
                    [("parameters", parameters), ("success", success)] ++
                    (failures.map fun failure => ("failure", failure))) ] })
    | _, _, _ => none

/-- One resource's declaration, with a typed stub for its content. `none` when
the resource name is not a legal binding.

Pin: `unstable/ai/McpServer.ts:1894-1909`. The content stub takes the `string`
leg of that overload's content union, which rc.112 turns into a text resource. -/
def resourceDecl (resource : Resource) : Option TypeScript.Decl :=
  if !identifier resource.name then none
  else
    some (.const
      { doc := ["Stub content: replace with this resource's own program."]
        name := resource.name ++ "Resource"
        value :=
          .call (.ident "McpServer.resource")
            [ .objectML
                ([("uri", Expr.str resource.uri), ("name", Expr.str resource.name)] ++
                  (match resource.descriptionOf with
                    | some text => [("description", Expr.str text)]
                    | none => []) ++
                  (match resource.mimeType with
                    | some text => [("mimeType", Expr.str text)]
                    | none => []) ++
                  [("content", .call (.ident "Effect.succeed") [.str ""])]) ] })

/-- One prompt's declaration, with a typed stub for its content. `none` when the
prompt name is not a legal binding.

Pin: `unstable/ai/McpServer.ts:2106-2126`. An argument becomes one field of the
`parameters` record; a required argument is `Schema.String` and an optional one
is `Schema.optionalKey(Schema.String)` (`Schema.ts:2444`), which is the same
optionality `McpSchema.PromptArgument.required` carries on the wire
(`:1196-1210`). -/
def promptDecl (prompt : Prompt) : Option TypeScript.Decl :=
  if !identifier prompt.name then none
  else
    some (.const
      { doc := ["Stub content: replace with this prompt's own program."]
        name := prompt.name ++ "Prompt"
        value :=
          .call (.ident "McpServer.prompt")
            [ .objectML
                ([("name", Expr.str prompt.name)] ++
                  (match prompt.descriptionOf with
                    | some text => [("description", Expr.str text)]
                    | none => []) ++
                  (if prompt.arguments.isEmpty then []
                    else
                      [("parameters", .objectQuoted (prompt.arguments.map fun argument =>
                        (argument.1,
                          if argument.2 then Expr.ident "Schema.String"
                          else .call (.ident "Schema.optionalKey") [.ident "Schema.String"])))]) ++
                  [("content", .lambda ["params"]
                    (.call (.ident "Effect.succeed") [.str ""]))]) ] })

/-- The imports the module actually uses, in a fixed order. -/
def toolkitImports {refs : List ReferenceEntry} (server : McpServer refs) :
    List TypeScript.Import :=
  let usesTool := !server.tools.isEmpty
  let usesMcpServer :=
    !server.tools.isEmpty || !server.resources.isEmpty || !server.prompts.isEmpty
  let usesEffect := !server.resources.isEmpty || !server.prompts.isEmpty
  let usesSchema :=
    (schemaSlots server).any (fun slot => !isBareReference slot) ||
      server.prompts.any fun prompt => !prompt.arguments.isEmpty
  let usesEntities :=
    (schemaSlots server).any fun slot => !(reachableKeys refs slot).isEmpty
  let aiNames :=
    (if usesMcpServer then ["McpServer"] else []) ++
      (if usesTool then ["Tool", "Toolkit"] else [])
  (if usesEffect then [TypeScript.Import.named ["Effect"] "effect"] else []) ++
    (if usesSchema then [TypeScript.Import.all "Schema" "effect/Schema"] else []) ++
    (if aiNames.isEmpty then [] else [TypeScript.Import.named aiNames "effect/unstable/ai"]) ++
    (if usesEntities then [TypeScript.Import.all "Entities" "./entities.generated"] else [])

/--
The rc.112 toolkit module of an agent server.

One `Tool.make` constant per tool, then `Toolkit.make` over them, then
`McpServer.toolkit` of that toolkit, then one `McpServer.resource` and one
`McpServer.prompt` constant per registered value. `none` when the server is not
well-formed, when a name it needs as a binding is not one, or when a schema has
no constructor spelling.

surface: rule.surface.mcp.toolkit -/
def toolkitModule (dom : Domain) (server : McpServer dom.refs) :
    Option TypeScript.Module :=
  if !McpServer.wellFormed server then none
  else if !identifier server.name then none
  else
    match optionList (server.tools.map toolDecl),
        optionList (server.resources.map resourceDecl),
        optionList (server.prompts.map promptDecl) with
    | some toolDecls, some resourceDecls, some promptDecls =>
      some
        { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
          imports := toolkitImports server
          decls :=
            toolDecls ++
              (if server.tools.isEmpty then []
                else
                  [ .const
                      { doc := []
                        name := server.name ++ "Toolkit"
                        value := .call (.ident "Toolkit.make")
                          (server.tools.map fun tool => .ident tool.name) }
                  , .const
                      { doc := []
                        name := server.name ++ "ToolkitLayer"
                        value := .call (.ident "McpServer.toolkit")
                          [.ident (server.name ++ "Toolkit")] } ]) ++
              resourceDecls ++ promptDecls }
    | _, _, _ => none

/-! ## Ingest: `tools/list` back into rows -/

/-- `Schema.unknown` is JSON-representable under every table, which is what the
decoded tool's absent success schema needs. -/
theorem kindCheck_unknown_json (refs : List ReferenceEntry) :
    kindCheck refs 64 .json Schema.unknown = true := rfl

/-- The path a `mcpMalformed` refusal names, for one entry of the array. -/
def toolsPath (index : Nat) (field : String) : String :=
  "tools/" ++ toString index ++ "/" ++ field

/--
Decode one entry of `tools/list`.

The decoded tool carries `identifier` set to its name and `description` when
the wire has one, and nothing else; a wire entry with no description therefore
decodes to a tool that `Tool.check` refuses by `descriptionMissing`, which is
§15.2's "the refusal names the ones it lacks".
-/
def toolOfJson (refs : List ReferenceEntry) (index : Nat) (value : Json) :
    Except Refusal (Tool refs) :=
  match value with
  | .obj fields =>
    match objGet fields "name" with
    | some (.str name) =>
      match objGet fields "inputSchema" with
      | some inputSchema =>
        match ofJsonSchema inputSchema with
        | .error refusal => .error refusal
        | .ok parameters =>
          if h : kindCheck refs 64 .struct parameters = true then
            .ok
              { name := name
                parameters := ⟨parameters, h⟩
                success := ⟨Schema.unknown, kindCheck_unknown_json refs⟩
                failure := none
                annotations :=
                  match objGet fields "description" with
                  | some (.str text) =>
                    descriptionKey.append text (identifierKey.append name none)
                  | _ => identifierKey.append name none }
          else .error (.mcpMalformed (toolsPath index "inputSchema"))
      | none => .error (.mcpMalformed (toolsPath index "inputSchema"))
    | _ => .error (.mcpMalformed (toolsPath index "name"))
  | _ => .error (.mcpMalformed ("tools/" ++ toString index))

/-- Decode the entries of `tools/list`, first refusal wins. -/
def toolsOfJson (refs : List ReferenceEntry) : Nat → List Json →
    Except Refusal (List (Tool refs))
  | _, [] => .ok []
  | index, first :: rest =>
    match toolOfJson refs index first, toolsOfJson refs (index + 1) rest with
    | .ok head, .ok tail => .ok (head :: tail)
    | .error refusal, _ => .error refusal
    | _, .error refusal => .error refusal

/--
Read a `tools/list` payload back as surface rows, on the fragment §4.3 admits.

The wrapping direction of the plan's §4.8: total on the admitted fragment,
refusing the rest by constructor. The quotient it is an inverse up to is named
in this module's header.
-/
def ofMcpToolsList (refs : List ReferenceEntry) (value : Json) :
    Except Refusal (List (Tool refs)) :=
  match value with
  | .obj fields =>
    match objGet fields "tools" with
    | some (.arr entries) => toolsOfJson refs 0 entries
    | _ => .error (.mcpMalformed "tools")
  | _ => .error (.mcpMalformed "tools/list")

/-- The part of a tool the `tools/list` fragment carries in both directions:
its name, its parameter representation and its description. -/
def toolFingerprint {refs : List ReferenceEntry} (tool : Tool refs) :
    String × Representation × Option String :=
  (tool.name, tool.parameters.rep, tool.descriptionOf)

/-! ## Anti-vacuity -/

-- the three list payloads, field for field
#guard toolsListJson shopDomain shopServer ==
  some (.obj
    [("tools", .arr
      [ .obj
          [ ("name", .str "get_user")
          , ("description", .str "Fetch one shop customer by id.")
          , ("inputSchema", .obj
              [ ("type", .str "object")
              , ("properties", .obj [("id", .obj [("type", .str "string")])])
              , ("required", .arr [.str "id"])
              , ("additionalProperties", .bool false) ]) ]
      , .obj
          [ ("name", .str "list_users")
          , ("description", .str "List the shop's customers.")
          , ("inputSchema", .obj
              [ ("type", .str "object")
              , ("properties", .obj [("limit", numberSchema)])
              , ("additionalProperties", .bool false) ]) ] ])])

#guard resourcesListJson shopDomain shopServer ==
  .obj
    [("resources", .arr
      [ .obj
          [ ("uri", .str "shop://users")
          , ("name", .str "users")
          , ("description", .str "Every customer of the shop, as JSON.")
          , ("mimeType", .str "application/json") ] ])]

#guard promptsListJson shopDomain shopServer ==
  .obj
    [("prompts", .arr
      [ .obj
          [ ("name", .str "greet_user")
          , ("description", .str "Greet a customer by name.")
          , ("arguments", .arr
              [ .obj [("name", .str "userId"), ("required", .bool true)]
              , .obj [("name", .str "tone"), ("required", .bool false)] ]) ] ])]

-- an optional field the carrier does not have is left out, not nulled
#guard resourcesListJson shopDomain
    { shopServer with resources := [{ usersResource with mimeType := none }] } ==
  .obj
    [("resources", .arr
      [ .obj
          [ ("uri", .str "shop://users")
          , ("name", .str "users")
          , ("description", .str "Every customer of the shop, as JSON.") ] ])]

-- `$defs` appears exactly when the parameters reach a definition
#guard (toolInputSchema
    { getUserTool with parameters := ⟨Schema.reference "Address", by decide⟩ }).isSome = true
#guard ((toolInputSchema
    { getUserTool with parameters := ⟨Schema.reference "Address", by decide⟩ }).map
  fun schema => match schema with
    | .obj fields => (objGet fields "$defs").isSome
    | _ => false) == some true
#guard ((toolInputSchema getUserTool).map fun schema => match schema with
    | .obj fields => (objGet fields "$defs").isSome
    | _ => false) == some false

-- the module builds, and its first lines are pinned
#guard (toolkitModule shopDomain shopServer).isSome = true
#guard ((toolkitModule shopDomain shopServer).map
    fun target => ((TypeScript.Render.module TypeScript.house0 target).splitOn "\n").take 7) ==
  some
    [ "/**"
    , " * Generated by Effect4 Surface."
    , " *"
    , " * Do not edit."
    , " */"
    , "import { Effect } from \"effect\""
    , "import * as Schema from \"effect/Schema\"" ]

#guard ((toolkitModule shopDomain shopServer).map
    fun target => ((TypeScript.Render.module TypeScript.house0 target).splitOn "\n").drop 7
      |>.take 8) ==
  some
    [ "import { McpServer, Tool, Toolkit } from \"effect/unstable/ai\""
    , "import * as Entities from \"./entities.generated\""
    , ""
    , "export const get_user = Tool.make(\"get_user\", {"
    , "  description: \"Fetch one shop customer by id.\","
    , "  parameters: Schema.Struct({ \"id\": Schema.String }),"
    , "  success: Entities.User,"
    , "  failure: Schema.Struct({ \"message\": Schema.String }),"]

-- the toolkit, its layer, the resource and the prompt
#guard ((toolkitModule shopDomain shopServer).map
    fun target => ((target.decls.drop 2).take 2).map fun declaration =>
      ((TypeScript.Render.decl TypeScript.house0 declaration).splitOn "\n").take 1) ==
  some
    [ ["export const shopToolkit = Toolkit.make(get_user, list_users)"]
    , ["export const shopToolkitLayer = McpServer.toolkit(shopToolkit)"] ]

-- the module's refusals
#guard (toolkitModule shopDomain { shopServer with annotations := none }).isNone = true
#guard (toolkitModule shopDomain
  { shopServer with tools := [{ getUserTool with name := "get-user" }] }).isNone = true
#guard (toolkitModule shopDomain
  { shopServer with resources := [{ usersResource with name := "class" }] }).isNone = true

-- the round trip, up to the quotient named in this module's header
#guard ((toolsListJson shopDomain shopServer).map fun payload =>
    (ofMcpToolsList shopDomain.refs payload).map (List.map toolFingerprint)) ==
  some (.ok
    [ ("get_user", Schema.struct [Schema.property "id" Schema.string],
        some "Fetch one shop customer by id.")
    , ("list_users", Schema.struct [Schema.property "limit" Schema.number true],
        some "List the shop's customers.") ])

-- and the parts the quotient drops
#guard ((toolsListJson shopDomain shopServer).map fun payload =>
    (ofMcpToolsList shopDomain.refs payload).map fun tools =>
      tools.map fun tool => (tool.success.rep, (tool.failure.map Sch.rep).isSome)) ==
  some (.ok [(Schema.unknown, false), (Schema.unknown, false)])

-- a wire tool with no description ingests, and is then refused by name
#guard (ofMcpToolsList shopDomain.refs
    (.obj [("tools", .arr [.obj
      [ ("name", .str "ping")
      , ("inputSchema", .obj
          [ ("type", .str "object")
          , ("properties", .obj [])
          , ("additionalProperties", .bool false) ]) ]])])).map
  (List.map (Tool.check "shop")) ==
  .ok [.error (.descriptionMissing "tool" "ping")]

-- the ingest refusals
#guard (ofMcpToolsList shopDomain.refs (.str "x") :
    Except Refusal (List (Tool shopDomain.refs))).map (List.map toolFingerprint) ==
  .error (.mcpMalformed "tools/list")
#guard (ofMcpToolsList shopDomain.refs (.obj [])).map (List.map toolFingerprint) ==
  .error (.mcpMalformed "tools")
#guard (ofMcpToolsList shopDomain.refs (.obj [("tools", .arr [.str "x"])])).map
  (List.map toolFingerprint) == .error (.mcpMalformed "tools/0")
#guard (ofMcpToolsList shopDomain.refs (.obj [("tools", .arr [.obj []])])).map
  (List.map toolFingerprint) == .error (.mcpMalformed "tools/0/name")
#guard (ofMcpToolsList shopDomain.refs
    (.obj [("tools", .arr [.obj [("name", .str "ping")]])])).map
  (List.map toolFingerprint) == .error (.mcpMalformed "tools/0/inputSchema")
#guard (ofMcpToolsList shopDomain.refs
    (.obj [("tools", .arr [.obj
      [("name", .str "ping"), ("inputSchema", .obj [("type", .str "string")])]])])).map
  (List.map toolFingerprint) == .error (.mcpMalformed "tools/0/inputSchema")
#guard (ofMcpToolsList shopDomain.refs
    (.obj [("tools", .arr [.obj
      [("name", .str "ping"), ("inputSchema", .obj [("type", .str "integer")])]])])).map
  (List.map toolFingerprint) == .error (.jsonSchemaUnsupportedType "integer")

end Effect4.Surface
