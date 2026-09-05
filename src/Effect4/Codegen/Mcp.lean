import Effect4.Codegen.JsonSchema

/-!
# Codegen.Mcp — the toolkit module and the MCP list payloads

Design: `docs/research/2026-09-04-codegen-api-design.md` §4, the `mcpToolkit` and
`mcpToolsList` rows. Two rules of the census (`src/Effect4/Codegen/Rule.lean`) live here:

| rule | id | target | emitter |
| --- | --- | --- | --- |
| `Rule.mcpToolkit` | `surface.mcp.toolkit` | ts | `toolkitModule` |
| `Rule.mcpToolsList` | `surface.mcp.toolsList` | json | `toolsListJson` |

Both are `emitted`, not `modeled`: no host receipt has landed, and
`Rule.modeled_has_receipt` keeps the stance honest.

**The reader half is `src/Effect4/Ingest/Mcp.lean`.** `ofMcpToolsList`, the parsers it is built
from, `toolFingerprint`, the `Ingest .mcpToolsList` instance, the quotient the round trip is
up to and the round-trip guards all live there; nothing in this module reads back what it
writes.

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

Every emitted key is a *required* or a *present optional* field of the cited class, and no
key is emitted that the class does not declare. An optional field the carrier does not have
is left out rather than emitted as `null`, which is what `Schema.optional` reads
(`McpSchema.ts:1561`, `:1570`, and so on).

| | |
| --- | --- |
| Carrier | none of its own; `TypeScript.Module` is the target package's and `Json` is the estate's |
| Operations | `toolkitModule`, `toolsListJson`, `resourcesListJson`, `promptsListJson`; the two `Emit` instances |
| Laws | none proved. `emit x = .ok _ → McpServer.check x.value = .ok ()` holds by construction: both rule emitters open with that check |
| Structure | two partial functions out of one carrier, each refusing by name, and two total ones |
| Payoff | the toolkit module and the three list payloads read one carrier, so a description cannot differ between the module and the wire |
| Anti-vacuity | the `#guard`s at the end: the three payloads on the fixture, the rendered module lines, and one refusal per constructor |
| Generation | this module *is* generation; nothing generates it |

## The refusals, by name

* **The server's own, unwrapped.** `toolkitModule` and `toolsListJson` open with
  `McpServer.check`, so an ill-formed server answers the refusal that check names and
  nothing else: a caller reads `identifierMissing "mcpServer" "shop"`, never "emit failed".
  This is the design note's §3.5 rule, and it is why there is no `emitNotWellFormed`
  constructor.
* **`notABinding "surface.mcp.toolkit" name`.** A name the toolkit module must bind as a
  top-level constant and cannot: a tool name (`get-user` is a legal MCP name and not a legal
  TypeScript identifier, `src/Effect4/Surface/Agent.lean`), a resource name, a prompt name, or
  the server's own name. The module refuses rather than inventing a mangling, because a
  mangled constant is a second spelling of the value's identity.
* **`refusedShape "surface.mcp.toolkit" shape site`**, `shape ∈ Rule.refuses .mcpToolkit`
  (`= Rule.schemaShapes`). A schema slot `src/Effect4/Codegen/Spell.lean` has no constructor
  spelling for; `site` is `<tool>.parameters`, `<tool>.success` or `<tool>.failure`, so the
  caller reads which slot of which tool was refused.
* **`refusedShape "surface.mcp.toolsList" shape site`**, `shape ∈ Rule.refuses .mcpToolsList`
  (`= Rule.jsonSchemaShapes`). A schema `src/Effect4/Codegen/JsonSchema.lean` will not compile;
  `site` is the tool's name for its own `inputSchema` and the reference key for a `$defs`
  entry.

`resourcesListJson` and `promptsListJson` are total and are not rules: no field of a
resource or a prompt is compiled, so nothing can fall outside a fragment.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Mcp

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen
open Effect4.Codegen.JsonSchema (toJsonSchema numberSchema)
open TypeScript (Expr)

/-! ## Reachable definitions

`getJsonSchemaFromSchemaWith` (`unstable/ai/Tool.ts:1725-1744`) compiles the parameters to a
document and, when that document has definitions, hangs them on the root as `$defs`. rc.112's
document collects a definition only for a reference it actually meets, so the definitions
emitted here are the references reachable from the parameters, not the whole domain.

The syntactic walk and its de-duplication are the layer's one pair, `Codegen.referenceKeys`
and `Codegen.dedupe` (`src/Effect4/Codegen/Spell.lean`); this module adds only the closure over
the table.
-/

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
  closeKeys refs refs.length (dedupe [] (referenceKeys 64 representation))

/-- The `$defs` entries for a representation: the reachable definitions, in the table's own
order, each compiled by `Codegen.JsonSchema`. A compilation refusal is addressed to
`mcpToolsList` and to the entry's own key. -/
def reachableDefinitions (refs : List ReferenceEntry) (representation : Representation) :
    Except Refusal (List (String × Json)) :=
  let wanted := reachableKeys refs representation
  traverse
    (fun entry =>
      (addressed Rule.mcpToolsList.id entry.key
          (toJsonSchema refs entry.representation)).map fun compiled =>
        (entry.key, compiled))
    (refs.filter fun entry => wanted.contains entry.key)

/-! ## The list payloads -/

/--
The `inputSchema` of one tool: the parameters' JSON Schema, with the reachable
definitions hung on the root as `$defs` when there are any.

The compilation's refusal is addressed to `mcpToolsList` and to the tool, so a caller reads
`refusedShape "surface.mcp.toolsList" "schema.checks" "get_user"`.

Pin: `unstable/ai/Tool.ts:1725-1744`.
-/
def toolInputSchema {refs : List ReferenceEntry} (tool : Tool refs) :
    Except Refusal Json := do
  let root ← addressed Rule.mcpToolsList.id tool.name (toJsonSchema refs tool.parameters.rep)
  let definitions ← reachableDefinitions refs tool.parameters.rep
  match definitions with
  | [] => .ok root
  | _ :: _ =>
    match root with
    | .obj fields => .ok (.obj (objSet fields "$defs" (.obj definitions)))
    | other => .ok other

/-- One entry of `tools/list`: `name`, `description` when the tool has one, and
`inputSchema`, in `McpSchema.Tool`'s own field order (`:1559-1596`). -/
def toolListEntry {refs : List ReferenceEntry} (tool : Tool refs) :
    Except Refusal Json := do
  let inputSchema ← toolInputSchema tool
  .ok (.obj
    ([("name", .str tool.name)] ++
      (match tool.descriptionOf with
        | some text => [("description", Json.str text)]
        | none => []) ++
      [("inputSchema", inputSchema)]))

/--
The `tools/list` result payload (`unstable/ai/McpSchema.ts:1604-1610`).

The server's own refusal when it is not well formed, unwrapped; then one entry per tool,
first refusal wins.

surface: rule.surface.mcp.toolsList -/
def toolsListJson (dom : Domain) (server : McpServer dom.refs) : Except Refusal Json := do
  let _ ← McpServer.check server
  let entries ← traverse toolListEntry server.tools
  .ok (.obj [("tools", .arr entries)])

/--
The `resources/list` result payload (`unstable/ai/McpSchema.ts:1031-1037`),
whose entries are `McpSchema.Resource`'s `uri`, `name`, `description` and
`mimeType` in that order (`:875-916`).

Total, unlike `toolsListJson`: no field of a resource is compiled, so nothing
can fall outside a fragment.
-/
def resourcesListJson (dom : Domain) (server : McpServer dom.refs) : Json :=
  .obj
    [("resources", .arr (server.resources.map fun resource =>
      .obj
        ([("uri", .str resource.uri), ("name", .str resource.name)] ++
          (match resource.descriptionOf with
            | some text => [("description", Json.str text)]
            | none => []) ++
          (match resource.mimeType with
            | some text => [("mimeType", Json.str text)]
            | none => []))))]

/--
The `prompts/list` result payload (`unstable/ai/McpSchema.ts:1382-1388`), whose
entries are `McpSchema.Prompt`'s `name`, `description` and `arguments`
(`:1218-1239`), each argument being `McpSchema.PromptArgument`'s `name` and
`required` (`:1196-1210`).
-/
def promptsListJson (dom : Domain) (server : McpServer dom.refs) : Json :=
  .obj
    [("prompts", .arr (server.prompts.map fun prompt =>
      .obj
        ([("name", .str prompt.name)] ++
          (match prompt.descriptionOf with
            | some text => [("description", Json.str text)]
            | none => []) ++
          [("arguments", .arr (prompt.arguments.map fun argument =>
            .obj [("name", .str argument.1), ("required", .bool argument.2)]))])))]

/-! ## The toolkit module -/

/--
Qualify an entity constant with the namespace the generated module imports it
under.

`src/Effect4/Codegen/Spell.lean` spells a `reference` as the bare identifier of the
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

/-- The constructor spelling of a schema as this module writes it: `Spell.spell`, its
refusal addressed to `mcpToolkit` and to the slot it was spelling, with entity references
qualified. -/
def spellQualified (refs : List ReferenceEntry) (site : String)
    (representation : Representation) : Except Refusal Expr :=
  (addressed Rule.mcpToolkit.id site (Spell.spell refs representation)).map
    (qualifyEntities refs "Entities" 64)

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

/-- One tool's declaration. `notABinding` when the tool name is not a legal generated
binding; otherwise the three schema slots in emission order, each refusal addressed to its
own site.

Pin: `unstable/ai/Tool.ts:1204-1246`. -/
def toolDecl {refs : List ReferenceEntry} (tool : Tool refs) :
    Except Refusal TypeScript.Decl :=
  if !identifier tool.name then .error (.notABinding Rule.mcpToolkit.id tool.name)
  else do
    let parameters ← spellQualified refs (tool.name ++ ".parameters") tool.parameters.rep
    let success ← spellQualified refs (tool.name ++ ".success") tool.success.rep
    let failure ← optional
      (fun (schema : Sch refs .json) =>
        spellQualified refs (tool.name ++ ".failure") schema.rep)
      tool.failure
    .ok (.const
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
                  (match failure with
                    | some value => [("failure", value)]
                    | none => [])) ] })

/-- One resource's declaration, with a typed stub for its content. `notABinding` when the
resource name is not a legal generated binding.

Pin: `unstable/ai/McpServer.ts:1894-1909`. The content stub takes the `string`
leg of that overload's content union, which rc.112 turns into a text resource. -/
def resourceDecl (resource : Resource) : Except Refusal TypeScript.Decl :=
  if !identifier resource.name then .error (.notABinding Rule.mcpToolkit.id resource.name)
  else
    .ok (.const
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

/-- One prompt's declaration, with a typed stub for its content. `notABinding` when the
prompt name is not a legal generated binding.

Pin: `unstable/ai/McpServer.ts:2106-2126`. An argument becomes one field of the
`parameters` record; a required argument is `Schema.String` and an optional one
is `Schema.optionalKey(Schema.String)` (`Schema.ts:2444`), which is the same
optionality `McpSchema.PromptArgument.required` carries on the wire
(`:1196-1210`). -/
def promptDecl (prompt : Prompt) : Except Refusal TypeScript.Decl :=
  if !identifier prompt.name then .error (.notABinding Rule.mcpToolkit.id prompt.name)
  else
    .ok (.const
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
`McpServer.prompt` constant per registered value. The server's own refusal when it is not
well formed, `notABinding` for a name it needs as a binding and does not have, and
`refusedShape` for a schema with no constructor spelling.

surface: rule.surface.mcp.toolkit -/
def toolkitModule (dom : Domain) (server : McpServer dom.refs) :
    Except Refusal TypeScript.Module := do
  let _ ← McpServer.check server
  if !identifier server.name then .error (.notABinding Rule.mcpToolkit.id server.name)
  else do
    let toolDecls ← traverse toolDecl server.tools
    let resourceDecls ← traverse resourceDecl server.resources
    let promptDecls ← traverse promptDecl server.prompts
    .ok
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

/-! ## The instances -/

instance : Emit .mcpToolkit := ⟨fun x => toolkitModule x.domain x.value⟩

instance : Emit .mcpToolsList := ⟨fun x => toolsListJson x.domain x.value⟩

/-! ## Anti-vacuity -/

-- the three list payloads, field for field
#guard toolsListJson shopDomain shopServer ==
  .ok (.obj
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
    { getUserTool with parameters := ⟨Schema.reference "Address", by decide⟩ }).toOption.isSome
  = true
#guard ((toolInputSchema
    { getUserTool with parameters := ⟨Schema.reference "Address", by decide⟩ }).toOption.map
  fun schema => match schema with
    | .obj fields => (objGet fields "$defs").isSome
    | _ => false) == some true
#guard ((toolInputSchema getUserTool).toOption.map fun schema => match schema with
    | .obj fields => (objGet fields "$defs").isSome
    | _ => false) == some false

-- the module builds, and its first lines are pinned
#guard (toolkitModule shopDomain shopServer).toOption.isSome = true
#guard ((toolkitModule shopDomain shopServer).toOption.map
    fun target => ((TypeScript.Render.module TypeScript.house0 target).splitOn "\n").take 7) ==
  some
    [ "/**"
    , " * Generated by Effect4 Surface."
    , " *"
    , " * Do not edit."
    , " */"
    , "import { Effect } from \"effect\""
    , "import * as Schema from \"effect/Schema\"" ]

#guard ((toolkitModule shopDomain shopServer).toOption.map
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
#guard ((toolkitModule shopDomain shopServer).toOption.map
    fun target => ((target.decls.drop 2).take 2).map fun declaration =>
      ((TypeScript.Render.decl TypeScript.house0 declaration).splitOn "\n").take 1) ==
  some
    [ ["export const shopToolkit = Toolkit.make(get_user, list_users)"]
    , ["export const shopToolkitLayer = McpServer.toolkit(shopToolkit)"] ]

-- the refusals, by constructor: the server's own, unwrapped
#guard refusal? (toolkitModule shopDomain { shopServer with annotations := none }) ==
  some (.identifierMissing "mcpServer" "shop")

-- a name the module must bind and cannot: a tool name, then a resource name
#guard refusal? (toolkitModule shopDomain
  { shopServer with tools := [{ getUserTool with name := "get-user" }] }) ==
  some (.notABinding "surface.mcp.toolkit" "get-user")
#guard refusal? (toolkitModule shopDomain
  { shopServer with resources := [{ usersResource with name := "class" }] }) ==
  some (.notABinding "surface.mcp.toolkit" "class")

-- a schema the constructor spelling refuses, addressed to the slot it was found in
#guard refusal? (toolkitModule shopDomain
  { shopServer with tools :=
      [{ getUserTool with
          parameters :=
            ⟨Schema.struct [Schema.property "id" (.string none [Check.pattern "^a$"])],
              by decide⟩ }] }) ==
  some (.refusedShape "surface.mcp.toolkit" "schema.checkPattern" "get_user.parameters")

-- a schema the JSON Schema compiler refuses, addressed to the tool it was found on
#guard refusal? (toolsListJson shopDomain
  { shopServer with tools :=
      [{ getUserTool with
          parameters :=
            ⟨Schema.struct [Schema.property "id" (.string none [Check.trimmed])],
              by decide⟩ }] }) ==
  some (.refusedShape "surface.mcp.toolsList" "schema.checks" "get_user")

-- and the ledgers those shapes are held to are these rules' own
#guard (Rule.refuses .mcpToolkit) == Rule.schemaShapes
#guard (Rule.refuses .mcpToolsList) == Rule.jsonSchemaShapes

-- the instances, through the one call
#guard (emit .mcpToolkit ⟨shopDomain, shopServer⟩).toOption.isSome
#guard (emit .mcpToolsList ⟨shopDomain, shopServer⟩).toOption.isSome

end Effect4.Codegen.Mcp
