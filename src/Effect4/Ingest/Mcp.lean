import Effect4.Ingest.JsonSchema
import Effect4.Codegen.Mcp

/-!
# Ingest.Mcp — the `tools/list` payload, read backwards

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4 and the `mcpToolsList` row of
§4. The projection this inverts is `src/Effect4/Codegen/Mcp.lean`'s `toolsListJson`
(`unstable/ai/McpSchema.ts:1604-1610`, whose entries are `McpSchema.Tool` at `:1559-1596`);
the toolkit module, the other two list payloads and the pinned spelling table are that
module's, and nothing here emits.

One rule is read here, `mcpToolsList` (`surface.mcp.toolsList`). The schema fragment the
`inputSchema` of an entry is read on is `src/Effect4/Ingest/JsonSchema.lean`'s, exactly:
`ofJsonSchema`, with its own refusals and its own quotient.

| | |
| --- | --- |
| Carrier | none of its own: `Tool` and `McpServer` are `src/Effect4/Surface/Agent.lean`'s |
| Operations | `toolsPath`, `toolOfJson`, `toolsOfJson`, `ofMcpToolsList`, `toolFingerprint`; the `Ingest .mcpToolsList` instance |
| Laws | `kindCheck_unknown_json`. The round trip is a `#guard` on the fixture at the quotient named below; the general theorem is an **owed** row |
| Structure | a partial function `Json ⇀ List (Tool refs)`, a section of the emitter up to that quotient |
| Payoff | wrapping a foreign MCP server's tool list as surface rows is one call, `ingest .mcpToolsList dom json` |
| Anti-vacuity | the fixture round trip through `toolFingerprint`, the parts the quotient drops, and one refusing `#guard` per ingest clause |
| Generation | none: this module is the reader |

## The quotient the round trip is up to

`toolsListJson` then `ofMcpToolsList` is **not** the identity on `Tool`, and the drop is
named here the way `src/Effect4/Ingest/JsonSchema.lean` names its own:

* `success` and `failure` are not on the `tools/list` wire in the fragment emitted there, so
  the decoded tool carries `success := Schema.unknown` and `failure := none`;
* the only annotations the decoded tool carries are `identifier`, set to the tool name, and
  `description`, when the wire has one. Every other entry of the original bag is gone;
* `parameters` survives exactly, because `toJsonSchema` and `ofJsonSchema` agree on an
  annotation-free struct of admitted property types. A parameter object whose nodes carry
  `description` or `title` is emitted with those keywords and then **refused** on the way
  back, because the ingest fragment admits no annotation keyword; lifting that is
  `src/Effect4/Ingest/JsonSchema.lean`'s row, not this one;
* at the server level the wire carries the tools and nothing else, so the decoded server has
  an empty name, an empty version, no resources, no prompts and no annotation bag. Every
  field of `McpServer` is required, so those are the empty values rather than absent fields;
  the decoded server is therefore *not* `McpServer.WellFormed`, exactly as the decoded entity
  of `src/Effect4/Ingest/JsonSchema.lean` is not `Entity.WellFormed`, and for the same reason:
  what the wire does not carry is not invented.

So the `#guard` below compares `(name, parameters.rep, descriptionOf)`, which is exactly the
part of a tool the fragment carries both ways.

**`RoundTrip .mcpToolsList` is not stated as a `Prop` here, and the reason is the type.**
`Ingest.RoundTrip r quotient` quantifies `∀ dom x out`, and its answer is
`Ingest.read dom out = .ok (quotient x)`; `Rule.Input .mcpToolsList` is `InDomain McpServer`,
so the answer carries the `dom` the reader was handed while `quotient x` can only carry a
domain read off `x`. No `quotient : r.Input → r.Input` satisfies that for every `dom`, so the
law is stated here as prose and pinned by the fixture guards below — the same choice, for the
same reason, that `Ingest .entityJsonSchema` makes. `Ingest .deployWrangler` can state its
`RoundTrip` because a `Deployment` carries no domain.

## The refusals, by name

Every one is `mcpMalformed <path>`, with the path naming the entry and the field:

* a payload that is not an object (`tools/list`) or has no `tools` array (`tools`);
* an entry that is not an object (`tools/<i>`);
* a missing or non-string `name` (`tools/<i>/name`);
* a missing `inputSchema`, or one that is not `Kind.struct` under the table
  (`tools/<i>/inputSchema`).

An `inputSchema` outside the schema fragment answers `ofJsonSchema`'s own refusal, unwrapped
— `jsonSchemaUnsupportedType`, `jsonSchemaUnsupportedKeywords`, and the rest of that group —
because that is the reader that refused it, and a wrapper would hide which keyword was at
fault.
-/

set_option autoImplicit false

namespace Effect4.Ingest.Mcp

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen Effect4.Codegen.Mcp
open Effect4.Ingest.JsonSchema (ofJsonSchema)

/-! ## Reading one entry -/

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
"the refusal names the ones it lacks".
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
Read a `tools/list` payload back as surface rows, on the fragment
`src/Effect4/Ingest/JsonSchema.lean` admits.

Total on that fragment, refusing the rest by constructor. The quotient it is an inverse up
to is named in this module's header.

surface: rule.surface.mcp.toolsList -/
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

/--
The reader of `surface.mcp.toolsList`.

The artefact is a tool list, so what comes back is a server carrying those tools and nothing
else: the name and the version are empty, there are no resources and no prompts, and the
annotation bag is absent. That is the server half of the quotient this module's header
states; every field of `McpServer` is required, so each is the empty value of its type rather
than an absent field, and the decoded server is deliberately not well formed.
-/
instance : Ingest .mcpToolsList :=
  ⟨fun dom json => (ofMcpToolsList dom.refs json).map fun tools =>
    ⟨dom,
      { name := ""
        version := ""
        tools := tools
        resources := []
        prompts := []
        annotations := none }⟩⟩

/-! ## Anti-vacuity -/

-- the round trip, up to the quotient named in this module's header
#guard ((toolsListJson shopDomain shopServer).toOption.map fun payload =>
    (ofMcpToolsList shopDomain.refs payload).map (List.map toolFingerprint)) ==
  some (.ok
    [ ("get_user", Schema.struct [Schema.property "id" Schema.string],
        some "Fetch one shop customer by id.")
    , ("list_users", Schema.struct [Schema.property "limit" Schema.number true],
        some "List the shop's customers.") ])

-- and the parts the quotient drops
#guard ((toolsListJson shopDomain shopServer).toOption.map fun payload =>
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

-- the instance, through the one call
#guard (ingest .mcpToolsList shopDomain
  ((toolsListJson shopDomain shopServer).toOption.getD .null)).toOption.isSome

end Effect4.Ingest.Mcp
