import Effect4.Ingest.Mcp

/-!
# Ingest Mcp contract — the reader of `surface.mcp.toolsList`, at its quotient

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4 and §6 ("`Test/Ingest/*`, one
per reader: the round trip at its quotient"). The quotient is named in
`src/Effect4/Ingest/Mcp.lean`'s header, and `toolFingerprint` is the part of a tool the
`tools/list` fragment carries in both directions: the name, the parameter representation and
the description.

What is pinned here:

* the round trip **through both instances**: `emit .mcpToolsList ⟨shopDomain, shopServer⟩`,
  then `ingest .mcpToolsList shopDomain` of the payload it answered, compared through
  `toolFingerprint`. The payload is destructured inside the `#guard`, so no definition of
  this battery holds an artefact;
* the parts the quotient drops: `success` comes back `Schema.unknown` and `failure` `none`,
  and at the server level the name and the version are empty, with no resources, no prompts
  and no annotation bag — the decoded server is deliberately not well formed, because what
  the wire does not carry is not invented;
* the consequence, as a receipt: a wire entry with no `description` ingests and is then
  refused by `Tool.check` with `descriptionMissing`, which is the reader refusing to invent
  a description rather than the reader hiding one;
* the reader's refusals through `ingest`, by constructor: the four `mcpMalformed` sites of
  the header, and the schema reader's own refusal, unwrapped, for an `inputSchema` outside
  the JSON Schema fragment.
-/

set_option autoImplicit false

namespace Test.Ingest.McpContract

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen Effect4.Ingest

/-! ## The round trip, through both instances, at the fingerprint -/

#guard (match emit .mcpToolsList ⟨shopDomain, shopServer⟩ with
  | .ok (.json payload) =>
    match (ingest .mcpToolsList shopDomain payload :
        Except Refusal (InDomain McpServer)) with
    | .ok server => some (server.value.tools.map Ingest.Mcp.toolFingerprint)
    | .error _ => none
  | _ => none) ==
  some
    [ ("get_user", Schema.struct [Schema.property "id" Schema.string],
        some "Fetch one shop customer by id.")
    , ("list_users", Schema.struct [Schema.property "limit" Schema.number true],
        some "List the shop's customers.") ]

-- the fingerprint is the emitted server's own, so the round trip compares like with like
#guard shopServer.tools.map Ingest.Mcp.toolFingerprint ==
  [ ("get_user", Schema.struct [Schema.property "id" Schema.string],
      some "Fetch one shop customer by id.")
  , ("list_users", Schema.struct [Schema.property "limit" Schema.number true],
      some "List the shop's customers.") ]

/-! ## The parts the quotient drops -/

#guard (match emit .mcpToolsList ⟨shopDomain, shopServer⟩ with
  | .ok (.json payload) =>
    match (ingest .mcpToolsList shopDomain payload :
        Except Refusal (InDomain McpServer)) with
    | .ok server =>
      some (server.value.tools.map fun tool => (tool.success.rep, tool.failure.isSome))
    | .error _ => none
  | _ => none) ==
  some [(Schema.unknown, false), (Schema.unknown, false)]

#guard (match emit .mcpToolsList ⟨shopDomain, shopServer⟩ with
  | .ok (.json payload) =>
    match (ingest .mcpToolsList shopDomain payload :
        Except Refusal (InDomain McpServer)) with
    | .ok server =>
      some (server.value.name, server.value.version, server.value.resources.length,
        server.value.prompts.length, server.value.annotations.isSome)
    | .error _ => none
  | _ => none) == some ("", "", 0, 0, false)

-- the server that went in carries all four, so the drop is real
#guard (shopServer.name, shopServer.version, shopServer.resources.length,
    shopServer.prompts.length, shopServer.annotations.isSome) ==
  ("shop", "1.0.0", 1, 1, true)

-- the domain the reader is handed is the closed world of the decoded tools
#guard (match emit .mcpToolsList ⟨shopDomain, shopServer⟩ with
  | .ok (.json payload) =>
    match (ingest .mcpToolsList shopDomain payload :
        Except Refusal (InDomain McpServer)) with
    | .ok server => some server.domain.name
    | .error _ => none
  | _ => none) == some "shop"

/-! ## No description on the wire, and the refusal that follows

The decoded tool carries `identifier` set to its name and `description` when the wire has
one, and nothing else. An entry with no description therefore decodes and is then refused by
name, which is "the refusal names the ones it lacks" rather than a silently invented bag.
-/

/-- A `tools/list` payload whose one entry has a name and an empty parameter object, and no
description. -/
def undescribedPayload : Json :=
  .obj
    [("tools", .arr
      [ .obj
          [ ("name", .str "ping")
          , ("inputSchema", .obj
              [ ("type", .str "object"), ("properties", .obj [])
              , ("additionalProperties", .bool false) ]) ] ])]

#guard (match (ingest .mcpToolsList shopDomain undescribedPayload :
    Except Refusal (InDomain McpServer)) with
  | .ok server => some (server.value.tools.map (Tool.check "shop"))
  | .error _ => none) == some [.error (.descriptionMissing "tool" "ping")]

-- it does decode: the refusal is the carrier's check, not the reader's
#guard (match (ingest .mcpToolsList shopDomain undescribedPayload :
    Except Refusal (InDomain McpServer)) with
  | .ok server => some (server.value.tools.map Ingest.Mcp.toolFingerprint)
  | .error _ => none) == some [("ping", Schema.struct [], none)]

/-! ## The reader's refusals, through `ingest`, by constructor -/

#guard refusal? (ingest .mcpToolsList shopDomain (.str "x")) ==
  some (.mcpMalformed "tools/list")

#guard refusal? (ingest .mcpToolsList shopDomain (.obj [])) ==
  some (.mcpMalformed "tools")

#guard refusal? (ingest .mcpToolsList shopDomain (.obj [("tools", .arr [.str "x"])])) ==
  some (.mcpMalformed "tools/0")

#guard refusal? (ingest .mcpToolsList shopDomain (.obj [("tools", .arr [.obj []])])) ==
  some (.mcpMalformed "tools/0/name")

#guard refusal? (ingest .mcpToolsList shopDomain
    (.obj [("tools", .arr [.obj [("name", .str "ping")]])])) ==
  some (.mcpMalformed "tools/0/inputSchema")

-- an `inputSchema` inside the JSON Schema fragment but not of `Kind.struct`
#guard refusal? (ingest .mcpToolsList shopDomain
    (.obj [("tools", .arr [.obj
      [("name", .str "ping"), ("inputSchema", .obj [("type", .str "string")])]])])) ==
  some (.mcpMalformed "tools/0/inputSchema")

-- and one outside it: the schema reader's own refusal, unwrapped, naming the keyword
#guard refusal? (ingest .mcpToolsList shopDomain
    (.obj [("tools", .arr [.obj
      [("name", .str "ping"), ("inputSchema", .obj [("type", .str "integer")])]])])) ==
  some (.jsonSchemaUnsupportedType "integer")

-- the index in the path is the entry's own
#guard refusal? (ingest .mcpToolsList shopDomain
    (.obj [("tools", .arr
      [ .obj
          [ ("name", .str "ping")
          , ("inputSchema", .obj
              [ ("type", .str "object"), ("properties", .obj [])
              , ("additionalProperties", .bool false) ]) ]
      , .obj [] ])])) ==
  some (.mcpMalformed "tools/1/name")

end Test.Ingest.McpContract
