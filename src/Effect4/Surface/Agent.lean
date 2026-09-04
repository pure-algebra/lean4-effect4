import Effect4.Surface.Entity

/-!
# Surface.Agent: the MCP surface

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.5.

An **agent server** is one more surface: a name, a version, a list of tools
whose parameters and results are kinded schemas, a list of resources and a list
of prompts. Nothing here is a protocol implementation; the carrier is the
first-order description that the toolkit module and the `tools/list`,
`resources/list` and `prompts/list` payloads of `Effect4/Surface/Agent/Emit.lean`
are projections of.

The shape is `Effect4/Arch/Views.lean`'s and `Effect4/Surface/Entity.lean`'s: a
first-order structure, a `check` that is a list of named clauses read left to
right and answers the *first* refusal (`Effect4/Surface/Facts.lean`), a
`WellFormed` that is `check = .ok ()` and therefore one `Decidable` equation, a
`wellFormed_iff` proving it equal to the conjunction of the clauses so a later
capability can ask for exactly the ones it needs, a `json` projection, a
`Document` view with an `Arch.accepts` receipt, and a `Canonical` instance.

## Semantics live in bags, never in a field

§15.3 binds: an MCP tool's `description` **is** its `description` annotation.
So no carrier here has a description field, and `Tool.descriptionOf`,
`Resource.descriptionOf`, `Prompt.descriptionOf` and `McpServer.descriptionOf`
all read `Effect4/Surface/Annotate.lean`'s `descriptionKey` off the value's own
bag through `bagValue?`. `identifier` is read the same way and both are
required by §15.2, so a tool with no meaning is ill-formed by the same
mechanism as one with an illegal name.

The bag is a field of the carrier rather than of a representation because a
resource and a prompt have no representation to hang one on; a `Tool` could
have used its `parameters.rep` bag, and does not, so that all four carriers
answer the semantic clauses the same way.

## The tool-name grammar, and where it comes from

rc.112's own wire schema types a tool name as `Schema.String` and nothing more
(`unstable/ai/McpSchema.ts:1559-1563`), so the grammar is **not** read off
rc.112. It is the Model Context Protocol's, at the protocol versions this
release declares (`unstable/ai/McpProtocol.ts:24`, `"2024-11-05" |
"2025-03-26" | "2025-06-18" | "2025-11-25"`): `^[A-Za-z0-9_-]{1,64}$`. It is
decided over UTF-8 bytes by the route `Effect4/Surface/Spell.lean`'s
`identifier` takes, `name.toUTF8.data.toList`, because `ByteArray.toList` does
not reduce in the kernel on this toolchain and a `decide` over it would get
stuck rather than answer.

That grammar is *wider* than a legal TypeScript binding: `get-user` is a legal
tool name and not a legal identifier. The toolkit emitter therefore refuses a
tool whose name it cannot spell as a constant, rather than this module
narrowing the wire grammar to the target's; the refusal row is named in
`Effect4/Surface/Agent/Emit.lean`.

| | |
| --- | --- |
| Carrier | `Tool refs` (5 fields), `Resource` (4 fields), `Prompt` (3 fields), `McpServer refs` (6 fields) |
| Operations | `mcpToolName`, the four `identifierOf`/`descriptionOf` pairs, the four `check`s, `Tool.json`, `Resource.json`, `Prompt.json`, `McpServer.json`, `mcpDoc` |
| Laws | `Tool.wellFormed_iff`, `Resource.wellFormed_iff`, `Prompt.wellFormed_iff`, `McpServer.wellFormed_iff`, the three `check*_ok_iff` walks, `McpServer.wellFormed_tool` |
| Structure | a three-part free monoid (tools, resources, prompts) over one server record; every clause is a `Bool` and the check is the `firstRefusal` fold |
| Payoff | the three duplicate-name throws an MCP registration would make at run time become one decidable clause each, and every emitted description has exactly one source |
| Anti-vacuity | the `shopServer` fixture: `decide` receipts for `WellFormed`, an `Arch.accepts` receipt for the view, and one refusing `#guard` per clause |
| Generation | none here; `Effect4/Surface/Agent/Emit.lean` owns the two rules |

## What is deliberately not here

* **A server-name clause.** The plan's §4.5 clause list is the five naming
  clauses plus §15.2's two, and a server name is not one of them. The toolkit
  emitter needs a legal binding and answers `none` without one, which is the
  emitter's refusal, not the carrier's.
* **Resource templates.** rc.112's `McpServer.resource` has a second,
  tagged-template overload for URI templates with typed parameters
  (`unstable/ai/McpServer.ts:1921-1947`). A `Resource` here is the plain
  overload only (`:1894-1909`); the template form is an owed row.
* **Tool annotations in the MCP sense.** `McpSchema.ToolAnnotations`
  (`:1481`) is a distinct wire record (`title`, `readOnlyHint`, and so on) and
  is not this module's `annotations` field, which is the estate's own
  `Annotations` bag. Nothing here emits `McpSchema.ToolAnnotations`.
* **`outputSchema`.** `McpSchema.Tool.outputSchema` (`:1577-1580`) is optional
  and rc.112 fills it only when the success schema compiles to an object
  (`McpServer.ts:1535-1538`). `Tool.success` is carried, and the `tools/list`
  projection does not emit `outputSchema`; the row is owed.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema Effect4.Store
open Effect4.Arch (accepts)

/-! ## The MCP tool-name grammar, over bytes -/

/-- A byte of `[A-Za-z0-9_-]`: the whole character class of the MCP tool-name
grammar. `45` is `-` and `95` is `_`. -/
def mcpNameByte (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) ||
    (48 ≤ byte && byte ≤ 57) || byte == 95 || byte == 45

/--
A legal MCP tool name: `^[A-Za-z0-9_-]{1,64}$`, decided over UTF-8 bytes.

Every byte of the class is below `0x80`, so a name containing any non-ASCII
character has a byte outside the class and is refused; the byte count and the
character count therefore agree on every admitted name and the `{1,64}` bound
is exact.
-/
def mcpToolName (name : String) : Bool :=
  let bytes := name.toUTF8.data.toList
  !bytes.isEmpty && bytes.length ≤ 64 && bytes.all mcpNameByte

/-! ## The carriers -/

/--
One tool of an agent server.

`parameters` is `Kind.struct`, because the MCP wire form is a JSON Schema
object (`unstable/ai/McpSchema.ts:1544-1551`); `success` and `failure` are
`Kind.json`, because rc.112 passes them to `Schema.toJsonSchemaDocument`
unchanged (`unstable/ai/Tool.ts:1719-1744`). `failure` is optional because
rc.112 defaults it to `Schema.Never` (`Tool.ts:1268`), which is a different
statement from a declared failure type.

No `DecidableEq` and no `Repr`: `Sch` carries a proof field, exactly as
`Effect4/Surface/Kind.lean` records, so the compared and stored content is the
`json` projection below.
-/
structure Tool (refs : List ReferenceEntry) where
  /-- The tool name the model calls, in the MCP grammar. -/
  name : String
  /-- The parameter object schema. -/
  parameters : Sch refs .struct
  /-- The success result schema. -/
  success : Sch refs .json
  /-- The declared failure schema, when the tool declares one. -/
  failure : Option (Sch refs .json)
  /-- The semantic bag: `identifier` and `description` (§15.2). -/
  annotations : Annotations

/--
One resource of an agent server: the plain overload of rc.112's
`McpServer.resource` (`unstable/ai/McpServer.ts:1894-1909`).
-/
structure Resource where
  /-- The resource URI, the server's identity for it. -/
  uri : String
  /-- The human-readable name clients show. -/
  name : String
  /-- The MIME type, when the server knows it. -/
  mimeType : Option String
  /-- The semantic bag: `identifier` and `description` (§15.2). -/
  annotations : Annotations
deriving DecidableEq

/--
One prompt of an agent server.

`arguments` is `(name, required)`, the two fields of
`McpSchema.PromptArgument` this fragment models (`:1196-1210`); a per-argument
description is an owed row.
-/
structure Prompt where
  /-- The prompt name. -/
  name : String
  /-- The templating arguments: a name and whether it must be provided. -/
  arguments : List (String × Bool)
  /-- The semantic bag: `identifier` and `description` (§15.2). -/
  annotations : Annotations
deriving DecidableEq

/--
An agent server: the whole MCP surface of one application.

`refs` is the domain's references table, so a tool's schemas refer to entities
by `Schema.reference name` and the closed world is the domain, exactly as it is
for an entity.
-/
structure McpServer (refs : List ReferenceEntry) where
  /-- The server name, as `McpServer.layerStdio` takes it
  (`unstable/ai/McpServer.ts:1207-1209`). -/
  name : String
  /-- The server version, the second field of the same options record. -/
  version : String
  /-- The tools, in registration order. -/
  tools : List (Tool refs)
  /-- The resources, in registration order. -/
  resources : List Resource
  /-- The prompts, in registration order. -/
  prompts : List Prompt
  /-- The semantic bag: `identifier` and `description` (§15.2). -/
  annotations : Annotations

/-! ## Semantics, read only through the bags -/

namespace Tool

variable {refs : List ReferenceEntry}

/-- The tool's `identifier`. -/
def identifierOf (tool : Tool refs) : Option String :=
  bagValue? identifierKey tool.annotations

/-- The tool's `description`. This *is* the MCP `description` of §15.3; there
is no second spelling. -/
def descriptionOf (tool : Tool refs) : Option String :=
  bagValue? descriptionKey tool.annotations

end Tool

namespace Resource

/-- The resource's `identifier`. -/
def identifierOf (resource : Resource) : Option String :=
  bagValue? identifierKey resource.annotations

/-- The resource's `description`. -/
def descriptionOf (resource : Resource) : Option String :=
  bagValue? descriptionKey resource.annotations

end Resource

namespace Prompt

/-- The prompt's `identifier`. -/
def identifierOf (prompt : Prompt) : Option String :=
  bagValue? identifierKey prompt.annotations

/-- The prompt's `description`. -/
def descriptionOf (prompt : Prompt) : Option String :=
  bagValue? descriptionKey prompt.annotations

/-- The argument names, in declaration order. -/
def argumentNames (prompt : Prompt) : List String :=
  prompt.arguments.map Prod.fst

end Prompt

namespace McpServer

variable {refs : List ReferenceEntry}

/-- The server's `identifier`. -/
def identifierOf (server : McpServer refs) : Option String :=
  bagValue? identifierKey server.annotations

/-- The server's `description`. -/
def descriptionOf (server : McpServer refs) : Option String :=
  bagValue? descriptionKey server.annotations

/-- The tool names, in registration order. -/
def toolNames (server : McpServer refs) : List String :=
  server.tools.map Tool.name

/-- The resource URIs, in registration order. -/
def resourceUris (server : McpServer refs) : List String :=
  server.resources.map Resource.uri

/-- The prompt names, in registration order. -/
def promptNames (server : McpServer refs) : List String :=
  server.prompts.map Prompt.name

end McpServer

/-! ## Well-formedness, as named clauses -/

namespace Tool

variable {refs : List ReferenceEntry}

/-- Clause: the tool name is in the MCP grammar. -/
def nameLegal (tool : Tool refs) : Bool := mcpToolName tool.name

/-- Clause (§15.2): the bag carries an `identifier`. -/
def identified (tool : Tool refs) : Bool := tool.identifierOf.isSome

/-- Clause (§15.2): the bag carries a `description`. -/
def described (tool : Tool refs) : Bool := tool.descriptionOf.isSome

/-- The clauses of a tool, in the order a check reads them. The server name is
carried only so a refusal can say which server the tool was registered on. -/
def clauses (server : String) (tool : Tool refs) : List (Bool × Refusal) :=
  [ (tool.nameLegal, .toolNameIllegal server tool.name)
  , (tool.identified, .identifierMissing "tool" tool.name)
  , (tool.described, .descriptionMissing "tool" tool.name) ]

/-- Check a tool: the clauses in order, first refusal wins. -/
def check (server : String) (tool : Tool refs) : Except Refusal Unit :=
  firstRefusal (tool.clauses server)

/-- The proposition a capability opts into. -/
def WellFormed (server : String) (tool : Tool refs) : Prop :=
  Tool.check server tool = .ok ()

instance (server : String) (tool : Tool refs) :
    Decidable (Tool.WellFormed server tool) := by
  unfold Tool.WellFormed; infer_instance

/-- The Bool projection, for a battery or an emitter that wants one. -/
def wellFormed (server : String) (tool : Tool refs) : Bool :=
  decide (Tool.WellFormed server tool)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (server : String) (tool : Tool refs) :
    Tool.wellFormed server tool = true ↔ Tool.WellFormed server tool := by
  simp [Tool.wellFormed]

/-- The tool name is in the MCP grammar. -/
def NameLegal (tool : Tool refs) : Prop := tool.nameLegal = true
/-- The bag carries an `identifier`. -/
def Identified (tool : Tool refs) : Prop := tool.identified = true
/-- The bag carries a `description`. -/
def Described (tool : Tool refs) : Prop := tool.described = true

/-- Well-formedness is exactly the conjunction of the named clauses. -/
theorem wellFormed_iff (server : String) (tool : Tool refs) :
    Tool.WellFormed server tool ↔
      (Tool.NameLegal tool ∧ Tool.Identified tool ∧ Tool.Described tool) := by
  rw [Tool.WellFormed, Tool.check, firstRefusal_ok_iff]
  simp [Tool.clauses, Tool.NameLegal, Tool.Identified, Tool.Described]

end Tool

namespace Resource

/-- Clause (§15.2): the bag carries an `identifier`. -/
def identified (resource : Resource) : Bool := resource.identifierOf.isSome

/-- Clause (§15.2): the bag carries a `description`. -/
def described (resource : Resource) : Bool := resource.descriptionOf.isSome

/-- The clauses of a resource, in the order a check reads them. -/
def clauses (resource : Resource) : List (Bool × Refusal) :=
  [ (resource.identified, .identifierMissing "resource" resource.name)
  , (resource.described, .descriptionMissing "resource" resource.name) ]

/-- Check a resource: the clauses in order, first refusal wins. -/
def check (resource : Resource) : Except Refusal Unit :=
  firstRefusal resource.clauses

/-- The proposition a capability opts into. -/
def WellFormed (resource : Resource) : Prop := Resource.check resource = .ok ()

instance (resource : Resource) : Decidable (Resource.WellFormed resource) := by
  unfold Resource.WellFormed; infer_instance

/-- The Bool projection. -/
def wellFormed (resource : Resource) : Bool := decide (Resource.WellFormed resource)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (resource : Resource) :
    Resource.wellFormed resource = true ↔ Resource.WellFormed resource := by
  simp [Resource.wellFormed]

/-- The bag carries an `identifier`. -/
def Identified (resource : Resource) : Prop := resource.identified = true
/-- The bag carries a `description`. -/
def Described (resource : Resource) : Prop := resource.described = true

/-- Well-formedness is exactly the conjunction of the named clauses. -/
theorem wellFormed_iff (resource : Resource) :
    Resource.WellFormed resource ↔
      (Resource.Identified resource ∧ Resource.Described resource) := by
  rw [Resource.WellFormed, Resource.check, firstRefusal_ok_iff]
  simp [Resource.clauses, Resource.Identified, Resource.Described]

end Resource

namespace Prompt

/-- Clause (§15.2): the bag carries an `identifier`. -/
def identified (prompt : Prompt) : Bool := prompt.identifierOf.isSome

/-- Clause (§15.2): the bag carries a `description`. -/
def described (prompt : Prompt) : Bool := prompt.descriptionOf.isSome

/-- Clause: no argument name is declared twice. -/
def argumentsDistinct (prompt : Prompt) : Bool := namesUnique prompt.argumentNames

/-- The clauses of a prompt, in the order a check reads them. -/
def clauses (prompt : Prompt) : List (Bool × Refusal) :=
  [ (prompt.identified, .identifierMissing "prompt" prompt.name)
  , (prompt.described, .descriptionMissing "prompt" prompt.name)
  , (prompt.argumentsDistinct,
      .promptArgumentDuplicate prompt.name (firstDuplicate prompt.argumentNames)) ]

/-- Check a prompt: the clauses in order, first refusal wins. -/
def check (prompt : Prompt) : Except Refusal Unit :=
  firstRefusal prompt.clauses

/-- The proposition a capability opts into. -/
def WellFormed (prompt : Prompt) : Prop := Prompt.check prompt = .ok ()

instance (prompt : Prompt) : Decidable (Prompt.WellFormed prompt) := by
  unfold Prompt.WellFormed; infer_instance

/-- The Bool projection. -/
def wellFormed (prompt : Prompt) : Bool := decide (Prompt.WellFormed prompt)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (prompt : Prompt) :
    Prompt.wellFormed prompt = true ↔ Prompt.WellFormed prompt := by
  simp [Prompt.wellFormed]

/-- The bag carries an `identifier`. -/
def Identified (prompt : Prompt) : Prop := prompt.identified = true
/-- The bag carries a `description`. -/
def Described (prompt : Prompt) : Prop := prompt.described = true
/-- No argument name is declared twice. -/
def ArgumentsDistinct (prompt : Prompt) : Prop := prompt.argumentsDistinct = true

/-- Well-formedness is exactly the conjunction of the named clauses. -/
theorem wellFormed_iff (prompt : Prompt) :
    Prompt.WellFormed prompt ↔
      (Prompt.Identified prompt ∧ Prompt.Described prompt ∧
        Prompt.ArgumentsDistinct prompt) := by
  rw [Prompt.WellFormed, Prompt.check, firstRefusal_ok_iff]
  simp [Prompt.clauses, Prompt.Identified, Prompt.Described, Prompt.ArgumentsDistinct]

end Prompt

namespace McpServer

variable {refs : List ReferenceEntry}

/-- Clause: no two tools share a name. -/
def toolNamesDistinct (server : McpServer refs) : Bool :=
  namesUnique server.toolNames

/-- Clause: no two resources share a URI. -/
def resourceUrisDistinct (server : McpServer refs) : Bool :=
  namesUnique server.resourceUris

/-- Clause: no two prompts share a name. -/
def promptNamesDistinct (server : McpServer refs) : Bool :=
  namesUnique server.promptNames

/-- Clause (§15.2): the bag carries an `identifier`. -/
def identified (server : McpServer refs) : Bool := server.identifierOf.isSome

/-- Clause (§15.2): the bag carries a `description`. -/
def described (server : McpServer refs) : Bool := server.descriptionOf.isSome

/-- The server's own clauses, in the order a check reads them. -/
def clauses (server : McpServer refs) : List (Bool × Refusal) :=
  [ (server.toolNamesDistinct,
      .toolNameDuplicate server.name (firstDuplicate server.toolNames))
  , (server.resourceUrisDistinct,
      .resourceUriDuplicate server.name (firstDuplicate server.resourceUris))
  , (server.promptNamesDistinct,
      .promptNameDuplicate server.name (firstDuplicate server.promptNames))
  , (server.identified, .identifierMissing "mcpServer" server.name)
  , (server.described, .descriptionMissing "mcpServer" server.name) ]

/-- Check every tool, first refusal wins. -/
def checkTools (server : String) : List (Tool refs) → Except Refusal Unit
  | [] => .ok ()
  | tool :: rest =>
    match Tool.check server tool with
    | .error refusal => .error refusal
    | .ok _ => checkTools server rest

/-- Check every resource, first refusal wins. -/
def checkResources : List Resource → Except Refusal Unit
  | [] => .ok ()
  | resource :: rest =>
    match Resource.check resource with
    | .error refusal => .error refusal
    | .ok _ => checkResources rest

/-- Check every prompt, first refusal wins. -/
def checkPrompts : List Prompt → Except Refusal Unit
  | [] => .ok ()
  | prompt :: rest =>
    match Prompt.check prompt with
    | .error refusal => .error refusal
    | .ok _ => checkPrompts rest

/-- Check a server: its own clauses, then its tools, resources and prompts. -/
def check (server : McpServer refs) : Except Refusal Unit :=
  Except.bind (firstRefusal server.clauses) fun _ =>
    Except.bind (checkTools server.name server.tools) fun _ =>
      Except.bind (checkResources server.resources) fun _ =>
        checkPrompts server.prompts

/-- The proposition a capability opts into. -/
def WellFormed (server : McpServer refs) : Prop := McpServer.check server = .ok ()

instance (server : McpServer refs) : Decidable (McpServer.WellFormed server) := by
  unfold McpServer.WellFormed; infer_instance

/-- The Bool projection, for a battery or an emitter that wants one. -/
def wellFormed (server : McpServer refs) : Bool := decide (McpServer.WellFormed server)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (server : McpServer refs) :
    McpServer.wellFormed server = true ↔ McpServer.WellFormed server := by
  simp [McpServer.wellFormed]

/-- No two tools share a name. -/
def ToolNamesDistinct (server : McpServer refs) : Prop := server.toolNamesDistinct = true
/-- No two resources share a URI. -/
def ResourceUrisDistinct (server : McpServer refs) : Prop := server.resourceUrisDistinct = true
/-- No two prompts share a name. -/
def PromptNamesDistinct (server : McpServer refs) : Prop := server.promptNamesDistinct = true
/-- The bag carries an `identifier`. -/
def Identified (server : McpServer refs) : Prop := server.identified = true
/-- The bag carries a `description`. -/
def Described (server : McpServer refs) : Prop := server.described = true

/-- The tool walk succeeds exactly when every tool is well-formed. -/
theorem checkTools_ok_iff (server : String) :
    ∀ tools : List (Tool refs),
      checkTools server tools = .ok () ↔ ∀ tool ∈ tools, Tool.WellFormed server tool
  | [] => by simp [checkTools]
  | tool :: rest => by
    simp only [checkTools]
    cases answer : Tool.check server tool with
    | error refusal => simp [Tool.WellFormed, answer]
    | ok value =>
      cases value
      simp [Tool.WellFormed, answer, checkTools_ok_iff server rest]

/-- The resource walk succeeds exactly when every resource is well-formed. -/
theorem checkResources_ok_iff :
    ∀ resources : List Resource,
      checkResources resources = .ok () ↔
        ∀ resource ∈ resources, Resource.WellFormed resource
  | [] => by simp [checkResources]
  | resource :: rest => by
    simp only [checkResources]
    cases answer : Resource.check resource with
    | error refusal => simp [Resource.WellFormed, answer]
    | ok value =>
      cases value
      simp [Resource.WellFormed, answer, checkResources_ok_iff rest]

/-- The prompt walk succeeds exactly when every prompt is well-formed. -/
theorem checkPrompts_ok_iff :
    ∀ prompts : List Prompt,
      checkPrompts prompts = .ok () ↔ ∀ prompt ∈ prompts, Prompt.WellFormed prompt
  | [] => by simp [checkPrompts]
  | prompt :: rest => by
    simp only [checkPrompts]
    cases answer : Prompt.check prompt with
    | error refusal => simp [Prompt.WellFormed, answer]
    | ok value =>
      cases value
      simp [Prompt.WellFormed, answer, checkPrompts_ok_iff rest]

/--
Well-formedness is exactly the conjunction of the server's own clauses and the
well-formedness of everything it registers.
-/
theorem wellFormed_iff (server : McpServer refs) :
    McpServer.WellFormed server ↔
      (McpServer.ToolNamesDistinct server ∧ McpServer.ResourceUrisDistinct server ∧
        McpServer.PromptNamesDistinct server ∧ McpServer.Identified server ∧
        McpServer.Described server ∧
        (∀ tool ∈ server.tools, Tool.WellFormed server.name tool) ∧
        (∀ resource ∈ server.resources, Resource.WellFormed resource) ∧
        (∀ prompt ∈ server.prompts, Prompt.WellFormed prompt)) := by
  rw [McpServer.WellFormed, McpServer.check, exceptSeq_ok_iff, exceptSeq_ok_iff,
    exceptSeq_ok_iff, firstRefusal_ok_iff, checkTools_ok_iff server.name server.tools,
    checkResources_ok_iff server.resources, checkPrompts_ok_iff server.prompts]
  simp [McpServer.clauses, McpServer.ToolNamesDistinct, McpServer.ResourceUrisDistinct,
    McpServer.PromptNamesDistinct, McpServer.Identified, McpServer.Described, and_assoc]

/-- Every tool of a well-formed server is well-formed on it. -/
theorem wellFormed_tool (server : McpServer refs) (h : McpServer.WellFormed server)
    (tool : Tool refs) (mem : tool ∈ server.tools) :
    Tool.WellFormed server.name tool :=
  ((McpServer.wellFormed_iff server).mp h).2.2.2.2.2.1 tool mem

end McpServer

/-! ## Projections -/

/-- A present string, or JSON null. Every semantic field of the views below is
optional on the carrier and required in the payload, so the view spells the
absent case rather than dropping the key. -/
def optionalString : Option String → Json
  | some text => .str text
  | none => .null

/-- A representation as its persisted JSON, or null when it has none. The view
declares the slot `unknown` for the reason `Entity.json` does: the persisted
shape is the Schema representation's business, not this view's. -/
def persistedJson (representation : Representation) : Json :=
  (Arch.Representation.toJson? representation).getD .null

/-- The tool as a JSON value. -/
def Tool.json {refs : List ReferenceEntry} (tool : Tool refs) : Json :=
  .obj
    [ ("name", .str tool.name)
    , ("description", optionalString tool.descriptionOf)
    , ("parameters", persistedJson tool.parameters.rep)
    , ("success", persistedJson tool.success.rep)
    , ("failure", match tool.failure with
        | some schema => persistedJson schema.rep
        | none => .null) ]

/-- The resource as a JSON value. -/
def Resource.json (resource : Resource) : Json :=
  .obj
    [ ("uri", .str resource.uri)
    , ("name", .str resource.name)
    , ("description", optionalString resource.descriptionOf)
    , ("mimeType", optionalString resource.mimeType) ]

/-- One prompt argument as a JSON value. -/
def promptArgumentJson (argument : String × Bool) : Json :=
  .obj [("name", .str argument.1), ("required", .bool argument.2)]

/-- The prompt as a JSON value. -/
def Prompt.json (prompt : Prompt) : Json :=
  .obj
    [ ("name", .str prompt.name)
    , ("description", optionalString prompt.descriptionOf)
    , ("arguments", .arr (prompt.arguments.map promptArgumentJson)) ]

/-- The server as a JSON value: the view's payload. -/
def McpServer.json {refs : List ReferenceEntry} (server : McpServer refs) : Json :=
  .obj
    [ ("name", .str server.name)
    , ("version", .str server.version)
    , ("description", optionalString server.descriptionOf)
    , ("tools", .arr (server.tools.map Tool.json))
    , ("resources", .arr (server.resources.map Resource.json))
    , ("prompts", .arr (server.prompts.map Prompt.json)) ]

/-! ## The view -/

/-- A string or JSON null, the shape every optional semantic field takes in the
views below. -/
def nullableString : Representation :=
  Schema.anyOf Schema.string [Schema.null]

/-- The tool view's representation. -/
def mcpToolRep : Representation :=
  Schema.struct
    [ Schema.property "name" Schema.string
    , Schema.property "description" nullableString
    , Schema.property "parameters" Schema.unknown
    , Schema.property "success" Schema.unknown
    , Schema.property "failure" Schema.unknown ]

/-- The resource view's representation. -/
def mcpResourceRep : Representation :=
  Schema.struct
    [ Schema.property "uri" Schema.string
    , Schema.property "name" Schema.string
    , Schema.property "description" nullableString
    , Schema.property "mimeType" nullableString ]

/-- The prompt-argument view's representation. -/
def mcpPromptArgumentRep : Representation :=
  Schema.struct
    [ Schema.property "name" Schema.string
    , Schema.property "required" Schema.boolean ]

/-- The prompt view's representation. -/
def mcpPromptRep : Representation :=
  Schema.struct
    [ Schema.property "name" Schema.string
    , Schema.property "description" nullableString
    , Schema.property "arguments" (Schema.array (Schema.reference "McpPromptArgument")) ]

/-- The server view's representation. -/
def mcpServerRep : Representation :=
  Schema.struct
    [ Schema.property "name" Schema.string
    , Schema.property "version" Schema.string
    , Schema.property "description" nullableString
    , Schema.property "tools" (Schema.array (Schema.reference "McpTool"))
    , Schema.property "resources" (Schema.array (Schema.reference "McpResource"))
    , Schema.property "prompts" (Schema.array (Schema.reference "McpPrompt")) ]

/-- The agent-server view, for registration at `["surface", "mcp"]`. The
registration itself is `Effect4/Surface/Views.lean`'s and is not made here. -/
def mcpDoc : Document :=
  { representation := mcpServerRep
    references :=
      [ ⟨"McpTool", mcpToolRep⟩
      , ⟨"McpResource", mcpResourceRep⟩
      , ⟨"McpPromptArgument", mcpPromptArgumentRep⟩
      , ⟨"McpPrompt", mcpPromptRep⟩ ] }

/-! ## Content -/

/-- An agent server is addressed by the canonical bytes of its view payload. -/
instance {refs : List ReferenceEntry} : Canonical (McpServer refs) :=
  ⟨fun server => encode server.json⟩

/-! ## Anti-vacuity: the `shop` agent server over `shopDomain`

Every fixture carries its semantics, because §15.2 makes a row without one
ill-formed. Tool parameter schemas are deliberately annotation-free: §4.3's
JSON Schema ingest admits no annotation keywords, so an annotated parameter
object would not survive the `tools/list` round trip of
`Effect4/Surface/Agent/Emit.lean`, and the fixture is the thing that round trip
is `#guard`ed on.
-/

/-- An identified, described semantic bag, the shape §15.3's DSL will write.

Fixture-local: `Effect4/Surface/Api.lean` carries the same construction for its
own battery. One canonical spelling in `Annotate.lean` is owed before wave 3a's
DSL needs it (plan §13.6 rule 2). -/
private def describedBag (identifier description : String) : Annotations :=
  descriptionKey.append description (identifierKey.append identifier none)

/-- A kinded struct with no annotations of its own. -/
private def structOf (properties : List PropertySignature) : Representation :=
  Schema.struct properties

/-- The `get_user` tool: one text parameter, an entity as its result, a
declared failure. -/
def getUserTool : Tool shopDomain.refs where
  name := "get_user"
  parameters := ⟨structOf [Schema.property "id" Schema.string], by decide⟩
  success := ⟨Schema.reference "User", by decide⟩
  failure := some ⟨structOf [Schema.property "message" Schema.string], by decide⟩
  annotations := describedBag "get_user" "Fetch one shop customer by id."

/-- The `list_users` tool: no declared failure, an array result. -/
def listUsersTool : Tool shopDomain.refs where
  name := "list_users"
  parameters := ⟨structOf [Schema.property "limit" Schema.number true], by decide⟩
  success := ⟨Schema.array (Schema.reference "User"), by decide⟩
  failure := none
  annotations := describedBag "list_users" "List the shop's customers."

/-- The customers resource. -/
def usersResource : Resource where
  uri := "shop://users"
  name := "users"
  mimeType := some "application/json"
  annotations := describedBag "users" "Every customer of the shop, as JSON."

/-- The greeting prompt: one required and one optional argument. -/
def greetPrompt : Prompt where
  name := "greet_user"
  arguments := [("userId", true), ("tone", false)]
  annotations := describedBag "greet_user" "Greet a customer by name."

/-- The fixture agent server. -/
def shopServer : McpServer shopDomain.refs where
  name := "shop"
  version := "1.0.0"
  tools := [getUserTool, listUsersTool]
  resources := [usersResource]
  prompts := [greetPrompt]
  annotations := describedBag "shop" "The shop's agent surface."

/-- The fixture server is well-formed, by the kernel. -/
theorem shopServer_wellFormed : McpServer.WellFormed shopServer := by decide

/-- Its first tool is well-formed on it, by the kernel. -/
theorem getUserTool_wellFormed : Tool.WellFormed "shop" getUserTool := by decide

/-- And that clause is read off `wellFormed_iff` rather than decided again:
this is the shape a capability of §14.3 opts into. -/
theorem getUserTool_nameLegal : Tool.NameLegal getUserTool :=
  ((Tool.wellFormed_iff "shop" getUserTool).mp getUserTool_wellFormed).1

/-- Every tool of the fixture server is well-formed on it, by the law rather
than by a second `decide`. -/
theorem shopServer_tools_wellFormed :
    ∀ tool ∈ shopServer.tools, Tool.WellFormed shopServer.name tool :=
  ((McpServer.wellFormed_iff shopServer).mp shopServer_wellFormed).2.2.2.2.2.1

-- the grammar
#guard mcpToolName "get_user" = true
#guard mcpToolName "get-user" = true
#guard mcpToolName "A0" = true
#guard mcpToolName "" = false
#guard mcpToolName "get user" = false
#guard mcpToolName "get.user" = false
#guard mcpToolName "naïve" = false
#guard mcpToolName (String.ofList (List.replicate 64 'a')) = true
#guard mcpToolName (String.ofList (List.replicate 65 'a')) = false

-- the view accepts its own payload, and refuses a payload that is not one
#guard accepts mcpDoc shopServer.json = true
#guard accepts mcpDoc (.obj [("name", .str "shop")]) = false
#guard accepts mcpDoc getUserTool.json = false

-- the checks pass on the fixture
#guard McpServer.check shopServer == .ok ()
#guard Tool.check "shop" getUserTool == .ok ()
#guard Resource.check usersResource == .ok ()
#guard Prompt.check greetPrompt == .ok ()
#guard McpServer.wellFormed shopServer

-- one refusal per clause, each naming the clause and the name it failed on
#guard Tool.check "shop" { getUserTool with name := "get user" } ==
  .error (.toolNameIllegal "shop" "get user")
#guard Tool.check "shop" { getUserTool with annotations := none } ==
  .error (.identifierMissing "tool" "get_user")
#guard Tool.check "shop"
    { getUserTool with annotations := identifierKey.append "get_user" none } ==
  .error (.descriptionMissing "tool" "get_user")
#guard Resource.check { usersResource with annotations := none } ==
  .error (.identifierMissing "resource" "users")
#guard Resource.check
    { usersResource with annotations := identifierKey.append "users" none } ==
  .error (.descriptionMissing "resource" "users")
#guard Prompt.check { greetPrompt with annotations := none } ==
  .error (.identifierMissing "prompt" "greet_user")
#guard Prompt.check
    { greetPrompt with annotations := identifierKey.append "greet_user" none } ==
  .error (.descriptionMissing "prompt" "greet_user")
#guard Prompt.check { greetPrompt with arguments := [("userId", true), ("userId", false)] } ==
  .error (.promptArgumentDuplicate "greet_user" "userId")
#guard McpServer.check { shopServer with tools := [getUserTool, getUserTool] } ==
  .error (.toolNameDuplicate "shop" "get_user")
#guard McpServer.check { shopServer with resources := [usersResource, usersResource] } ==
  .error (.resourceUriDuplicate "shop" "shop://users")
#guard McpServer.check { shopServer with prompts := [greetPrompt, greetPrompt] } ==
  .error (.promptNameDuplicate "shop" "greet_user")
#guard McpServer.check { shopServer with annotations := none } ==
  .error (.identifierMissing "mcpServer" "shop")
#guard McpServer.check
    { shopServer with annotations := identifierKey.append "shop" none } ==
  .error (.descriptionMissing "mcpServer" "shop")

-- a refusal inside a registered value reaches the server's check
#guard McpServer.check { shopServer with tools := [{ getUserTool with name := "x y" }] } ==
  .error (.toolNameIllegal "shop" "x y")
#guard McpServer.check { shopServer with resources := [{ usersResource with annotations := none }] } ==
  .error (.identifierMissing "resource" "users")
#guard McpServer.check { shopServer with prompts := [{ greetPrompt with annotations := none }] } ==
  .error (.identifierMissing "prompt" "greet_user")

-- semantics are read off the bag, and nowhere else
#guard getUserTool.descriptionOf == some "Fetch one shop customer by id."
#guard usersResource.descriptionOf == some "Every customer of the shop, as JSON."
#guard shopServer.descriptionOf == some "The shop's agent surface."
#guard (Tool.descriptionOf { getUserTool with annotations := none }) == none

end Effect4.Surface
