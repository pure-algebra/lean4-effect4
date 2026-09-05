# Surface agent (MCP) contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.5)

Implementation (owed): `src/Effect4/Surface/Agent.lean`

Battery: `Test/Surface/AgentContract.lean`

Counterexamples: `E4-SURFACE-CE-038` through `E4-SURFACE-CE-042`,
`E4-SURFACE-CE-066`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet.

Witnesses: `Test/Counterexamples/Surface/Agent.lean`

Pins: rc.112 `unstable/ai/Tool.ts:1204`,
`unstable/ai/McpServer.ts:1609, 1882, 2106`

## Purpose

The MCP boundary as rows: tools with a parameter struct, a success schema and
an optional failure schema; resources by URI; prompts by name. The
distinguishing constraint of this surface is that MCP names are a wire
alphabet with a published regular expression, so the name check is a modeled
law rather than a target-identifier convention.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
structure Tool (refs : List Effect4.ReferenceEntry) where
  name        : String
  annotations : Effect4.Annotations := none
  parameters  : Sch refs .struct
  success     : Sch refs .json
  failure     : Option (Sch refs .json) := none

structure Resource where
  uri         : String
  name        : String
  annotations : Effect4.Annotations := none
  mimeType    : Option String := none
deriving DecidableEq

structure Prompt where
  name        : String
  annotations : Effect4.Annotations := none
  arguments   : List (String × Bool) := []
deriving DecidableEq

structure McpServer (refs : List Effect4.ReferenceEntry) where
  name        : String
  version     : String
  annotations : Effect4.Annotations := none
  tools       : List (Tool refs)
  resources   : List Resource := []
  prompts     : List Prompt := []

def Tool.nameLegal (name : String) : Bool
def Tool.description {refs} : Tool refs → Option String
def Resource.description : Resource → Option String

def Tool.check {refs} (t : Tool refs) : Except Refusal Unit
def Tool.WellFormed {refs} (t : Tool refs) : Prop := Tool.check t = .ok ()

def Resource.check (r : Resource) : Except Refusal Unit
def Resource.WellFormed (r : Resource) : Prop := Resource.check r = .ok ()

def McpServer.check {refs} (s : McpServer refs) : Except Refusal Unit
def McpServer.WellFormed {refs} (s : McpServer refs) : Prop :=
  McpServer.check s = .ok ()

def Tool.Named {refs} (t : Tool refs) : Prop
def Tool.Described {refs} (t : Tool refs) : Prop
def McpServer.ToolNamesDistinct {refs} (s : McpServer refs) : Prop
def McpServer.ResourceUrisDistinct {refs} (s : McpServer refs) : Prop
def McpServer.PromptNamesDistinct {refs} (s : McpServer refs) : Prop

theorem Tool.wellFormed_iff {refs} (t : Tool refs) :
    Tool.WellFormed t ↔ (Tool.Described t ∧ Tool.Named t)

theorem McpServer.wellFormed_iff {refs} (s : McpServer refs) :
    McpServer.WellFormed s ↔
      (McpServer.ToolNamesDistinct s ∧ McpServer.ResourceUrisDistinct s ∧
        McpServer.PromptNamesDistinct s ∧
        (∀ t ∈ s.tools, Tool.WellFormed t) ∧
        (∀ r ∈ s.resources, Resource.WellFormed r))

def McpServer.toolkitModule {refs} (s : McpServer refs) (dom : Domain) :
    Option TypeScript.Module
def McpServer.toolsListJson {refs} (s : McpServer refs) : Option Effect4.Json
```

## Observations

1. `Tool.nameLegal n : Bool`, over a small alphabet of hostile names.
2. `Tool.check t` and `McpServer.check s`, `Except Refusal Unit`, compared
   against `.ok ()` or an exact `.error` value.
3. `McpServer.toolsListJson s : Option Json`, compared against a literal
   `Json` term for the fixture server, so the key order and the
   `inputSchema` spelling are both pinned.
4. `McpServer.toolkitModule s dom : Option Module`, `isSome` in this packet.

## Acceptance conditions

- `Tool.nameLegal` decides `^[A-Za-z0-9_-]{1,64}$` exactly. The empty name is
  refused, a 64-character name is admitted, a 65-character name is refused
  (`E4-SURFACE-CE-039`), and any character outside `[A-Za-z0-9_-]` is refused,
  including `.`, `/`, a space and a non-ASCII letter (`E4-SURFACE-CE-038`).
  The check is on the string's characters, not on its UTF-8 byte length.
- `Tool.check` clause order: `identifier` on the bag
  (`identifierMissing "tool" t.name`); `description` on the bag
  (`descriptionMissing "tool" t.name`, `E4-SURFACE-CE-066`); the MCP name
  (`toolNameIllegal t.name`). An MCP client shows a tool's description to a
  model, so a tool with none is unusable in the way §15.2 means: a surface
  value with no meaning is ill-formed.
- `Resource.check`: `identifier` then `description`
  (`identifierMissing "resource" r.name`, `descriptionMissing "resource"
  r.name`).
- `McpServer.check` clause order: tool names distinct
  (`toolNameDuplicate s.name n`, `E4-SURFACE-CE-040`); resource URIs distinct
  (`resourceUriDuplicate s.name uri`, `E4-SURFACE-CE-041`); prompt names
  distinct (`promptNameDuplicate s.name n`, `E4-SURFACE-CE-042`); every
  tool's `check`; every resource's `check`.
- `toolsListJson` produces `{ "tools": [ { "name", "description",
  "inputSchema" } ] }` in tool declaration order, with `inputSchema` the
  `toJsonSchema` of the parameter struct (`surface-jsonschema.contract.md`)
  and the description read from the annotation bag through the `description`
  key of §15.1, never from a field on the carrier (plan §15.3). It answers
  `none` exactly when some parameter struct has no JSON Schema spelling. A
  well-formed tool always has a description, so the omitted-description branch
  is reachable only from an ill-formed value and the battery pins it there.
- `toolkitModule` spells `Tool.make("<name>", { description, parameters,
  success, failure })`, `Toolkit.make(…)`, `McpServer.toolkit(…)` and
  `McpServer.resource({...})` at the pinned lines. Import lines cover exactly
  what is used.

## Assurance allocation

Leaf receipts plus two emitter rules on the `SURFACE-PG-EMIT` graph.

The carriers are passive records; `Tool.nameLegal` is a decidable predicate on
a finite alphabet and closes with its census. The two rules
`surface.mcp.toolkit` and `surface.mcp.toolsList` land `Stance.emitted`; the
receipt that flips `mcpToolsList` is the `tools/list` response of a running
`McpServer.layerStdio` at the pin, and if that is not feasible in the landing
packet the rule stays `emitted` with a typecheck-only receipt recorded as such.

## What this contract does not claim

It does not claim an emitted toolkit answers any request; there is no run
agreement here. It does not model MCP sampling, roots, notifications,
progress, or resource templates. It does not claim `toolsListJson` is the
whole MCP `tools/list` response envelope: it is the `tools` array and its
wrapper object, with no `nextCursor` and no JSON-RPC frame.
