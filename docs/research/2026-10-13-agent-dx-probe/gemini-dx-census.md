# 2026-10-13 Census: where the agent's authoring surface stands

Status: research note.
Base: HEAD of `refactor/phase1-phase3`.
Author: Gemini agent.

Row 307 (4) of `docs/core/decisions.md` rules the first authoring path.
An agent operates through data operations behind an MCP wrapper.
This note records the head status of thirty-four planned items.

## List A: Fixes that change the API

These ten items come from `docs/research/2026-10-12-probe-api-usability.md`.

| # | Item | Status | Details |
| --- | --- | --- | --- |
| 1 | Render functions for `ExitV`, `TypeRefusal` and `BuildRefusal` | **absent** | Searched `ExitV.render`, `TypeRefusal.render`, `BuildRefusal.render` across `src/`, `tools/`, `Test/`. `ExitV` in `src/Effect4/Machine/Exit.lean`, `TypeRefusal` in `src/Effect4/Program/Typing/Blame.lean`, and `BuildRefusal` in `src/Effect4/Api/Author.lean` lack render functions. `Test/Audit/AxiomGate.lean` exempts only `Ty.render` and codegen string renderers. |
| 2 | `Built.runToEnd`, and `commandFuel` kept in `Run.inspect` | **absent** | Searched `runToEnd` and `commandFuel` in `src/` and `tools/`. `Built.runToEnd` does not exist in `src/Effect4/Api/Author.lean`. `Run.inspect` in `src/Effect4/Run/Basic.lean` delegates to `Api.HostSession.inspect` in `src/Effect4/Api/HostSession.lean`. That function replays at zero fuel and reports `awaitDecision`. |
| 3 | Forms `catchAll`, `mapError`, `orElse`, `timeoutFail` and `retryTimes` | **absent** | Searched `catchAll`, `mapError`, `orElse`, `timeoutFail`, `retryTimes` in `src/Effect4/Codegen/Forms.lean` and `src/Effect4/Codegen/Authoring/Forms.lean`. In `src/Effect4/Codegen/Forms.lean`, `duals` lists names without expansions. `src/Effect4/Codegen/Authoring/Forms.lean` declares none of these forms. |
| 4 | An `atom` alternative in `TermTypingRefusal` | **absent** | Searched `atom` in `src/Effect4/Program/Typing/TermRefusal.lean`. `TermTypingRefusal` in `src/Effect4/Program/Typing/TermRefusal.lean` declares only `record`, `tuple`, and `fold`. |
| 5 | `Built.runSync` refusing a program that is not closed | **absent** | Examined `Built.runSync` in `src/Effect4/Api/Author.lean`. `Built.runSync` in `src/Effect4/Api/Author.lean` returns `ExitV` directly via `b.typed.runSync budget`. It does not inspect `Built.closed` and returns no `Except` refusal. |
| 6 | `Typed.emitText` with the import header | **absent** | Searched `emitText` across `src/Effect4/Api.lean` and `src/Effect4/Codegen/Checked.lean`. `Typed.emit` in `src/Effect4/Api.lean` produces `ModuleEmission`, which prints syntax without import headers. No declaration named `Typed.emitText` exists. |
| 7 | `ServiceDef.of` and a `reservedName` reason | **absent** | Searched `ServiceDef.of` and `reservedName` in `src/Effect4/Program/Authoring.lean` and `src/Effect4/Api/Author.lean`. `ServiceDef` in `src/Effect4/Program/Authoring.lean` has no `ServiceDef.of` constructor. `BuildRefusal` in `src/Effect4/Api/Author.lean` has no dedicated `reservedName` constructor. |
| 8 | The alias `Schema.Codec.decode` and a located `decodeAt` | **absent** | Searched `Codec.decode` and `decodeAt` in `src/Effect4/Schema/Codec.lean`. `Effect4.Schema.decode` is declared in `src/Effect4/Schema/Codec.lean`, but not as `Schema.Codec.decode`. No located `decodeAt` returning a path and reason exists for schemas. |
| 9 | `ExitV` and `Val` exported into `Effect4.Program.Authoring` | **absent** | Searched exports of `ExitV` and `Val` in `src/Effect4/Program/Authoring.lean` and `src/Effect4/Program/Authoring/*.lean`. Neither name is exported into `Effect4.Program.Authoring`. They remain in `Effect4.Machine` and `Effect4.Api`. |
| 10 | The alias `Built.emit` and a minted `Forms.matchCauseWith` | **absent** | Searched `Built.emit` in `src/Effect4/Api/Author.lean` and `matchCauseWith` in `src/Effect4/Codegen/Authoring/Forms.lean`. `Built` in `src/Effect4/Api/Author.lean` has no `emit` projection. `src/Effect4/Codegen/Authoring/Forms.lean` does not declare `matchCauseWith`. |

## List B: The eleven tools of §3

These eleven tools come from `docs/research/2026-10-08-agent-authoring.md` §3.

| Tool | Status | Details |
| --- | --- | --- |
| `find` | **absent** | Searched `#find`, `elabFind`, `find` in `src/Effect4/Laws/Author/` and `tools/`. No query command over the registry and implementation map exists. |
| `explain` | **landed** | Commands `#explain`, `#explain_json`, and `#explain_schema` in `src/Effect4/Laws/Author/Explain.lean`. Declared as `Tools.Explain.elabExplain` in `src/Effect4/Laws/Author/Explain.lean`. Reports kind, type, placement, claims, standing, step facts, and statement dependencies. |
| `run model` | **absent** | Searched `runModel`, `run_model` in `tools/` and `src/Effect4/`. No command evaluates model steps into decoded Lean values. |
| `explore` | **absent** | Searched `#explore`, `elabExplore` in `src/` and `tools/`. No bounded model exploration tool exists. |
| `derive` | **absent** | Searched `derive_step` across `src/` and `tools/`. It existed only in research probe `docs/research/2026-10-08-agent-authoring/DeriveProbe.lean`. Row 375 (7) of `docs/core/decisions.md` records that it is not in the tree. |
| `module` | **absent** | Searched `eff_module` and `module mirrors` in `src/Effect4/Program/Authoring/` and `tools/`. Row 375 (7) of `docs/core/decisions.md` and `docs/core/api-surface.md` record that the module form is not in the tree. |
| `obligations` | **landed** | Commands `#obligations` and `#obligations_json` in `src/Effect4/Laws/Author/Explain.lean`. Declared as `Tools.Explain.elabObligations` in `src/Effect4/Laws/Author/Explain.lean`. Reports proved, modulo, and goal counts, statements, and placement under a namespace. |
| `prove` | **absent** | Searched `#prove`, `elabProve` in `src/` and `tools/`. `ProofGraph.search` in `tools/ProofGraph/Search.lean` is speculative tactic search for meta code, not an agent command. |
| `compare` | **absent** | Searched `#compare`, `elabCompare` in `src/` and `tools/`. Conformance runners exist in `tools/Conform/` and `scripts/check-conform.py`, but no agent tool `compare` exists. |
| `impact` | **absent** | Searched `#impact`, `elabImpact` in `src/` and `tools/`. No footprint impact analysis tool exists. |
| `report` | **absent** | Searched `#report`, `elabReport` in `src/` and `tools/`. No module reporting command exists. |

## List C: The slices M0 to M12

These slices come from `docs/research/2026-10-09-mcp-code-mode-design.md` §10.1.

| Slice | Status | Details |
| --- | --- | --- |
| M0 | **absent** | Searched `schema/2026-07-28` in `vendor/`. `vendor/` holds Effect's internal schemas, but the official MCP specification repository is not vendored. |
| M1 | **absent** | Searched `Op` in `tools/Effect4Gen/manifest.json` and `tools/Tools/Session.lean`. `Tools.Session.Request` in `tools/Tools/Session.lean` remains a flat record with string operation names. `Tools.Query.Answer` in `tools/Tools/Query.lean` keeps untyped JSON. |
| M2 | **absent** | Searched `tools/Drivers/McpGen.lean`, `generated/mcp/`, and `schemaOf` in `src/Effect4/Store/Domain/`. `schemaOf` exists only in research probe `docs/research/2026-10-09-mcp-code-mode/ShapeSchemaProbe.lean`. |
| M3 | **absent** | Searched `server/discover` and MCP executable entries in `lakefile.toml` and `tools/Drivers/`. No MCP stdio server executable exists. |
| M4 | **partial** | Exists: store roots with version compare-and-set exist as `Store.putRoot`, `Store.Root`, and `putRoot_root?` in `src/Effect4/Store/Domain/Store.lean`. Missing: `Content` instances for `NativeEff` and `Sketch` in `src/Effect4/Store/Domain/Derived/Program.lean`. Missing: commit store nodes in `src/Effect4/Store/Carrier/Kind.lean`. Missing: tool `edit.apply` in `tools/Tools/Session.lean`. |
| M5 | **partial** | Exists: single edits (`Edit.fill`, `Edit.omitAt`) and session execution (`EditSession.feed`, `EditSession.run`, `EditSession.feedStep`) in `src/Effect4/Program/Edit.lean`. Missing: edit script data type, hole-name targeting, reduction of actions to edits, dry run, and refusal by operation index. |
| M6 | **absent** | Searched `builders.gen.ts` and `mcp.gen.ts` in `ts/eff/`. `ts/eff/` contains `eff.gen.ts` and `wire.gen.ts`, but neither `builders.gen.ts`, `mcp.gen.ts`, state API resources, nor tsgo snippet batteries exist. |
| M7 | **absent** | Searched `piece.put`, `usePiece`, `search.type` across `src/`, `tools/`, `Test/`. Neither piece storage tools nor type search tools exist. |
| M8 | **absent** | Searched `presence.set`, `subscriptions`, and script rebase in `tools/Tools/Session.lean`. Path rebase theorems `Checker.check_rebase` and `tableAt_rebase` exist in `src/Effect4/Laws/Program/Typing/Rebase.lean`. Multi-agent session rebasing, presence, and subscriptions do not exist. |
| M9 | **partial** | Exists: the host session face landed as `Live.open`, `Live.start`, `Live.feed`, and `Live.view` in `src/Effect4/Run/Live.lean` and `src/Effect4/Run/View.lean`. Missing: MCP tools `run.start`, `run.feed`, `run.view`, and MCP tasks extension support. |
| M10 | **absent** | Searched `McpServer` and Unix socket servers in `ts/`, `harness/`, and `tools/`. `McpServer` exists only in vendored Effect in `vendor/effect-4.0.1/src/ai/McpServer.ts`. No local HTTP front exists. |
| M11 | **absent** | Searched `@[export]` and `C ABI` in `src/` and `tools/`. No exported C ABI function over canonical bytes exists. |
| M12 | **partial** | Exists: `Effect4.Program.Package` structure in `src/Effect4/Program/Authoring.lean`. Missing: translation from tool lists into packages, and server generation from module operations. |

## Authoring `programJson` from scratch

The owner asks whether an agent could write a new program's `programJson` from scratch with no Lean.

### Can an agent author `programJson` without Lean?

Yes.
`Tools.Session.programOfJson` in `tools/Tools/Session.lean` reads `programJson` through `Tools.JsonBridge.ofLeanJson` and `Canonical.ofJsonAnyOrder`.
`Canonical.ofJsonAnyOrder` accepts plain JSON objects where sum types carry a `_tag` property.
An agent can construct this JSON directly in any language.

### What an agent reads to learn the shape

An agent must read three sources:

1. `ts/eff/eff.gen.ts`: declaration `export type Eff` defines `Eff` as a TypeScript tagged union. The auxiliary types `Term`, `Lit`, `NativeOp`, `DefDecl`, `Stmt`, `ActionTerm`, and `LayerTerm` define every valid child node.
2. `src/Effect4/Store/Domain/Derived/Program.lean`: declaration `EffShape` in namespace `EffC` defines the canonical shape. It lists the canonical tag string and field names for every constructor.
3. `Test/fixtures/session/requests.jsonl`: the `fill` request fixture provides an example of `replacementJson`. It demonstrates `succeed` with a literal natural number.

### Publication of the shape: schema, grammar, or examples?

The tree does not publish a JSON Schema for `programJson`.
Probe MCP-1 in `docs/research/2026-10-09-mcp-code-mode/ShapeSchemaProbe.lean` generated a schema, but slice M2 has not landed.
The tree publishes no formal grammar for `programJson`.
Instead, the tree publishes:

- TypeScript type definitions and Effect Schemas in `ts/eff/eff.gen.ts`.
- Lean shape definitions in `src/Effect4/Store/Domain/Derived/Program.lean`.
- Finite example requests in `Test/fixtures/session/requests.jsonl`.

An external agent without Lean must use `ts/eff/eff.gen.ts` as its shape specification.
