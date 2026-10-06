# The reusable TypeScript library and compiler boundary

Recommend consolidating the compiler client first. Keep the pure Lean syntax library independent from compiler processes and Effect4 policy.

Evidence status: source inspection only. No compiler, Lean, build, generator, installation, target execution, or repository edit ran.

## Verified package

The installed `lean4-typescript` is clean at `f5878bf879bd5712db964c2cd12802748c707605`, version 0.7.0.
Its origin is `https://github.com/pure-algebra/lean4-typescript`. Effect4's manifest selects that exact revision.
The observed Effect4 head begins at `33a39ca4192079af788e2df2932cce0d7c8103fd`; the receipt records the final head too.

The package has no Lake dependencies. Its modules provide syntax, rendering, identifier predicates, host pins, and a control-flow structurer.
There is no compiler invocation, parser, source-position model, diagnostic model, or TypeScript typechecker interface in its source inventory.

`TypeRef` stores names, arguments, literals, tuples, unions, fields, and function types as data.
`Expr`, `Stmt`, `Import`, and `Module` preserve the distinctions the Effect4 printer currently needs.
`Render.type`, `Render.expr`, `Render.stmt`, and `Render.module` write deterministic fixed-layout source.
`targetIdentifier` and `qualifiedIdentifier` provide a deliberately narrow generated-name profile.

`TypeRef.beq_iff` proves structural equality reflection. The package pins its expected axiom output to `[propext]` in `TypeScriptTest/ObjectForms.lean`.
The expression and statement equality procedures are structural, total source definitions; they do not establish TypeScript typing or execution.
Several older renderer smoke examples use `native_decide`. Their finite result is not a renderer-correctness or target-semantics theorem.
No source parser, general renderer retraction theorem, or TypeScript semantic model appears in this package.

The carrier admits invalid or noncanonical TypeScript. For example, an empty union renders as `never`, and type-only import markers normalize.
The README explicitly assigns grammatical admission and exactness to consumers. Preserve that distinction in any compiler API.

## Recommended ownership

| Surface | Reusable owner | Effect4 owner |
| --- | --- | --- |
| Syntax and rendering | Existing `lean4-typescript` carriers and renderer | `Eff` printing, record choices, Forms expansions, annotation interpretation |
| Compiler process/session | Optional host-side client beside the library | Gate scheduling and the selected Effect4 compiler policy |
| Compiler request/result data | Generic protocol with explicit project inputs and operations | Effect A/E/R extraction and consumer-specific query generation |
| Diagnostics and source locations | Lossless compiler records with source identity and offset convention | Whether a diagnostic means refusal, mismatch, or an accepted control |
| Compiler configuration | Selected config, resolved options, roots, dependency inputs, compiler identity | The project's exact tsgo pin and accepted options |
| Parsing queries | Small data projections from the selected parser/compiler | Effect recognition, normalization, printer-image restrictions and refusal codes |
| Lexical name resolution | Existing small binding algebra is a possible later extraction | Permitted Effect origins, ambient names and the admitted source profile |

Use an optional host-side module or sibling package for Node-specific machinery. Keep it out of the pure syntax library's default import/build path.
A second published package name is not needed before its packaging decision. One reusable component can first serve the existing consumers in place.

## First useful slice: one compiler session and result contract

Concrete consumers are `tools/target/checker.ts` and the tsgo branch of `ts/eff/check-styles.ts`.
Both construct virtual projects and query compiler diagnostics. Their policies differ, so share the mechanism and preserve each policy.

The existing `oracle.ts` already separates serializable requests from the Node compiler process. Extend this seam rather than introducing another transport.

A request needs a schema version, request identity, selected operation, project/config identity, explicit sources and options.
A result needs the matching identity, actual compiler identity, resolved inputs/options, diagnostics, requested observations, and a distinct process/protocol outcome.
Keep compiler diagnostics separate from missing files, failed process startup, malformed responses, and unsupported queries.

Require exact requested-versus-attempted source or query coverage. An empty or partial success response cannot satisfy a nonempty request.
Bind source and configuration bytes to the result. Include the selected library/package inputs; identical source text under another environment is another check.

Existing useful functions: `open` and `compilerVersion` in `checker.ts`; transport `run` in `oracle.ts`; the exact source-set check in `check-styles.ts`.
The current Node requirement is real in this pinned client. Do not merge Bun and Node execution merely to remove a subprocess.

Small verification plan for the implementation owner: preserve each consumer's current positive output, then plant one missing source, wrong compiler, and malformed response.
A known invalid program must remain a compiler diagnostic, while a failed compiler process must remain infrastructure failure.
This slice produces finite compiler evidence. It proves no Lean-to-TypeScript semantic theorem.

Do not add a Lean mirror of every compiler result yet. No current Lean consumer of these JSON report formats appeared in the inspected source.
Design the schema now; add a Lean decoder when a named Lean-facing report consumer arrives.

## Second useful slice: lossless diagnostics and honest locations

The native preview's `Diagnostic` exposes file, start/end positions, code, category, text, message chains and related information.
The present `oracle.ts` projection keeps code, file, line, column and flattened message only.
The styles check retains start/end positions in text, through a separate presentation.

Preserve the richer record in the shared boundary. Derive the existing concise display afterward, without discarding the original evidence.
Use an optional source file/span for global diagnostics. Avoid pretending a synthetic file and line zero are ordinary source locations.

Name the offset convention. The installed declaration only labels start/end positions; it does not document their unit there.
`checker.ts` currently computes columns through JavaScript string slicing and explicitly limits its report to ASCII query modules.
Do not silently widen that claim. The first Unicode extension needs CRLF, BMP and supplementary-character controls against the chosen compiler API.
Retain raw offsets even when a presentation conversion is unavailable.

Consumer: both existing diagnostic outputs and later compiler-backed source navigation. This is a bounded normalization improvement, not a full source-map engine.

## Third useful slice: small generic query operations

Keep syntax-only parsing, type queries, and assignment tests as distinct requested operations.
`subjectReceivers` already needs one narrow parser projection: the object part of an indexed-access type.
The pair oracle already needs two generic facts: the checker's assignability answer and the result of an actual assignment statement.
Keep both; the existing `Direction` deliberately records them separately.

Return data, not remote compiler objects. Compiler `Node`, `Type`, and snapshot handles must not become stored Lean program syntax or durable report identities.
Use stable request-local selection keys and explicit missing/ambiguous results for named declarations.
Keep `typeToString` as presentation data. Text equality must not replace an assignment or checker relation.

Effect4 retains `Query.kind`, A/E/R extraction, request/receiver axes, unknown contamination policy, handle binding injectivity, and conformance classification.
Its `pairImports` import Effect-specific types; they stay local even if the bare pair comparison becomes generic.

Do not port the full oxc tree or all compiler types into `TypeScript.Expr`.
The existing `parseTypeScript` in `ts/eff/ingest/oxc.ts` owns TS versus TSX selection; its callers own recognition.
Rows 168 and 247 already distinguish parser use from compiler use and permit a syntax-package extension when a construct needs one.
Consolidation does not require replacing the selected parser or treating two walks over one parse as independent parsers.

## A small later Lean-library extraction

`Effect4.Codegen.Bindings` imports only `TypeScript.Syntax` and `TypeScript.Identifier`.
Its `Space`, `Origin`, `Binding`, `ofImport`, `resolve`, and `lawfulImports` are generic source-binding operations.
Its laws in `Effect4/Laws/Codegen/Bindings.lean` state nearest-name resolution, type-only refusal, import preservation and lawful import checks.

If a second consumer needs this exact lexical policy, extract that small algebra with its laws and compatibility wrappers.
Consumer today: `Codegen.SourceBindings`, then public `Api.checkSourceBindings`. Preserve their exact results during any move.
The nearest unavailable name must continue to block an outer binding. Keep type-only and alias controls beside the extracted implementation.

Do not move the entire source checker now. It uses Effect4 name policy, UTF-8 decoding, renderer-introduced names, and the admitted syntax fragment.
`Codegen.Admit` also reconstructs `Eff`, checks formation and typing, compares declarations, and verifies Effect-specific origins.
Those are Effect4's judgments. A generic compiler client must not weaken or replace them.

The existing syntax carrier also has legacy Effect convenience nodes, including scoped generators and effectful fields.
Preserve compatibility; do not use their presence as a reason to place new Effect-specific compiler policy in the shared package.
Their removal is outside this consolidation and has no demonstrated immediate consumer.

## Pins and profiles

`HostPin` is header data, not a verified tool identity. Its fields are `typescript`, optional language service, runtime, and library strings.
Its compiler comment still mentions `tsc --version`. Add an explicit compiler package/version/entrypoint identity if compiler receipts reuse it.
Keep declared pins separate from observed installed tools and actual configuration. Compare them in the client; do not merely print them.

`Tools.TsGen.hostPin` remains an existing header/address consumer. Preserve its output until an explicit migration updates the relevant generated group.

Keep three profiles separate: represented syntax, compiler language/options, and Effect4's admitted semantic fragment.
Do not add one global feature flag record pretending to decide all three. Add a capability only for a concrete syntax or query consumer.

## Proof and evidence placement

The existing `Api.checkSourceBindings_iff` connects the lexical checker to `SourceBindings.WellBound`.
It establishes lexical resolution only, not package exports, TypeScript typing or execution.
`Api.admitModule_emitModule` and `ModuleEmission.readModule` relate checked Effect4 construction and the module AST on their stated readable domains.
They do not reach compiler diagnostics or host behavior.

A compiler-client refactor initially needs schema, coverage, identity and mutation controls. Do not manufacture a semantic proof goal for a passive protocol alphabet.
If extracting the binding algebra, preserve the existing exact statements and their consumers before adding any new theorem.
If later claiming compiler-backed admission, place that claim in translation-simulation with its exact profile, version and external-oracle assumption first.
The seven judgments remain separate. A compiler's successful report is not by itself membership, codec admission or reply admission.

## Recommended sequence

1. Freeze the shared request/result boundary, then move session opening and diagnostic collection behind it for the two named consumers.
2. Preserve diagnostic structure and source/configuration identity, including failure outputs and exact coverage checks.
3. Extract only the current parser projection and bare assignability operation; retain Effect-specific query construction locally.
4. Move the small binding algebra only when a second consumer needs its exact policy.

Defer a complete TypeScript AST port, semantic type-model mirror, universal profile framework, and broad binding-checker migration.
No current observation justifies those costs. The boundaries above leave room for planned consumers without requiring them now.
