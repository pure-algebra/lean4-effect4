# Step A — the move to the D20 tree (mechanical plan)

Parent: `docs/research/2026-09-04-api-design-review.md` §6–7. One commit, gate green. Nothing
semantic changes: files move, module names and app-level namespaces change, declaration
names of the machine layer do not.

## A.1 Directory map (`git mv`)

| today | after |
| --- | --- |
| `Effect4.lean` | `src/Effect4.lean` |
| `Effect4/Api.lean` | `src/Effect4/Api.lean` |
| `Effect4/Data/{Json,Row,Optic}.lean` | `src/Effect4/Data/…` |
| `Effect4/Schema/{Payload,Representation,Annotations,Document,Check,Authoring,EffectfulField}.lean` | `src/Effect4/Schema/…` |
| `Effect4/Schema/{Codec,Value,Foreign,Registry,Getter,Transformation}.lean` | `src/Effect4/Schema/Pins/…` |
| `Effect4/Arch/Accepts.lean` | `src/Effect4/Schema/Accepts.lean` |
| `Effect4/Arch/JsonCanonical.lean` | `src/Effect4/Store/JsonCanonical.lean` |
| `Effect4/Store/{Canonical,Digest,Trie,Store,Pin}.lean` | `src/Effect4/Store/…` |
| `Effect4/Surface/{Kind,Facts,Annotate,Entity,Api,Agent,Deploy,Site}.lean` | `src/Effect4/Surface/…` (`Facts` → `Refusal.lean`) |
| `Effect4/Surface/Spell.lean` | `src/Effect4/Codegen/Spell.lean` |
| `Effect4/Surface/JsonSchema.lean` | split: `src/Effect4/Codegen/JsonSchema.lean` (`toJsonSchema`, `Document.jsonSchema`, `Entity.jsonSchema`) and `src/Effect4/Ingest/JsonSchema.lean` (`ofJsonSchema`) |
| `Effect4/Surface/Api/Emit.lean` | `src/Effect4/Codegen/HttpApi.lean` |
| `Effect4/Surface/Agent/Emit.lean` | `src/Effect4/Codegen/Mcp.lean` (emitters) + `src/Effect4/Ingest/Mcp.lean` (`ofMcpToolsList`, `toolOfJson`, `toolsOfJson`) |
| `Effect4/Surface/Deploy/Emit.lean` | `src/Effect4/Codegen/Worker.lean` (emitters) + `src/Effect4/Ingest/Wrangler.lean` (`ofWrangler`) |
| `Effect4/Surface/Emit.lean` | `src/Effect4/Codegen/Rules.lean` |
| `Effect4/Surface/Views.lean` | `src/Effect4/Evidence/SurfaceViews.lean` |
| `Effect4/Target/TypeScript/Schema.lean` | `src/Effect4/Codegen/Schema.lean` (`reifyJson?` → `src/Effect4/Ingest/ReifyJson.lean`) |
| `Effect4/Target/TypeScript/EffectfulField.lean` | `src/Effect4/Codegen/EffectfulField.lean` |
| `Effect4/Target/TypeScript/EffectV4.lean` | `src/Effect4/Codegen/Profile.lean` (`Spelling` and its `render/depth/arity/admitted` → `src/Effect4/Program/Ty.lean`) |
| `Effect4/Syntax/{Eff,Typing,Native,Compile}.lean` | `src/Effect4/Program/{Eff,Typing,Native,Compile}.lean` |
| `Effect4/Syntax/Print.lean` | `src/Effect4/Codegen/Print.lean` |
| `Effect4/Syntax/Read.lean` (A4, when it lands) | `src/Effect4/Ingest/Read.lean` |
| `Effect4/Semantics/{Cause,Exit}.lean` | `src/Effect4/Machine/{Cause,Exit}.lean` |
| `Effect4/Concurrency/{Fiber,Supervision}.lean` | `src/Effect4/Machine/{Fiber,Supervision}.lean` |
| `Effect4/Context/Key.lean` | `src/Effect4/Machine/Key.lean` |
| `Effect4/Runtime/{Runtime,Scope,ScopeMachine,ScopeRestoration,LiveStack}.lean` | `src/Effect4/Machine/{Frames,Scope,ScopeMachine,ScopeRestoration,LiveStack}.lean` |
| `Effect4/Deep/*.lean` | `src/Effect4/Machine/Deep/*.lean` |
| `Effect4/Arch/Views.lean` | `src/Effect4/Evidence/Views.lean` |
| `Effect4/StdLib/{Entry,Rc112,Links}.lean` | `src/Effect4/Evidence/StdLib/…` |
| `Effect4/Char/**` | `src/Effect4/Evidence/Char/**` |
| `Effect4/Surface/*` fixtures (`shopDomain`, `addressEntity`, `userEntity`, `shopApi` + its endpoints and schemas, `shopServer` + tools/resource/prompt, `docsDeployment`, `docsRequirements`, `docsSite`, `docsEndpointTable`, `docsWranglerJson`, `docsWorker*`) | `Fixtures/Shop/{Domain,Api,Mcp}.lean`, `Fixtures/Docs/{Deployment,Site}.lean` (module `Fixtures.Shop.Domain`, …) |
| `Effect4Test.lean` | `Test/All.lean` (module `Test.All`; `#effect4_axiom_gate` stays here) |
| `Effect4Test/**` | `Test/**`, area directories renamed with the layers: `Syntax`→`Program`, `Semantics`+`Runtime`+`Environment`→`Machine`, `Target/TypeScript`→`Codegen`, `Arch`+`Store`→`Store`/`Evidence`, `Deep`→`Machine/Deep`, `Audit`, `Api`, `Schema`, `Surface`, `Data`, `Counterexamples/*` likewise |
| `test/contracts`, `test/counterexamples`, `test/fixtures` | `Test/contracts`, `Test/counterexamples`, `Test/fixtures` |

The Schema pins under `Schema/Pins/` keep their prose; they are still built (zero
declarations, zero cost).

## A.2 Namespace map (declaration names)

| today | after | how |
| --- | --- | --- |
| `Effect4.Syntax.*` | `Effect4.Program.*` (printer: `Effect4.Codegen.Print.*`) | `namespace`/`open`/qualified uses, sed |
| flat Schema names `Effect4.{Representation, Check, Document, MultiDocument, ReferenceEntry, Annotations, AnnotationKey, AnnotationEntry, Payload types, EffectfulField…}` | `Effect4.Schema.*` | `namespace Effect4` → `namespace Effect4.Schema` in the Schema files; `open Effect4.Schema` added beside every `open Effect4` in consumers |
| `Effect4.Surface.{Entity, Domain, …}` types stay; the loose functions and clause predicates | `Effect4.Surface.Entity.*`, `.Api.*`, `.Agent.*`, `.Deploy.*`, `.Site.*` (`Kind`, `Sch`, `Refusal`, `Stance`, `Pin`, `SurfaceMark` and the annotation keys stay `Effect4.Surface.*`) | per file `namespace` |
| `Effect4.Target.TypeScript.Schema.*`, `Effect4.Target.TypeScript.EffectfulField.*`, `Effect4.Target.EffectV4.*` | `Effect4.Codegen.Schema.*`, `Effect4.Codegen.EffectfulField.*`, `Effect4.Codegen.Profile.*` | sed; `AxiomGate` exact names |
| the emitters in `Effect4.Surface` (`httpApiModule`, `clientModule`, `openApi`, `toolkitModule`, `toolsListJson`, `resourcesListJson`, `promptsListJson`, `wranglerJson`, `workerModule`, `Entity.tsModule`, `Domain.tsModule`, `spell`, `toJsonSchema`, `*.jsonSchema`) | `Effect4.Codegen.*` | move + namespace |
| the readers (`ofJsonSchema`, `ofMcpToolsList`, `ofWrangler`, `reifyJson?`) | `Effect4.Ingest.*` | move + namespace |
| `Effect4.Arch.*` | `Effect4.Schema.accepts`/`acceptsShape`, `Effect4.Store.{Json.ofNat, binary64OfNat, Representation.toJson?, Document.toJson?}`, `Effect4.Evidence.Views.*` | move + namespace |
| `Effect4.StdLib.*`, `Effect4.Char.*` | `Effect4.Evidence.StdLib.*`, `Effect4.Evidence.Char.*` | sed |
| `Effect4Test.*` | `Test.*` | sed on `namespace`/`import`/qualified names; `AxiomGate` module lists |
| `Effect4.{Json, Float64, Row, Lens, Optional, Traversal}` and every machine name (`Effect4.Cause`, `Exit`, `FiberId`, `Supervision`, `ServiceKey`, `Prim`, `FrameFiber`, `Scope`, `Deep.*`) | unchanged (D19 later) | — |

## A.3 Build files and roots

`lakefile.toml`: `[[lean_lib]] name = "Effect4"`, `srcDir = "src"`, `globs = ["Effect4.*"]`;
`name = "Test"`, `roots = ["Test.All"]` (the green battery + gate) and `globs = ["Test.+"]`
for the red-inclusive tree; per-area libs `TestSchema`… → `globs = ["Test.<Area>.+"]`;
`name = "Fixtures"`, `globs = ["Fixtures.+"]`; `defaultTargets = ["Effect4", "Fixtures", "Test"]`.
`src/Effect4.lean` imports every layer; `Test/All.lean` imports every battery and runs the
gate. `AxiomGate`: the audited prefixes become `Effect4.*`, `Fixtures.*`, `Test.*`; the
module-closure gate walks `src/Effect4`, `Fixtures`, `Test`.

## A.4 Records and scripts

Docstring path citations (`Effect4/Runtime/Runtime.lean:560`, ~800 sites) are rewritten by
one script with the A.1 map (`Effect4/Runtime/Runtime.lean` → `src/Effect4/Machine/Frames.lean`
…). `scripts/test-trust-gate.sh` (walks `Effect4/`, `Effect4Test/`, copies `Effect4.lean`,
`Effect4Test.lean`), `check-effect-runtime-census.sh` and `report-effect-runtime-coverage.sh`
(`Effect4Test/Audit/RuntimeCoverage.lean`), `check-internal-citations.sh`, the schema and
data-row/context-key gates, `sweep.sh`, the CI workflow, `README.md`, `AGENTS.md`,
`docs/ARCHITECTURE.md`, `harness/README.md`, `test/contracts/README.md`: every `Effect4Test/`
and `Effect4/` path updated. `COORDINATION.md` gets the claim.

## A.5 Order and delegation

1. Coordinator: `git mv` everything per A.1 (one script), `lakefile.toml`, `src/Effect4.lean`,
   `Test/All.lean`, `AxiomGate` prefixes; the `Effect4Test` → `Test` sed; the
   `Effect4.Syntax` → `Effect4.Program` sed. `lake build -j 2 Effect4` until green.
2. Agents, one per area, disjoint files, no builds beyond `lake build -j 2 <own modules>`,
   one at a time: (a) Schema namespace, (b) Surface sub-namespaces + fixture extraction into
   `Fixtures/`, (c) Codegen/Ingest split of the emitter files + `Spelling` into `Program.Ty`,
   (d) scripts, docs, citations (no build).
3. Coordinator: `lake build -j 2 Effect4 Fixtures Test`, the trust gate through WSL, commit.
