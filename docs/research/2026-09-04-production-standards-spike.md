# Production standards spike: the interface catalogue, configuration as an algebra, and the shapes worth freezing

Date: 2026-09-04, late. Session: the provision session (PC, Claude), the follow-up the user asked
for after `f182d2b` landed (`2026-09-04-provision-algebra.md`). Status: **design note, grilled;
one workshop spike (`workshop/Config/Config.lean`, §4) elaborated under `-M 3072`; nothing
landed.** The rulings this note answers, in the user's words:

1. *"look into what the best deployment standards, data shapes, and tools we should explicitly
   model in order to guide us towards the abstractions that lead towards the best ergonomics and
   observability by giving the developer knowledge, confidence, and control via proven
   algebraically tested abstractions."*
2. *"we should have every interface of the Effect standard and platform libs enumerated and typed
   a la TyXML + Eff since they all natively speak Effect Schema .. and yes Config and Config
   provider are crucial ... ENV injected .. string substituted .. general abstraction."*

Everything cited is at the pins in this tree: `vendor/effect-4.0.0-rc.112/src` and
`vendor/wrangler-3.114.16/config-schema.json` (SHA-256 `3f7bca5c…495ea7bb`, as
`Ingest/Wrangler.lean:12-13` records it). Line numbers are those files'.

## 0. The one-paragraph answer

Model explicitly exactly what can be **frozen at a pin and checked against the algebra**: (a) the
rc.112 interface surface itself, as a generated, committed, Schema-native snapshot with one typed
row per export (the TyXML move, §2); (b) configuration, as a small algebra with a proved fallback
monoid, a path-transformation action, a tri-state reader and a fuel-bounded substitution (§4,
the spike); (c) the wrangler *environment* (not just the binding tables) as an instance of that
same provider algebra, inheritance included (§3 row 3); (d) the OTLP resource, span, log and
metric records together with the `OTEL_*` configuration rows the four rc.112 exporters read
(§3 rows 4–6); (e) the reference-key table (the `Context.Reference`s with defaults), which is the
population of the owed R8 split (§3 row 7); (f) trace-context propagation (W3C/b3) as a header
codec with a round trip (§3 row 6). The "developer knowledge, confidence and control" the user
asked for is then three columns of one table (§5): what the developer *sees* (rows, residuals,
receipts), what is *proved or probed* about it (theorems at the axiom ceiling, finite machine
probes, host receipts), and which *lever* changes it (`provide`, `withDefault`, `nested`, a
deployment's `vars`). The tsgo rule table (§6) is the external check on that claim: 99 rules at
the pin, of which the algebra decides or makes unrepresentable a majority, a testable prediction.

## 1. What rc.112 is at the pin, by census

One PowerShell pass over `vendor/effect-4.0.0-rc.112/src` (every `.ts` outside `internal/`,
`index.ts` excluded; persisted as `census-rc112.csv` in this session's scratchpad):

| | files | exports | service/reference keys | `layer*` exports | files citing `Schema.` | files reading `Config.` |
| --- | --- | --- | --- | --- | --- | --- |
| whole surface | 341 | 7,356 | 451 | 170 | 131 | 12 |
| stable core (`src/*.ts`) | 137 | 4,302 | 295 | 11 | | |

The `unstable/` packages, by the same count (exports / keys / layers / `Schema.` references):
ai 574/22/5/1,717; cli 269/3/2/124; cluster 347/23/40/246; devtools 50/1/5/145; encoding
62/0/0/196; eventlog 166/16/23/222; http 471/24/10/168; httpapi 273/15/6/493; observability
43/2/14/8; persistence 98/7/23/103; process 37/1/0/0; reactivity 164/6/3/26; rpc 179/9/20/226;
schema 61/0/0/211; socket 43/5/2/19; sql 93/5/0/94; workers 31/3/1/43; workflow 77/14/3/271.

Three readings the rest of the note rests on:

1. **Schema is the lingua franca.** 131 of 341 files reference `Schema.`; every platform package
   that carries data across a boundary (httpapi, rpc, cluster, workflow, eventlog, ai, encoding,
   persistence) types that data as a codec. The user's "they all natively speak Effect Schema" is
   the census, not a slogan. The consequence for the catalogue (§2): where rc.112 gives a codec,
   the row's request and answer are *Schema* values in the estate's own carrier, not `Ty`.
2. **The R channel has 451 named keys.** Every one is a `ServiceKey` row in the estate's sense;
   the provision algebra (`LayerTy`, `applyServices`) is the arithmetic over exactly this set. The
   references among them (the ones with a `defaultValue`) are the soft half the R8 row owes.
3. **Only twelve files read configuration**, and they are the production surface: the four OTLP
   exporters (`OtlpTracer.ts:161-179`, `OtlpLogger.ts:144-158`, `OtlpMetrics.ts:506-519`,
   `OtlpResource.ts:102-116`, plus `internal/otlpEnv.ts:17-37`), `ShardingConfig.ts:251-353`
   (twenty-six keys under one `nested` prefix, the largest single consumer), the CLI's
   `Argument`/`Flag`/`Param`, `RateLimiter`, and `Config`/`ConfigProvider`/`Layer` themselves.
   Modelling configuration therefore covers the whole of what the library needs from an operator.

## 2. The ruling made precise: a TyXML for Effect

**What TyXML is, in the four properties that matter.** OCaml's TyXML enumerates the *entire*
element and attribute vocabulary of HTML/SVG as typed combinators (the signature is total, not
a convenient subset); the nesting rules are phantom types over one uniform tree; there is one
signature and several implementations (printer, DOM, streaming) obtained by functor
application; and the printer is derived from the signature rather than written per element.

**The analogue here, property by property.**

| TyXML | The estate's counterpart | Exists / owed |
| --- | --- | --- |
| total signature of the standard | the **Interface Surface Snapshot**: one row per rc.112 export call signature, generated from the vendored source, committed, frozen by an exact census gate | owed (lanes L1–L2, §9); the Eff native alphabet's `Row` (`Program/Eff.lean:175-191`: `name`, `spelling`, `shape`, `kind`, `request`, `answer`, `error`, `requires`, `cite`) is already the row shape, hand-transcribed for the runtime fragment |
| phantom nesting types | the **R channel and the provision algebra**: `Effect<A, E, R>` typing (`Program/Typing.lean`), `LayerTy.provide` (`Program/Provision.lean`), `Middleware.applyServices` (`Surface/Middleware.lean`), `appTy_closed_iff` | exists (`f182d2b`) |
| one signature, many implementations | one `Signature Op` (`Typing.lean:48-54`), consumed by `typeOf`, the compile to the Layer machine, the printer, and the OCaml `eff` reader | exists for the runtime alphabet |
| derived printer | `Codegen/Layer.lean`, `Codegen/Spell.lean`: spellings are a table (`Row.spelling`), never per-row code | exists |

**The row of the snapshot** (the alchemy vocabulary on the Mac names the same object a
*Runtime Operation Surface Snapshot*: "a committed generated Schema-native artifact … for
deterministic capability derivation, tests, reviews, and demos", `alchemy_effect_flow/CONTEXT.md`;
its *Runtime Operation Descriptor* is one entry with "binding type, runtime object type,
operation name, broad parameter kinds, return kind, source version, and generation metadata").
Per export call signature:

| column | content | source of truth |
| --- | --- | --- |
| identity | module path, export name, signature index, `kind` (const/function/class/interface/type/namespace) | the TS compiler API over `src` (the Mac's `effect-profile/type-profile.mjs` already walks `export` statements and call signatures; `jsdoc-extract.py` already yields `@category`/`@since`/summary/examples per export) |
| stability | `stable` (`src/*.ts`) / `unstable/<package>` | path |
| channels | `A`, `E`, `R` as spelled, each graded: **schema** (rc.112 gives a codec: HttpApi payloads, Rpc, Entity messages, Workflow payloads, `Config.schema`, `KeyValueStore.toSchemaStore`, `Model`), **ty** (inside `Program.Ty`), **handle** (verbatim spelling, `Ty.handle`) | the compiler API; the estate's `Ty.render` inverse for the `ty` grade |
| R-class | what the export does to `R`: `neutral`, `adds`, `discharges`, `closes`, `transforms`, `replaces` (the census taxonomy of `type-profile.mjs`'s second pass, `classify(before, after)`) | derived; and it is the provision algebra's operation table: `adds` = `Row.union`, `discharges` = `Row.diff` / `provide`, `closes` = `Closed`, `neutral` = identity |
| scope | `Scope` in `R`, `Exclude<…, Scope>` (the `scopeInR` / `scopeExcluded` counters) | derived; matches `layerTy`'s subtraction of `sig.scopeKey` |
| keys | the `Context.Service`/`Context.Reference` identity strings the module declares, with `defaultValue` presence and `fiberCached` | grep-exact today (§3 row 7) |
| config | the `Config.*("NAME")` paths the module reads (the twelve files of §1) | grep-exact today |
| cite | file and lines | the generator |

**Feasibility, measured.** A syntactic pass with the TypeScript compiler API (`typescript@5.9.3`
from `vsco-loupe`'s `node_modules`; `workshop/Surface/surface-probe.mjs`, output
`surface-probe.tsv`) over the same 341 files runs in seconds and already yields the row shape:

| | count |
| --- | --- |
| exported statements | 7,480 |
| classes / of which `extends Context.Service\|Reference` | 432 / 98 (the other 353 keys of §1 are `const X = Context.Reference(…)`/`Service` values) |
| interfaces / type aliases / namespaces | 1,086 / 677 / 119 |
| value-level rows (consts, functions, call signatures) | 6,806 |
| of which with no syntactic type (`export const x = dual(…)`, `= Schema.Struct(…)`) | 2,027 |
| effectful call signatures (`Effect` 930, `Stream` 242, `Layer` 121, `Config` 13) | 1,306, of which data-last 441 |
| typing grade of the effectful rows (A, E, R all inside `Ty`) / parametric / handle | 233 / 693 / 380 |
| `R` shape (Effect + Layer): `never` / union / type parameter / single key / `Exclude<…>` / other | 447 / 404 / 313 / 74 / 39 / 16 |
| `E` shape: `never` / type parameter / union / single / other | 477 / 347 / 274 / 30 / 27 |
| stable / unstable among the effectful rows | 1,085 / 221 |
| top `@category` values | constructors 1,081; combinators 743; schemas 299; guards 277; getters 265; filtering 261; mutations 223; transforming 202; predicates 191; sequencing 190; layers 188 |

Two consequences for lane L1. The 2,027 untyped values need the checker (`ts.createProgram`,
`getTypeAtLocation`) or the emitted `.d.ts`, as the Mac's `type-profile.mjs` already assumed
by reading `dist/*.d.ts`; the source-only pass is a census, not the snapshot. And the unstable
packages' surface lives mostly in *interface members* (service shapes: 1,086 interfaces) and
class methods, which this probe does not walk; the snapshot's row unit for a service is the
member, with the service key as its `requires`. The grade numbers are syntactic estimates and
are quoted here only to size the columns: roughly one effectful row in six is fully inside `Ty`
today, one in two is parametric (typed at the call site), and the rest are handles.

**What the gate says.** As `Test/Data/RowAssurance.lean` freezes the exact declaration list of
`Effect4.Data.Row`, a `Test/Audit/SurfaceCensus.lean` freezes the snapshot's counts (rows,
keys, references, config paths) and the Lean reader's agreement with them. The claim is
totality of the *enumeration*; the typing is a graded column, and the honest statement is "every
export appears; N% are schema-typed, M% ty-typed, the rest handles", with N and M as numbers the
gate prints, never as prose.

**Why this is not a second type checker.** The snapshot does not re-derive TypeScript; tsc and
tsgo remain the truth column (`2026-09-04-ts-ingestion-and-programs-as-content.md` §1.2, stage
(f)). What the snapshot adds is that the *estate* can now say, of a program it prints, which
rows it performs, which keys those rows need, which config paths those keys' layers read, and
whether a given deployment closes both rows, before the host is consulted. That is the
"knowledge" column of §5.

## 3. The data shapes to model explicitly

Ordered by the rule of §0: frozen at a pin, checked against the algebra, and consumed by the
production surface (the twelve files, the deployment, the exporters).

| # | shape | authority | estate today | add | why (knowledge / confidence / control) |
| --- | --- | --- | --- | --- | --- |
| 1 | **Configuration path tree**: `Path`, `Node` (`Value`, `Record keys value?`, `Array length value?`), the provider (`load`, `mapInput`), the reader with its tri-state resolution (`Resolved {value, hasInput}` / `Absent {error}` / `EvaluationFailure {error, hasInput}`) | `ConfigProvider.ts:55-72, 269-305, 357-386`; `Config.ts:108-138` | nothing | §4, the spike: `Provider`, `ConfigTerm`, `eval`, laws | the residual config row (§4.6) is what the operator must set; absence and invalidity are distinguished, so "missing" is never reported as "wrong" |
| 2 | **Environment record and dotenv**: the `_` trie (`DATABASE_HOST` at both `["DATABASE_HOST"]` and `["DATABASE","HOST"]`), empty string as missing, all-numeric children as `Array`; dotenv with `${VAR}` / `${VAR:-default}` expansion | `ConfigProvider.ts:1121-1256` (`fromEnvRecord`, `buildEnvTrie`, `nodeAtEnv`), `:1304-1408` (`fromDotEnvContents`, `interpolate`) | `Binding.var`/`Binding.secret` (`Surface/Deploy.lean:283-284`) | `fromRecord`/`fromEnvRecord`, `Tmpl`/`expand` with fuel; refusal rows CE-002, CE-003 | "ENV injected, string substituted" become two provider constructors with laws; rc.112's own interpolation diverges on a self-reference (§4.5), the model refuses by name |
| 3 | **The wrangler environment**: `RawEnvironment` (definition at `config-schema.json:2326`; 57 property keys; `RawConfig` at `:1256` has 72, the extra ones being the top-level-only `env`, `dev`, `site`, `alias`, `legacy_*`, `*_blobs`, `wasm_modules`, `miniflare`, `send_metrics`, `keep_vars`, `type`, `webpack_config`, `pages_build_output_dir`), `env.<name>` (`:1510`), and the inheritance rule: 23 keys carry the schema's own note "not automatically inherited from the top level environment" (`ai`, `analytics_engine_datasets`, `browser`, `cloudchamber`, `containers.app`, `d1_databases`, `define`, `dispatch_namespaces`, `durable_objects`, `hyperdrive`, `images`, `kv_namespaces`, `mtls_certificates`, `pipelines`, `queues`, `r2_buckets`, `send_email`, `services`, `tail_consumers`, `unsafe`, `vars`, `vectorize`, `workflows`; `:347-1162`), the rest inherit | the schema | the 13-key fragment (`Ingest/Wrangler.lean:75-78`), `Deployment`/`Binding` (`Surface/Deploy.lean:272-415`) | `effective name raw := orElse (nested ["env", name] raw) (restrict inheritable raw)` in the §4 algebra; extend the fragment by `observability` (`:1225-1255`), `triggers.crons`, `queues.consumers` (`:1852-1902`: `dead_letter_queue`, `max_batch_size`, `max_batch_timeout`, `max_concurrency`, `max_retries`, `retry_delay`, `visibility_timeout_ms`), `limits` (`UserLimits :3263`), `placement`, `tail_consumers` (`:3238`), `logpush`, `compatibility_flags` | a named environment is a *provider expression*, so "this binding is not visible in `env.prod`" is a theorem of `restrict`, not a surprise at deploy time; `vars` is `provided` for the residual of row 1 |
| 4 | **OTLP resource and exporter configuration**: `Resource {serviceName, serviceVersion, attributes}` from `OTEL_SERVICE_NAME`, `OTEL_SERVICE_VERSION`, `OTEL_RESOURCE_ATTRIBUTES` (a URI-component-encoded record *schema*, `OtlpResource.ts:102-105`); exporter rows `OTEL_SDK_DISABLED`, `OTEL_EXPORTER_OTLP_ENDPOINT` and the per-signal `…_{TRACES,LOGS,METRICS}_ENDPOINT`/`_HEADERS`/`_TIMEOUT`, `OTEL_{TRACES,LOGS,METRICS}_EXPORTER`, `OTEL_BSP_*`, `OTEL_BLRP_*`, `OTEL_METRIC_EXPORT_*` | `OtlpResource.ts:91-131`, `OtlpTracer.ts:161-179`, `OtlpLogger.ts:144-158`, `OtlpMetrics.ts:506-519`, `internal/otlpEnv.ts:17-37`; `Otlp.layerFromConfig :93` | nothing | the config rows of the four exporter layers as `ConfigTerm`s; `Resource` as a Schema-typed record | the observability stack's operator contract is one residual row; `fromConfig` is `orDie` on a missing `OTEL_SERVICE_NAME` (`OtlpResource.ts:131`), which the tri-state reader makes visible as *absence* before the host dies |
| 5 | **Signal records**: `Span` (`Tracer.ts:372-388`: `name`, `spanId`, `traceId`, `parent`, `annotations`, `status`, `attributes`, `links`, `sampled`, `kind`), `SpanLink` (`:431-434`), `Logger.Options` (`Logger.ts:101-107`: `message`, `logLevel`, `cause`, `fiber`, `date`), the metric states (`CounterState :249`, `FrequencyState :407`, `GaugeState :536`, `HistogramState :711`, `SummaryState :898`), OTLP `TraceData`/`ResourceSpan`/`ScopeSpan`/`OtlpSpan` (`OtlpTracer.ts:353-389`), wrangler `observability {enabled, head_sampling_rate, logs {enabled, head_sampling_rate, invocation_logs}}` (`:1225-1255`) | as cited | the tape and the receipt (substrate note §4.3, §5.4) | the records as carriers now; the fold `Tape → TraceData` (a span is a `scoped` interval on the tape; attributes are annotations; links are fork/await edges; `status` is the interval's `Exit`) as an owed design | the developer's trace is a *projection of the proved tape*, and the OTLP export is a printer of that projection; sampling (`head_sampling_rate`) is a filter on the fold, stated once |
| 6 | **Trace-context propagation**: W3C `traceparent`, b3 single header, `x-b3-*`; `toHeaders`/`fromHeaders` | `unstable/http/HttpTraceContext.ts:41-139`; `HttpClient.TracerPropagationEnabled` default `true` (`HttpClient.ts:2043`) | nothing | a header codec with `fromHeaders (toHeaders s) = some (external s)` as the law; three parsers, one printer | small, and it is the one place a request's identity crosses a service boundary |
| 7 | **The key table with kinds**: 451 `Context.Service`/`Context.Reference` declarations; the references with defaults (one grep surfaces 34: `ConfigProvider` → `fromEnv()`, `Scheduler`, `MaxOpsBeforeYield` 2048, `PreventSchedulerYield`, `Tracer`, `DisablePropagation`, `CurrentTraceLevel` "Info", `TracerEnabled`, `TracerTimingEnabled`, `CurrentLogLevel` "Info", `LogToStderr`, `Console`, `Random`, `ExecutionPlan.CurrentMetadata`, `Schedule.CurrentMetadata`, `FiberRuntimeMetrics`, `Socket.SendQueueCapacity` 16, `Workflow.CaptureDefects`/`SuspendOnFailure`, `Activity.CurrentAttempt` 1, `ClusterSchema.Persisted`/`WithTransaction`/`Uninterruptible`/`ClientTracingEnabled`, `OpenApi.Exclude`, `MessageStorage.MemoryTransaction`, `HttpClient.TracerPropagationEnabled`, `EventLog.CurrentStoreId`, `HttpIncomingMessage.MaxBodySize`, `Multipart.MaxFileSize`, `SqlClient.SafeIntegers`, ai `Tool.Readonly`/`Destructive`/`Idempotent`/`OpenWorld`; `internal/references.ts` holds the log/trace ones) | the sources | `ServiceKey`, `Context.References`, `SatisfiesRefs` (`Program/Provision.lean`), the machine's reserved keys 0–3 (`scopeKey`, `maxOpsKey`, `preventYieldKey`, `currentMemoMapKey`) | the R8 split (`KeyKind := service \| reference`) populated from the snapshot's `keys` column | a program that reads a reference has no hard requirement (`satisfiesRefs_of_defaults`); the table says which reads are soft and what the default is, so a deployment's residual is exact |
| 8 | **Cluster topology**: `ShardingConfig` (26 keys under one prefix, `ShardingConfig.ts:251-353`), `K8sTypes.Pod`, `RunnerAddress`, `EntityAddress` | `unstable/cluster` | nothing | the `ShardingConfig` row as a `ConfigTerm` now (it is the largest consumer); the topology records later | deferred beyond the config row |
| 9 | **Persistence**: `KeyValueStore.layerMemory :331`, `layerFileSystem :368`, `layerSql :509`, `toSchemaStore :782` | `unstable/persistence/KeyValueStore.ts` | nothing | three `LayerTy` triples and one Schema-typed store row | the one library example where a *store* speaks Schema at its boundary |
| 10 | **Runtime**: `ManagedRuntime.make(layer, memoMap?)` (`ManagedRuntime.ts:285`) | as cited | `App`, `build`, `lower` | nothing new: a runtime is a built closed layer | the `appTy_closed_iff` theorem is its type |
| 11 | **Capability graph** (alchemy): `Capability Node`, `Identity` (structural), `Provenance` (fields and edges), `Evidence`, `Scope`, `Catalog`, `Resource State Label` | `alchemy_effect_flow/CONTEXT.md` (Mac) | the Evidence views | the snapshot's `cite` column is provenance; identity = (module, name, signature index); the catalogue is a derived graph, never the stack | the vocabulary to reuse rather than reinvent when the snapshot is rendered |

Not modelled, on purpose: Terraform/vsphere (the Mac's `bfkn-vmware-provisioning` mission is a
different substrate with no pin in this tree), Kubernetes beyond the `Pod` record, the
`unstable/ai` provider surfaces (the standards survey of 2026-09-02 ranks those separately), and
`cloudchamber`/`containers` (the schema calls them out; they are a second host).

## 4. Configuration as an algebra (the spike, `workshop/Config/Config.lean`)

The spike is one file, parametric in a name type so that no theorem unfolds `String` (string
equality and order reach `Classical.choice` on this toolchain; `Program/Eff.lean:93-96` records
the same constraint for `Ty.key`). Lane results are §10.

### 4.1 Objects

```lean
inductive Seg (Name) | key (name : Name) | index (n : Nat)          -- ConfigProvider.ts:55-72
abbrev Path (Name) := List (Seg Name)
inductive Node | value (v : String) | record (keys : List String) (value : Option String)
               | array (length : Nat) (value : Option String)
inductive Provider (Name)
  | source (get : Path Name → Except (SourceError Name) (Option Node)) (transform : Path Name → Path Name)
  | orElse (first second : Provider Name)
```

`SourceError` carries a `path` here and not in rc.112 (`:207-210`: `message` and an optional
`cause`); it is the model's addition so that a source failure and a `missing` at one place stay
distinguishable. `source get transform` is rc.112's `makeSource` (`:367-375`): `load p = get (transform p)`, and
`mapInput f` yields `source get (f ∘ transform)` because the source composes `flow(transform, f)`:
**`f` runs after the existing transformation**. `orElse` is `makeOrElse` (`:377-386`): the second
provider is consulted only on `undefined`, a `SourceError` propagates (`:455-456`), and
`mapInput` distributes to both operands (`:384`). `nested prefix = mapInput (prefix ++ ·)`
(`:883-886`); `constantCase = mapInput` over string segments by `String.configCase` (`:748-750`).

### 4.2 Laws

| law | statement | status |
| --- | --- | --- |
| fallback monoid | `(orElse (orElse a b) c).load = (orElse a (orElse b c)).load`; `empty` (`get := fun _ => ok none`) is a two-sided identity; `orElse p p` loads as `p` | proved (spike) |
| not commutative | two sources disagreeing at one path | `#guard`, row `E4-CONF-CE-004` |
| action | `(p.mapInput g).mapInput f = p.mapInput (f ∘ g)`; `mapInput id = id`; `mapInput f (orElse a b) = orElse (mapInput f a) (mapInput f b)` by definition | proved |
| nesting composes outward | `(p.nested q).nested r = p.nested (r ++ q)`: the later `nested` is the outer prefix (docs `:767-772`) | proved |
| fresh pre-composition | `(make get |>.mapInput f).load p = get (f p)` | proved |
| **non-law** | `(p.mapInput f).load ≠ p.load ∘ f` once `p` carries a transform: with `p = source get (key "a" :: ·)` and `f = (key "b" :: ·)`, rc.112 looks up `["b","a"]`, pre-composition would look up `["a","b"]` | `#guard`, row `E4-CONF-CE-001`. This is the documented gotcha (`:812-815`) turned into a checked inequation; the naive "provider is a function of the path" model is *wrong* for rc.112, which is the single most useful thing the spike establishes |

### 4.3 The reader

`ConfigTerm Name` with `string`/`nat`/`bool` primitives, `succeed`, `fail`, `withDefault`,
`orElse`, `option`, `nested`, `zip`; `eval : ConfigTerm → Provider → Path → Except Failure
Resolution` where `Resolution = resolved value hasInput | absent error` is `Config.ts:118-129`
verbatim and `Failure = {error, hasInput}` is `:131-134`. The semantics that the docs state and the
spike pins:

| combinator | on `resolved` | on `absent` | on `Failure` | cite |
| --- | --- | --- | --- | --- |
| `withDefault d` | unchanged | `resolved d false` | propagates | `Config.ts:744-759`: "validation errors and partially supplied groups still propagate" |
| `orElse d` | unchanged | evaluates `d`, `hasInput` or-ed | evaluates `d`, `hasInput` or-ed | `:444-464`: "recovery preserves whether the primary config read provider input" |
| `option` | `some` | `resolved none false` | propagates | `:887` |
| `zip a b` | both: `pair`, `hasInput` or-ed | both absent: absent; one absent, the other resolved *with input*: **Failure** with `hasInput = true`; one absent, the other resolved without input: absent | propagates | `:1150-1154`, `:755-756` |
| `nested n c` | `eval c P (q ++ [key n])` | | | `:1943-1958` |

A primitive over a found container with no co-located scalar (a `Record` at a `string` path)
is *absent*, not invalid: `hasProviderInput` is `getScalar(node) !== undefined` (`Config.ts:1041`)
and a decode failure without input evidence is `absent` (`:1211-1213`), so `withDefault` fires
on it. The draft of this note had it as a failure; the spike corrected it against the source
(§10, finding 3).

The transfer law between the two `nested`s holds modulo the path an error reports:
`reroot q (eval c ((make get).nested q) r) = eval c (make get) (q ++ r)`, hence
`eval (nested n c) P []` and `eval c (P.nested [key n]) []` agree on values and on input
evidence for a fresh `P`, and differ only in the prefix a `missing`/`invalid` carries, because
`Config.nested` extends the evaluator's prefix (`Config.ts:2050-2051`) while
`ConfigProvider.nested` extends the provider's transform and the error path is the Config-level
one (`:1209`). It holds only for fresh providers, by the non-law of §4.2. Row `E4-CONF-CE-005`
is the partial-group case: a `withDefault` over `zip (string "host") (string "port")` with
`host` present and `port` absent is a *failure*, not the default.

### 4.4 ENV injection

`fromRecord entries` (segmented paths, generic in `Name`) is the tree side of `fromEnvRecord`;
`fromEnvRecord env = fromRecord (split on "_")` is the bridge, executable over `String`. The
quotient is row `E4-CONF-CE-002`: rc.112 also answers the flat spelling `["DATABASE_HOST"]`
(`:1227`, the joined key), the segmented model does not; and `A_B` at `["A","B"]` and at
`["A_B"]` name one value, so `fromEnv` is not injective on paths. Empty strings are missing
(`:1089-1091`), all-numeric children make an `Array` (`:1237-1241`). `fromTree` is
`fromUnknown` (`:1044-1082`) over a local tree with numbers rendered by `toString`.

### 4.5 String substitution

rc.112's `interpolate` (`:1364-1408`, dotenv-expand's algorithm) replaces the right-most
`${NAME}` / `${NAME:-default}` / `$NAME` group and recurses on the result. **It diverges on a
self-reference and on a mutual reference.** Verified on this PC on 2026-09-04 by transcribing the
function verbatim into node with a depth counter: `A=${A}` and `A=${B}, B=${A}` both exceed
depth 2000 (`dotenv-probe.js` in the scratchpad; plain, default, chain, escape and
empty-as-missing cases all answer as documented). The model represents a value as a template
(`lit | ref name default | cat`) and expands with fuel; fuel exhaustion on a `ref` is a refusal
by name, row `E4-CONF-CE-003`. The parse from a `.env` line to a template is a stated refusal
of the spike (a regex transcription buys nothing the theorems use). Owed to the truth harness: the
same divergence through the public API, `fromDotEnvContents("A=${A}", { expandVariables: true })`.

### 4.6 The configuration requirement row

`reads q c : List (Path Name)` is what a term may load; `provided entries` is what a record
provides with a non-empty value; `residual := Row.diff (reads) (provided)` over `Row ServiceKey`
through a path table (`keyOf i = ⟨⟨i⟩, ⟨i⟩⟩`, the move of `Surface/Provision.lean`), and not
over `Row Nat`: instantiating `Row.diff_eq_empty_iff_subset` at `Nat` pulls `Classical.choice`
through core's `Std.IsLinearOrder Nat` / `Std.LawfulOrderLT Nat` instances, while
`Machine/Key.lean:270-290`'s hand-proved instances keep it at the ceiling (§10, finding 2). The
theorem the spike proves
is the one that makes the residual *mean* something: **absence names a missing key**,
`eval c (fromRecord entries) q = ok (absent e) → ∃ p ∈ reads q c, p ∉ provided entries`; with
`Row.diff_eq_empty_iff_subset`, an empty residual rules absence out. This is the exact analogue
of `requirementsMet_row` one level down: the service row says which *keys* a deployment must
bind, the config row says which *values* its `vars` must carry.

### 4.7 The deployment closes the config row

`Deployment.bindings` (`Surface/Deploy.lean:394-415`) is a provider: `var name value` entries
are `provided`, `secret name` entries are provided out of band (a reference-satisfied name, never
a value in the model), and the exporter rows of §3 row 4 are `reads`. A named environment is
`orElse (nested ["env", name] raw) (restrict inheritable raw)` with `inheritable` the complement
of the 23 non-inherited keys. The row law then reads: a deployment is *config-closed* for a set
of layers when the residual of the union of their `reads` against its `provided` is empty. That
is the "what must the operator set" report, decided by `decide`.

## 5. Knowledge, confidence, control

| the developer wants | what they see | proved / probed | the lever |
| --- | --- | --- | --- |
| which services this program needs | `typeOf e` → `EffTy.requires` (`Program/Typing.lean`) | total by structure; progress owed to A3 | `provide` / `provideMerge` (`LayerTy`) |
| whether this wiring is complete | `appTy_closed_iff`, `deploymentLayer_closed`, `requirementsMet_row` | theorems at the ceiling; `#guard`s through the Layer machine | the deployment's bindings; `Middleware.residual` |
| which config the layers read, and what is still unset | `reads`, `residual` (§4.6) | `absent_names_missing` (spike) | `vars`, `withDefault`, `nested`, a named environment |
| whether a soft requirement will silently take a default | the reference table (§3 row 7) with defaults | `satisfiesRefs_of_defaults`; the machine's `maxOpsKey` incident (`E4-PROV-CE-007`) is the cautionary probe | provide the reference explicitly |
| what the library offers, at this pin, typed | the snapshot rows (§2) | census gate; typing grade column | the alphabet: rows admitted into `Signature` |
| what happened at run time | the tape and its receipt (fuel, tape address, profile address, host id; substrate note §4.3) | replay determinism (DB-03); host receipts (`harness/truth` 9/9 at rc.112) | fuel, masks, `choose` sites |
| how it will look in a tracer | the `Tape → TraceData` fold (§3 row 5, owed) | owed | sampling as a filter; `DisablePropagation` |
| that the printed module is what the host accepts | tsc + tsgo + a node run (`effect4-tools/packages/harness`) | evidence rows | the printer's canonical forms (§6) |

The pattern in the second column: every row is a *value the developer can print*, not a message
in an IDE. That is what "knowledge via algebraically tested abstractions" cashes out to: the
thing they read is the thing the theorem is about.

## 6. The 99 tsgo rules against the algebra

The Mac's pinned `effect-profile/tsgo-rules.json` lists 99 rules. Grouped by what the estate
does about each (a claim table; the prediction is testable, §9 L7):

| group | rules | the estate's answer |
| --- | --- | --- |
| requirement / error channel | `anyUnknownInErrorContext`, `missingEffectContext`, `missingEffectError`, `missingLayerContext`, `leakingRequirements`, `missingEffectServiceDependency`, `scopeInLayerEffect`, `layerMergeAllWithDependencies`, `strictEffectProvide`, `multipleEffectProvide`, `genericEffectServices`, `nonObjectEffectServiceType`, `classSelfMismatch`, `serviceNotAsClass` | **decided** by the provision algebra and the typing: `appTy_closed_iff`, `residual`, `provide_provide_rows`, `layerTy`'s scope subtraction; `Ty.handle "unknown"` in `E`/`R` is a typing refusal; services print as `class X extends Context.Service<X, Shape>()` by construction |
| generator / structure | `floatingEffect`, `floatingEffectInVitest`, `missingReturnYieldStar`, `missingStarInYieldEffectGen`, `returnEffectInGen`, `runEffectInsideEffect`, `nestedEffectGenYield`, `tryCatchInEffectGen`, `effectGenUsesAdapter`, `effectFnIife`, `effectInFailure`, `effectInVoidSuccess`, `promiseInEffectSuccess`, `lazyEffect`, `lazyPromiseInEffectSync`, `asyncFunction`, `newPromise`, `abortControllerInEffect`, `unsafeEffectTypeAssertion`, `catchUnfailableEffect` | **unrepresentable**: the `Eff` IR (`Program/Eff.lean:245-303`) has no floating value, no adapter, no promise; the printer cannot emit the shape the rule fires on |
| global capture | `processEnv`, `processEnvInEffect`, `globalFetch`(`InEffect`), `globalConsole`(`InEffect`), `globalDate`(`InEffect`), `globalRandom`(`InEffect`), `globalTimers`(`InEffect`), `cryptoRandomUUID`(`InEffect`) | **the reference keys of §3 row 7**: `ConfigProvider`, `Console`, `Random`, `Clock`, `Scheduler`; a program that reads the global has no config row, the rule and the row agree |
| schema | `preferSchemaOverJson`, `schemaLiteralNonFinite`, `instanceOfSchema`, `newSchemaClass`, `schemaUnionOfLiterals`, `schemaStructWithTag`, `overriddenSchemaConstructor`, `schemaSyncInEffect`, `preferTypedSchemaDecoder`, `redundantSchemaTagIdentifier`, `schemaNumber`, `preferSchemaTypeProperty`, `schemaOpaqueInstanceMember`, `deterministicKeys` | the Schema core (`Schema/Representation.lean`, `Check.lean`) and its printer; each rule is a canonical form the emitter already chooses or a refusal row to add |
| canonical spelling | `unnecessaryPipe`, `unnecessaryPipeChain`, `missedPipeableOpportunity`, `flatMapToMap`, `syncToSucceed`, `effectMapVoid`, `effectMapFlatten`, `effectSucceedWithVoid`, `unnecessaryEffectGen`, `effectDoNotation`, `effectFnOpportunity`, `catchAllToMapError`, `catchTagToCatchReason`, `catchDieToOrDie`, `catchToIgnore`, `catchToOrElseSucceed`, `catchChainToFirstSuccessOf`, `catchConditionalRefailToCatchIf`, `multipleCatchTag`, `redundantMapError`, `redundantOrDie`, `mapSomeToAsSome`, `allOfMapToForEach`, `unnecessaryArrowBlock`, `unnecessaryTypeofType`, `unnecessaryFailYieldableError`, `preferUnsafeConstructor`, `strictBooleanExpressions`, `missingPipeableSignature` | the printer emits one spelling per row (`Row.spelling`); a prediction, not a theorem: zero diagnostics from this group on the printed corpus |
| host facts | `outdatedApi`, `duplicatePackage`, `extendsNativeError`, `nodeBuiltinImport`, `globalErrorInEffectCatch`, `globalErrorInEffectFailure`, `unknownInEffectCatch`, `effectFnImplicitAny` | not covered; the pin and the harness answer these |

The prediction worth running (L7): print the nine corpus programs and the docs deployment,
run tsgo with the rule set on, and report diagnostics per rule; the algebra predicts zero in the
first three groups.

## 7. Sources used, and what each contributed

| source | contribution |
| --- | --- |
| rc.112 `Config.ts`, `ConfigProvider.ts` (cited by line above) | the whole of §4; the tri-state resolution is theirs, the term normal form for providers is theirs (`makeSource`/`makeOrElse`) |
| rc.112 `unstable/observability/*`, `Tracer.ts`, `Logger.ts`, `Metric.ts`, `unstable/http/HttpTraceContext.ts` | §3 rows 4–6 |
| `vendor/wrangler-3.114.16/config-schema.json` | §3 row 3; the inheritance notes are the schema's own words |
| Mac `effect4-tools/packages/effect-profile` (`type-profile.mjs`, `jsdoc-extract.py`, `tsgo-rules.json`, `v3-v4-renames.json`) | the generator seed for §2 and the R-class taxonomy; the 99 rules of §6 |
| Mac `alchemy_effect_flow/CONTEXT.md` | the snapshot vocabulary (§2, §3 row 11) |
| `2026-09-04-ts-ingestion-and-programs-as-content.md` §1.2 | the pipeline with the trust column; the snapshot generator is its stage (a) applied to the library rather than to user code |
| `2026-09-04-substrate-thesis-and-production-model.md` §4–5 | receipts and certificates as the confidence column of §5 |
| `2026-09-02-standards-targets-survey.md` §3.5 | OTel semantic conventions already scored there; this note adds only the SDK environment rows rc.112 reads |
| `2026-09-04-provision-algebra.md` | the algebra the catalogue's R column is typed with; §6 there already placed configuration on the reference half |
| twelve-factor "config in the environment"; the OpenTelemetry SDK environment-variable and OTLP-exporter configuration specifications; W3C Trace Context; Zipkin b3; dotenv-expand | the external standards behind rows 2, 4, 6 of §3; none is vendored, each is reached only through rc.112's reading of it, which is what the pin fixes |

## 8. Grill

**A1. "7,356 rows is a fantasy; nobody transcribes that."** Nobody does: the generator is
mechanical and already half-written on the Mac, and the probe of §2 produced 6,806 rows from the
vendored source in seconds on this PC; the gate is on the enumeration; the typing is a graded
column. The first slices are chosen by consumption, not by size: the twelve
configuration-reading files, the observability package, the reference table, and the R-classes of
`Effect`/`Layer`/`Stream` that the census already computed.

**A2. "`Ty` cannot type TypeScript generics, so the rows will be mostly handles."** True for the
core combinators, false for the platform boundary, where the census shows codecs everywhere. The
grade column says which is which; a row that is a handle still carries its `R` keys and its
config reads, which is what the algebra consumes. The claim is never "we typed rc.112".

**A3. "The provider carrier has a Lean function inside (`source get`), so it is not content."**
For theorems the leaf is a function; for content-addressing and printing the leaves are the four
constructors rc.112 exports (`fromEnv`, `fromUnknown`, `fromDotEnv`, `fromDir`), exactly the
`LeafSem` versus `lower` split of the provision note (§3 there). The spike keeps the function leaf
because every law is about `load`.

**A4. "The naive law is the one everyone believes."** Yes, and it is false at the pin (§4.2). A
model that proved `load (mapInput f p) = load p ∘ f` would be a proof about a different library.
The non-law is a register row, and the fresh-provider law is the theorem that survives.

**A5. "The dotenv divergence is a probe of a transcription, not of rc.112."** The function was
transcribed line by line from `:1364-1408`, the seven probes reproduce the documented cases, and
the divergence is structural (`interpolate` recurses on `envValue.replace(group, value)` with the
*unexpanded* record, `:1358`, so a self-reference replaces itself with itself). The public-API
reproduction through `fromDotEnvContents` is owed to the truth harness before the row is quoted
outside this tree.

**A6. "wrangler inheritance is subtler than the note."** It is; only the 23 stated notes are
modelled, and anything the schema does not state is a refusal, not a guess. The named
environment's own derived `name` (wrangler appends `-<env>`) is outside the fragment.

**A7. "Observability as a tape fold is a slogan until someone writes it."** Agreed; §3 row 5
freezes the *records* now, so that the fold, when written, has a typed target and a golden from
`OtlpSerialization`. The fold itself is a design row, not a claim.

**A8. "This is more lanes than the quota allows."** One agent ran (the spike), staggered as the
pacing rule requires; the generator runs on either machine (node is on the PC through mise; the
compiler API needs no build of rc.112); the Lean reader and gate are one Opus lane each; the rest
is sequenced in §9 and nothing in it needs a second Layer machine or a change to `Row`.

## 9. Lanes and decisions

| # | piece | files | who / size |
| --- | --- | --- | --- |
| L1 | the snapshot generator: `effect-profile`'s two scripts joined into one `surface-export.mjs` over `vendor/effect-4.0.0-rc.112/src`, emitting the §2 columns as TSV + JSON, deterministic (sorted, no timestamps); committed under `generated/` beside `schema-structural-assurance.tsv` | `effect4-tools` (Mac) or `scripts/` (PC) | one agent, node; half a day |
| L2 | the Lean reader and gate: `Ingest/Surface.lean` (a `Rule` whose `Input` is `List Row` plus the key and config tables), `Test/Audit/SurfaceCensus.lean` (exact counts, typing-grade percentages printed) | new modules; one import each in `src/Effect4.lean`, `Test/All.lean` | Opus, after L1 |
| L3 | land the Config algebra: `Program/Config.lean` (§4.1–4.6), `Surface/Config.lean` (the deployment provider, `restrict`, the named environment), `Codegen/Config.lean` (printer to `ConfigProvider.*`/`Config.*` syntax with `#guard` goldens), batteries and axiom reports, register rows `E4-CONF-CE-001..006` | new modules | Opus, from the green spike |
| L4 | the R8 split with the generated reference table (`KeyKind`, defaults as `Lit`s where literal) | `Machine/Context.lean`, `Program/Provision.lean` | coordinator (shared surfaces) |
| L5 | OTLP records and the exporter config rows; `HttpTraceContext` codec with its round trip | `Surface/Observability.lean` (new) | Opus |
| L6 | the wrangler fragment extension (`observability`, `triggers`, `queues.consumers`, `limits`, `placement`, `tail_consumers`, `logpush`, `compatibility_flags`, `env.<name>`) through the emitter and the reader, round trip at the named quotient | `Codegen/Worker.lean`, `Ingest/Wrangler.lean`, `Surface/Deploy.lean` | Opus |
| L7 | the tsgo prediction: print the corpus, run tsgo at the pin, count diagnostics per rule; a stress-plan slot | `harness/truth` | Mac, after L1 |
| D3 | **decision:** the typing-grade policy for the snapshot (which grades may enter `Signature`; whether a handle row may be performed by an Eff program) | — | owner |
| D4 | **decision:** whether `Config` terms enter `Eff` as rows performing against the `ConfigProvider` reference (the natural reading after R8), or stay a layer-time construct only | — | owner |
| D5 | **decision:** the snapshot's home: this repository's `generated/` (pinned with the vendor tree) or `effect4-tools` (regenerated per pin) | — | owner |

Gate at every landing: `lake build Effect4 Test` green on Windows, `#print axioms` at
`propext`/`Quot.sound` for every theorem, the row census extended when `Row.lean` changes, commit
by pathspec, the WSL bash gates, nothing pushed without the user's word.

## 10. Lane results

**Config lane (`workshop/Config/Config.lean`, one Opus agent, `lake env lean -M 3072`; re-run
by the coordinator afterwards, same command, `exit=0`).** 1,286 lines, imports
`Effect4.Data.Row` and `Effect4.Machine.Key` only; 28 public theorems and 16 private lemmas, 48
`#guard`s, no `sorry`, no `axiom`, no `native_decide`, no owed rows. Every `#print axioms` is at
`propext`/`Quot.sound` or below (fourteen depend on nothing; `orElse_assoc`, `orElse_empty_*`,
`orElse_idem`, `nested_nested`, `residual_empty_of_subset` use `Quot.sound` through `funext`
and `Row`; the rest `propext` only). `Classical.choice` appears nowhere.

What the lane found against the source, and what the note now says because of it:

1. **The axiom fence is String *traversal*, not String equality.** `String.decEq`, `==` on
   `String` and `List.contains` are clean; `String.toNat?`, `toUpper`, `splitOn`, `toList` and
   `length` each reach `Classical.choice` (well-founded recursion over `String.Pos`), and
   `#print axioms` traverses definitions, so one `toNat?` inside `eval` had made *every* `eval`
   theorem classical, `eval_nested := rfl` included. Fix: the scalar codecs are a supplied
   `Scalars` hook (`natOf`, `boolOf`) threaded through `eval`, the `LeafSem` position of
   `Program/Provision.lean`; `stdScalars` is the rc.112 instantiation and appears only in
   `#guard`s. Likewise `render : Seg Name → String` is supplied for a `Record`'s numeric child
   keys (`ConfigProvider.ts:1227`).
2. **`Row Nat` breaks the ceiling.** `Row.diff_eq_empty_iff_subset` is `[propext, Quot.sound]`
   generically and `[propext, Classical.choice, Quot.sound]` the moment it is instantiated at
   `Nat`: core's `Std.IsLinearOrder Nat` / `Std.LawfulOrderLT Nat` instances are the whole
   difference. The row carrier is `Row ServiceKey` with `keyOf i = ⟨⟨i⟩, ⟨i⟩⟩`;
   `Machine/Key.lean:270-290` proves those instances by hand from `Nat.lt_trichotomy`, which is
   why they stay clean. §4.6 is corrected accordingly.
3. **A found container with no co-located scalar is `absent`, not a failure.**
   `hasProviderInput = getScalar(node) !== undefined` for every scalar schema (`Config.ts:1041`)
   and a decode failure without input evidence is `Effect.succeed(absent(error))`
   (`:1211-1213`); so `Config.string` over a `Record` node is absent, and `withDefault` fires on
   it. The draft spec had said `invalid`; the model follows rc.112 and pins both readings as
   `#guard`s. §4.3 is corrected.
4. **The two `nested`s transfer only modulo error paths.** `missing`/`invalid` record the
   Config-level path (`Config.ts:1209`), which cannot know the provider's prefix; the law is
   `reroot q (eval c ((make get).nested q) r) = eval c (make get) (q ++ r)`, where `reroot`
   re-prefixes the error's path and leaves `ConfigError.source` alone (the provider's own
   report). Values and input evidence agree on the nose. §4.3 is corrected.
5. **`SourceError` has no path in rc.112** (`ConfigProvider.ts:207-210`: `message` and an
   optional `cause`); the model's `path` field is its own addition, documented as such.
6. **`leafAt` reads the first entry at the path whose value is present**, because "the value at
   exactly `p`, with `""` as missing" is false over a list with a duplicated key; the two agree
   on every record JavaScript can build.
7. **`orElse`'s recovery is `preserveInputEvidence`** (`Config.ts:211-224`, `:564-568`); the
   `hasInput` or-ing spelling equals it in both branches, and the `hasInput = false` branch is
   pinned as `recover_no_input`.
8. The lane did not re-run the node probe of §4.5; it checked the source instead
   (`:1396-1399` recurses on the substituted text with no depth bound and no cycle check). The
   probe was run by the coordinator (`workshop/Surface/dotenv-probe.js`).

The six register rows, each a pair of `#guard`s that would both have to change to fake the law:

| row | law refused / pinned | the pair |
| --- | --- | --- |
| `E4-CONF-CE-001` | `mapInput` is post-composition on the transform (`ConfigProvider.ts:373`), not pre-composition on `load` | `(P.mapInput f).load [] = ok (some (value "hit"))` vs `P.load (f []) = ok none` |
| `E4-CONF-CE-002` | the flat env spelling is the quotient (`:1227` vs `:1206-1207`) | `[key "DATABASE_HOST"]` answers `none`; `[key "DATABASE", key "HOST"]` answers `"localhost"` |
| `E4-CONF-CE-003` | rc.112 diverges on a `${}` cycle, the model refuses by fuel (`:1396-1399`) | `expand 8 [("A", ref "A")] (ref "A")` refused; the mutual pair refused; `expand_ref_self_refused` at every fuel |
| `E4-CONF-CE-004` | `orElse` is not commutative (`:379-383`) | `orElse a b` answers `"a"`, `orElse b a` answers `"b"` at one path |
| `E4-CONF-CE-005` | a partially supplied group is not defaulted (`Config.ts:674-675`, `:847-852`) | `withDefault (zip host port)` with `host` present is `Failure ⟨missing [port], true⟩`; with both absent it is the default |
| `E4-CONF-CE-006` | a later `nested` is the outer prefix and is not constant-cased (`:767-772`, `:883-886`) | `constantCase` then `nested "app"` reads `app_HOST`; `nested "app"` then `constantCase` reads `APP_HOST` |

`configCase` is transcribed from `String.ts:1628-1664, 1760-1761` as a character-pair test with
one character of lookahead and pinned by `databaseHost ↦ DATABASE_HOST`, `host ↦ HOST`,
`v2 ↦ V2`, `api-v2 xml ↦ API_V2_XML` (the case `String.ts:1754` states), `APIKey ↦ API_KEY`.

**Landing (lane L3, this session).** The first gate build failed: `Test/Audit/AxiomGate.lean`
audits every declaration, defs included, and the module's `String`-side instantiations
(`stdScalars`, `segOfString`, `splitUnderscore`, `fromEnvRecord`, `configCase`, `segCase`,
`Provider.constantCase`) and the `E4-CONF-CE-006` witnesses (`ce006Late`, `ce006Early`,
`entriesOf`, in the module and in the battery) reach `Classical.choice`; they are pinned by
exact name in the gate's choice lists, as the codegen renderers are, with the comment that
every theorem takes them as supplied hooks. The battery re-declares the module's eighteen
`private` witnesses verbatim, so it freezes the laws, not the witnesses; dropping `private`
in the module and deleting the copies is an owed tidy-up.

**Surface probe (coordinator, node, `workshop/Surface/surface-probe.mjs`):** the §2 table.

**What is landable from here, unchanged:** the whole of `workshop/Config/Config.lean` as
`src/Effect4/Program/Config.lean` (lane L3), with the six rows into `REGISTER.md`, a contract
battery holding the 48 `#guard`s and an axiom report holding the 28 `#print axioms`; the
deployment provider and the named environment (§4.7) are the part not yet written.
