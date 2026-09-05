import Effect4.Program.Config
import Effect4.Store.Digest

/-!
# Surface.Observability — the signal records, the exporter configuration row, and the
trace-context codec

Design: `docs/research/2026-09-04-production-standards-spike.md` §3 rows 4–6 (the shapes),
§4 (the configuration algebra this module instantiates), §5 (knowledge / confidence /
control) and §9 lane **L5**. Everything is transcribed from the pin
`vendor/effect-4.0.0-rc.112/src` and `vendor/wrangler-3.114.16/config-schema.json`; every
fact carries its `file:lines`.

The module is in three parts, and only the middle one is a payoff:

* **§1–§6, the carriers.** `Resource`, `Span`, `LogRecord`, `MetricState` and the OTLP
  export records as first-order structures. These are *data*: they exist so that the owed
  `Tape → TraceData` fold (§3 row 5 of the note, `A7` of its grill) has a typed target
  instead of a slogan, and so that what rc.112 cannot carry into a total first-order model
  is named rather than faked. Nothing here is claimed to be proved.
* **§7, the exporter rows.** The four rc.112 exporters' `Config` reads as
  `Program.Config.ConfigTerm String` values, and the one sentence that is the point of the
  lane: *the operator contract of the observability stack is this residual*. It is one
  path — `OTEL_SERVICE_NAME` — and `required_nil_never_absent` is the theorem that makes
  "one path" mean something rather than being a table someone typed.
* **§8, trace-context propagation.** `HttpTraceContext.ts`'s printer and its three parsers.
  The identifiers are `List UInt8` and never `String` in a theorem: the `String` faces are
  executable and appear only in `#guard`s, because every function that *iterates* a
  `String` on this toolchain reaches `Classical.choice` (the module docstring of
  `Effect4/Program/Config.lean` records the measurement). The round trip is therefore
  stated on the structured codec, `decodeW3c (encodeW3c s) = some s`.

| | |
| --- | --- |
| Carrier | `AttrValue`/`KeyValue`/`Resource`; `Span` with `SpanKind`/`SpanStatus`/`SpanRef`/`SpanLink`; `LogRecord` with `LogLevel`; `MetricState`; `TraceData`/`ResourceSpan`/`ScopeSpan`/`OtlpSpan`; `WranglerObservability`; `ExternalSpan` |
| Operations | `resourceOfOptions`, `spanKindCode`, `logLevelOrdinal`; `otlpResourceReads`/`otlpTracerReads`/`otlpLoggerReads`/`otlpMetricsReads`/`otlpExporterEnv`/`observabilityReads`; `required`, `obsResidual`; `toHeaders`/`fromHeaders`, `encodeW3c`/`decodeW3c` |
| Laws | `decodeW3c_encodeW3c` (the propagation round trip), `required_nil_never_absent` (a term with no required path never comes back absent), `absent_names_missing` instantiated at the observability row, `spanKindCode_inj`, `logLevelOrdinal_inj` |
| Structure | one Lean structure per rc.112 interface, one `ConfigTerm` per `Config.*` call the exporters make, one codec per propagation format; no closures, no floats, no `String` inside a theorem |
| Payoff | `obsResidual []` is a one-element row and `obsResidual` of an env that sets `OTEL_SERVICE_NAME` is `Row.empty`: the whole `OTEL_*` surface of rc.112 asks the operator for exactly one value, and every other one of the twenty-eight names it reads has a default or is optional |
| Anti-vacuity | ten refusal rows `OBS-FB-001..010`; the `E4-OBS-CE-001..004` `#guard` pairs (§9); the twenty-eight-name census; the two concrete spans' round trip and the malformed header that answers `none` |
| Generation | none yet: the printer for these rows is the owed `Codegen/Config.lean` of the note's lane L3 |

## Refusal rows

Where rc.112's shape cannot be carried, the field is *absent and named* rather than
invented. Each row below is a place a reader would otherwise assume a fidelity this model
does not have.

| row | what rc.112 has | what is here, and why |
| --- | --- | --- |
| `OBS-FB-001` | `doubleValue: number` (`OtlpResource.ts:208-210`, `:248`); `HistogramState`'s `buckets`/`min`/`max`/`sum` and `SummaryState`'s `quantiles`/`min`/`max`/`sum` are `number` (`Metric.ts:711-717`, `:898-904`) | **no `Float` in any carrier.** `AttrValue` has `str`, `int`, `bool`, `arr` — the four branches `unknownToAttributeValue` can produce for an integer or a bigint (`:199-207`) — and a non-integral `number` attribute is *unrepresentable*, not silently rounded. The metric states carry `Int`. Lean's `Float` has no `DecidableEq` and its `BEq` is IEEE equality (`Effect4/Data/Json.lean` records the same ruling for the payload datum), so a `Float` field would cost every `deriving DecidableEq` below |
| `OBS-FB-002` | `Span.end`, `.attribute`, `.event`, `.addLinks` (`Tracer.ts:384-387`); `Tracer.make(options)` returns its argument (`Tracer.ts:455`) | **methods are host closures.** They are *operations* on a span, not fields of one, and a first-order record cannot hold them. `Span` below has the ten data fields of `Tracer.ts:372-383` and none of the four methods; `event` in particular means the OTLP `events` array (`OtlpTracer.ts:395`, `:402-407`) has no source inside this carrier |
| `OBS-FB-003` | `Logger.Options.cause : Cause<unknown>`, `.fiber : Fiber<unknown, unknown>`, `.date : Date` (`Logger.ts:101-107`); `SpanStatus.exit : Exit<unknown, unknown>` (`Tracer.ts:98`) | **opaque spellings.** `cause` is a rendered `String`, `fiber` is reduced to `fiberId : Nat`, `date` is the ISO-8601 `String`, and an ended span's `exit` is reduced to `exitOk : Bool` — exactly the bit `OtlpTracer.ts:438-440` reads out of it when it picks a `StatusCode` |
| `OBS-FB-004` | `AnyValue.kvlistValue`, `.bytesValue` (`OtlpResource.ts:253-255`); the `default:` branch formatting an arbitrary value (`:215-218`); `arrayValue`'s recursion (`:187-192`) | **`unknown` is not a carrier.** rc.112's own converter never produces `kvlistValue` or `bytesValue`, so neither is a constructor here; a value of no other type becomes a `str` in rc.112 by calling `format`, which is a host function and is not modelled. `AttrValue.arr` holds `AttrScalar`s, so an array **of arrays** is unrepresentable: the recursive spelling defeats `deriving DecidableEq` on this toolchain, and a carrier without decidable equality would cost every `#guard` in §2 and §6 |
| `OBS-FB-005` | `observability.head_sampling_rate` and `observability.logs.head_sampling_rate` are `"type": "number"` (`config-schema.json:1232-1235`, `:1242-1245`) | **per-mille `Nat`.** The field is `headSamplingRatePerMille : Option Nat`, read as thousandths, so `0.05` is `50` and a rate off the 0.001 grid is unrepresentable. A `Float` field here would be a fabrication of precision the emitter cannot round-trip and would break `DecidableEq` for the whole record (`OBS-FB-001`) |
| `OBS-FB-006` | `Config.int` is signed (`OtlpTracer.ts:171`); `Config.url` parses and *mutates* a URL (`otlpEnv.ts:23-31`); `Config.Record(StringFromUriComponent, …)` (`otlpEnv.ts:14`), `Config.Array(String)` lower-cased and filtered (`otlpEnv.ts:7-12`), `Config.literals([…])` (`OtlpMetrics.ts:524`) | **the row records the read, not the codec.** `Program.Config.ConfigTerm` has `string`/`nat`/`bool` only, so a negative timeout, the `v1/<signal>` path the endpoint fallback appends (`otlpEnv.ts:26-30`), the URI-component decode of the headers record and the lower-casing of the exporter list are all outside this carrier. What survives is what the residual is about: *which paths are read, and which of them the operator must set* |
| `OBS-FB-007` | `Span.parent : Option<AnySpan>` where `AnySpan = Span \| ExternalSpan` (`Tracer.ts:125`, `:377`); `toHeaders` appends `-${parent.spanId}` to the `b3` header (`HttpTraceContext.ts:44-47`) | **a parent is a `SpanRef`, not a span.** The recursive field is replaced by the three fields any propagation format actually reads. The consequence is visible in §8: `ExternalSpan` has no parent (`Tracer.ts:199-205`), so `toHeaders` here emits the three-field `b3` and never the four-field one |
| `OBS-FB-008` | `Headers.Headers` are lower-cased at construction (`unstable/http/Headers.ts`) | **exact-match association list.** `lookupHeader` compares names verbatim, so `Traceparent` is not found where `traceparent` is. Every `#guard` below uses the lower-case spelling rc.112 stores |
| `OBS-FB-009` | `Config.all({…})` over a record, and a short circuit: a disabled or endpoint-less exporter returns before the second `Config.all` runs (`OtlpTracer.ts:166-168`, `OtlpLogger.ts:149-151`, `OtlpMetrics.ts:510-512`) | **`zip` is ordered and total.** The rows below fix a left-to-right nesting of pairs where rc.112 has an unordered record, and they read the timeout block unconditionally where rc.112 reads it only when the exporter is on. So `reads` is an *over*-approximation of a single run and an exact statement of the surface, which is the direction a requirement row must err in |
| `OBS-FB-010` | `Span.annotations : Context.Context<never>`, `ExternalSpan.annotations` (`Tracer.ts:378`, `:204`) | **a `List KeyValue`.** The annotation bag is a service map keyed by `Context` keys; the carrier keeps the attribute-shaped projection an exporter can print |

## The axiom receipt, measured on 2026-09-04

Every theorem in this module is `[propext]`, except `obsResidual_empty_of_subset`, which is
`[propext, Quot.sound]` through `Row`. Exactly five *executable* declarations reach
`Classical.choice`, all of them through `String.toList` or `String.splitOn` and all of them
in §8's `String` faces:

```text
parseHexId  w3c  b3  xb3  fromHeaders
```

They are the analogue of `Effect4/Program/Config.lean`'s `stdScalars`/`fromEnvRecord` and
belong in the gate's pinned choice list for the same reason: they are witnesses, no theorem
mentions them, and the structured codec (`encodeW3c`/`decodeW3c`/`splitN`) that the round
trip *is* about is clean. `toHeaders` is clean — `String.append` and `String.ofList` do not
iterate — so the printer costs nothing; only the parsers do.
-/

set_option autoImplicit false

namespace Effect4.Surface.Observability

open Effect4
open Effect4.Program.Config

/-! ## §1 Attributes

`unknownToAttributeValue` (`OtlpResource.ts:186-220`) is the only producer of an
`AnyValue` in rc.112, and it produces exactly four shapes: an array of values (`:187-192`),
a `stringValue` (`:195-197` and the `default:` branch `:215-218`), an `intValue` (`:199-201`
for a `bigint`, `:204-207` for an integral `number`) and a `boolValue` (`:211-213`). The
fifth, `doubleValue` (`:208-210`), is `OBS-FB-001`. -/

/-- The scalar branches of an OTLP `AnyValue`
(`OtlpResource.ts:195-197`, `:199-207`, `:211-218`). -/
inductive AttrScalar where
  /-- `stringValue` (`OtlpResource.ts:195-197`, `:215-218`). -/
  | str (s : String)
  /-- `intValue`; a `bigint` is rendered as a decimal string there (`OtlpResource.ts:199-201`)
  and an integral `number` is passed through (`:204-207`). -/
  | int (i : Int)
  /-- `boolValue` (`OtlpResource.ts:211-213`). -/
  | bool (b : Bool)
deriving DecidableEq, Repr

/-- An OTLP `AnyValue`, restricted to the branches `unknownToAttributeValue` produces
(`OtlpResource.ts:186-220`, `:241-256`). See `OBS-FB-001` and `OBS-FB-004`. -/
inductive AttrValue where
  /-- A scalar value. -/
  | scalar (v : AttrScalar)
  /-- `arrayValue` (`OtlpResource.ts:187-192`, `:264-267`), one level deep — `OBS-FB-004`. -/
  | arr (values : List AttrScalar)
deriving DecidableEq, Repr

/-- An OTLP `KeyValue` (`OtlpResource.ts:228-233`). -/
structure KeyValue where
  /-- `KeyValue key`. -/
  key : String
  /-- `KeyValue value`. -/
  value : AttrValue
deriving DecidableEq, Repr

/-! ## §2 The resource

Two records, because rc.112 has two: `Resource` is the *exported* shape
(`OtlpResource.ts:22-27`) and it has no `serviceName` field at all — the service identity
lives in the attribute list under the key `service.name`. What the note's §3 row 4 calls
"`Resource {serviceName, serviceVersion, attributes}`" is `make`'s *options* record
(`OtlpResource.ts:40-44`). Both are carried, and `resourceOfOptions` is `make`. -/

/-- The exported OTLP resource (`OtlpResource.ts:22-27`). -/
structure Resource where
  /-- Resource attributes. -/
  attributes : List KeyValue
  /-- Resource `droppedAttributesCount`; `make` always sets `0` (`OtlpResource.ts:65`). -/
  droppedAttributesCount : Nat
deriving DecidableEq, Repr

/-- The options `make` takes (`OtlpResource.ts:40-44`). -/
structure ResourceOptions where
  /-- `serviceName`, required (`OtlpResource.ts:41`). -/
  serviceName : String
  /-- `serviceVersion`, optional (`OtlpResource.ts:42`). -/
  serviceVersion : Option String
  /-- Additional attributes; `Record<string, unknown>` there (`OtlpResource.ts:43`), already
  converted here — see `OBS-FB-004`. -/
  attributes : List KeyValue
deriving DecidableEq, Repr

/-- `make` (`OtlpResource.ts:44-67`): the supplied attributes first, then `service.name`,
then `service.version` when it is present, and `droppedAttributesCount := 0`. -/
def resourceOfOptions (o : ResourceOptions) : Resource :=
  let base := o.attributes ++ [⟨"service.name", .scalar (.str o.serviceName)⟩]
  { attributes :=
      match o.serviceVersion with
      | some v => base ++ [⟨"service.version", .scalar (.str v)⟩]
      | none => base
    droppedAttributesCount := 0 }

/-- `serviceNameUnsafe` (`OtlpResource.ts:148-156`), total: the first `service.name`
attribute whose value is a string, and `none` where rc.112 throws (`:152-154`). -/
def serviceName? (r : Resource) : Option String :=
  match r.attributes.find? (fun kv => kv.key == "service.name") with
  | some ⟨_, .scalar (.str s)⟩ => some s
  | _ => none

private def demoResource : Resource :=
  resourceOfOptions
    ⟨"checkout", some "1.4.0", [⟨"deployment.environment", .scalar (.str "prod")⟩]⟩

#guard decide (demoResource.droppedAttributesCount = 0)
#guard decide (demoResource.attributes.length = 3)
#guard decide (serviceName? demoResource = some "checkout")
-- `make` pushes `service.name` *after* the supplied attributes (`OtlpResource.ts:45-53`).
#guard decide ((demoResource.attributes.map (fun kv => kv.key))
  = ["deployment.environment", "service.name", "service.version"])
-- No `serviceVersion`, no `service.version` attribute (`OtlpResource.ts:54-61`).
#guard decide ((resourceOfOptions ⟨"checkout", none, []⟩).attributes
  = [⟨"service.name", .scalar (.str "checkout")⟩])
#guard decide (serviceName? ⟨[], 0⟩ = none)

/-! ## §3 Spans -/

/-- `SpanKind` (`Tracer.ts:310`). -/
inductive SpanKind where
  /-- `"internal"`. -/
  | internal
  /-- `"server"`. -/
  | server
  /-- `"client"`. -/
  | client
  /-- `"producer"`. -/
  | producer
  /-- `"consumer"`. -/
  | consumer
deriving DecidableEq, Repr

/-- The OTLP wire code of a span kind (`OtlpTracer.ts:429-436`); `0` there is
`unspecified`, which no `Tracer.SpanKind` denotes. -/
def spanKindCode : SpanKind → Nat
  | .internal => 1
  | .server => 2
  | .client => 3
  | .producer => 4
  | .consumer => 5

/-- `SpanStatus` (`Tracer.ts:91-99`). Times are `bigint` nanoseconds there and `Nat` here;
`exit : Exit<unknown, unknown>` is reduced to the success bit — `OBS-FB-003`. -/
inductive SpanStatus where
  /-- `{ _tag: "Started", startTime }` (`Tracer.ts:92-93`). -/
  | started (startTime : Nat)
  /-- `{ _tag: "Ended", startTime, endTime, exit }` (`Tracer.ts:95-98`). -/
  | ended (startTime endTime : Nat) (exitOk : Bool)
deriving DecidableEq, Repr

/-- The OTLP status code a span status maps to (`OtlpTracer.ts:421-427`, `:438-440`):
a successful exit is `Ok`, a failed one is `Error`, and a span still running is `Unset`. -/
inductive StatusCode where
  /-- `StatusCode.Unset = 0`. -/
  | unset
  /-- `StatusCode.Ok = 1`. -/
  | ok
  /-- `StatusCode.Error = 2`. -/
  | error
deriving DecidableEq, Repr

/-- The wire numbers (`OtlpTracer.ts:421-425`). -/
def statusCodeNumber : StatusCode → Nat
  | .unset => 0
  | .ok => 1
  | .error => 2

/-- What a propagation format and a `SpanLink` actually read out of a span: its two
identifiers and its sampling bit. This is `ExternalSpan` minus its annotations
(`Tracer.ts:199-205`) and the projection `OBS-FB-007` replaces `AnySpan` by. -/
structure SpanRef where
  /-- `traceId` (`Tracer.ts:202`). -/
  traceId : String
  /-- `spanId` (`Tracer.ts:201`). -/
  spanId : String
  /-- `sampled`, defaulting to `true` (`Tracer.ts:203`, `:507`). -/
  sampled : Bool
deriving DecidableEq, Repr

/-- `SpanLink` (`Tracer.ts:431-434`). -/
structure SpanLink where
  /-- The linked span (`Tracer.ts:432`); an `AnySpan` there — `OBS-FB-007`. -/
  span : SpanRef
  /-- `Readonly<Record<string, unknown>>` there (`Tracer.ts:433`) — `OBS-FB-004`. -/
  attributes : List KeyValue
deriving DecidableEq, Repr

/-- `Span` (`Tracer.ts:372-388`), data fields only: the four methods at `:384-387` are
`OBS-FB-002`. -/
structure Span where
  /-- `name` (`Tracer.ts:374`). -/
  name : String
  /-- `spanId` (`Tracer.ts:375`). -/
  spanId : String
  /-- `traceId` (`Tracer.ts:376`). -/
  traceId : String
  /-- `parent : Option.Option<AnySpan>` (`Tracer.ts:377`) — `OBS-FB-007`. -/
  parent : Option SpanRef
  /-- `annotations : Context.Context<never>` (`Tracer.ts:378`) — `OBS-FB-010`. -/
  annotations : List KeyValue
  /-- `status` (`Tracer.ts:379`). -/
  status : SpanStatus
  /-- `attributes : ReadonlyMap<string, unknown>` (`Tracer.ts:380`) — `OBS-FB-004`. -/
  attributes : List KeyValue
  /-- `links` (`Tracer.ts:381`). -/
  links : List SpanLink
  /-- `sampled` (`Tracer.ts:382`). -/
  sampled : Bool
  /-- `kind` (`Tracer.ts:383`). -/
  kind : SpanKind
deriving DecidableEq, Repr

/-- The five kinds have five distinct wire codes — the anti-vacuity of `spanKindCode`,
which would otherwise be satisfiable by a constant. -/
theorem spanKindCode_inj (a b : SpanKind) (h : spanKindCode a = spanKindCode b) : a = b := by
  cases a <;> cases b <;> simp_all [spanKindCode]

/-- Likewise for the three status codes (`OtlpTracer.ts:421-425`). -/
theorem statusCodeNumber_inj (a b : StatusCode) (h : statusCodeNumber a = statusCodeNumber b) :
    a = b := by
  cases a <;> cases b <;> simp_all [statusCodeNumber]

/-! ## §4 Logs -/

/-- `LogLevel` (`LogLevel.ts:67`); `Severity` (`:87`) is the six concrete middle
constructors. -/
inductive LogLevel where
  /-- `"All"`, the least restrictive (`LogLevel.ts:125-126`). -/
  | all
  /-- `"Fatal"`. -/
  | fatal
  /-- `"Error"`. -/
  | error
  /-- `"Warn"`. -/
  | warn
  /-- `"Info"`. -/
  | info
  /-- `"Debug"`. -/
  | debug
  /-- `"Trace"`. -/
  | trace
  /-- `"None"`, the most restrictive (`LogLevel.ts:125-126`). -/
  | none
deriving DecidableEq, Repr

/-- The severity order, as the position in `LogLevel.values` (`LogLevel.ts:114`, and
`getOrdinal` at `:198`): `All` through the six severities to `None`. -/
def logLevelOrdinal : LogLevel → Nat
  | .all => 0
  | .fatal => 1
  | .error => 2
  | .warn => 3
  | .info => 4
  | .debug => 5
  | .trace => 6
  | .none => 7

/-- `LogLevel.values` (`LogLevel.ts:114`), in the order the array has. -/
def logLevelValues : List LogLevel :=
  [.all, .fatal, .error, .warn, .info, .debug, .trace, .none]

/-- `LogLevel.isGreaterThan` at the ordinal (`LogLevel.ts:236`, `:198`). -/
def logLevelGreater (a b : LogLevel) : Bool := logLevelOrdinal b < logLevelOrdinal a

/-- `Logger.Options` (`Logger.ts:101-107`). `cause`, `fiber` and `date` are `OBS-FB-003`. -/
structure LogRecord where
  /-- `message : Message` (`Logger.ts:102`), rendered. -/
  message : String
  /-- `logLevel` (`Logger.ts:103`). -/
  logLevel : LogLevel
  /-- `cause : Cause.Cause<unknown>` (`Logger.ts:104`), as its rendered spelling; the empty
  string is rc.112's `hasCause: false` case (`Logger.ts:95`). -/
  cause : String
  /-- `fiber : Fiber.Fiber<unknown, unknown>` (`Logger.ts:105`), reduced to its id. -/
  fiberId : Nat
  /-- `date : Date` (`Logger.ts:106`), as ISO-8601. -/
  date : String
deriving DecidableEq, Repr

/-- The eight levels have eight distinct ordinals: `LogLevel.Order` (`LogLevel.ts:141`) is
a total order, not a preorder with ties. -/
theorem logLevelOrdinal_inj (a b : LogLevel) (h : logLevelOrdinal a = logLevelOrdinal b) :
    a = b := by
  cases a <;> cases b <;> simp_all [logLevelOrdinal]

#guard decide (logLevelValues.length = 8)
#guard decide ((logLevelValues.map logLevelOrdinal) = [0, 1, 2, 3, 4, 5, 6, 7])
-- `LogLevel.Order("Error", "Info") // => 1` (`LogLevel.ts:133`): `Error` is more severe.
#guard logLevelGreater .info .error
#guard !logLevelGreater .error .info
-- `LogLevel.Order("Info", "Info") // => 0` (`LogLevel.ts:135`).
#guard !logLevelGreater .info .info

/-! ## §5 Metric states

The five states of `Metric.ts`. Every `number` field is `Int` here — `OBS-FB-001`. -/

/-- `CounterState` (`Metric.ts:249-252`), `FrequencyState` (`:407-409`), `GaugeState`
(`:536-538`), `HistogramState` (`:711-717`) and `SummaryState` (`:898-904`) as one sum. -/
inductive MetricState where
  /-- `CounterState { count, incremental }` (`Metric.ts:249-252`); `count` is
  `number | bigint` there. -/
  | counter (count : Int) (incremental : Bool)
  /-- `FrequencyState { occurrences : ReadonlyMap<string, number> }` (`Metric.ts:407-409`). -/
  | frequency (occurrences : List (String × Nat))
  /-- `GaugeState { value }` (`Metric.ts:536-538`); `number | bigint` there. -/
  | gauge (value : Int)
  /-- `HistogramState { buckets, count, min, max, sum }` (`Metric.ts:711-717`); the bucket
  boundaries and the three statistics are `number` there — `OBS-FB-001`. -/
  | histogram (buckets : List (Int × Nat)) (count : Nat) (min max sum : Int)
  /-- `SummaryState { quantiles, count, min, max, sum }` (`Metric.ts:898-904`); a quantile's
  value is `number | undefined` there. -/
  | summary (quantiles : List (Int × Option Int)) (count : Nat) (min max sum : Int)
deriving DecidableEq, Repr

#guard decide (MetricState.counter 3 true ≠ MetricState.counter 3 false)
#guard decide (MetricState.gauge (-2) ≠ MetricState.counter (-2) false)

/-! ## §6 The OTLP export records and the wrangler block -/

/-- `Event` (`OtlpTracer.ts:402-407`). -/
structure OtlpEvent where
  /-- `attributes`. -/
  attributes : List KeyValue
  /-- `name`. -/
  name : String
  /-- `timeUnixNano`, a decimal string on the wire. -/
  timeUnixNano : String
  /-- `droppedAttributesCount`. -/
  droppedAttributesCount : Nat
deriving DecidableEq, Repr

/-- `Link` (`OtlpTracer.ts:409-414`). -/
structure OtlpLink where
  /-- `attributes`. -/
  attributes : List KeyValue
  /-- `spanId`. -/
  spanId : String
  /-- `traceId`. -/
  traceId : String
  /-- `droppedAttributesCount`. -/
  droppedAttributesCount : Nat
deriving DecidableEq, Repr

/-- `Status` (`OtlpTracer.ts:416-419`). -/
structure OtlpStatus where
  /-- `code`. -/
  code : StatusCode
  /-- `message?`. -/
  message : Option String
deriving DecidableEq, Repr

/-- `OtlpSpan` (`OtlpTracer.ts:385-400`). `kind` is the wire number of
`OtlpTracer.ts:429-436`, not a `Tracer.SpanKind`. -/
structure OtlpSpan where
  /-- `traceId`. -/
  traceId : String
  /-- `spanId`. -/
  spanId : String
  /-- `parentSpanId : string | undefined`. -/
  parentSpanId : Option String
  /-- `name`. -/
  name : String
  /-- `kind : number` (`OtlpTracer.ts:390`, `:429-436`). -/
  kind : Nat
  /-- `startTimeUnixNano`. -/
  startTimeUnixNano : String
  /-- `endTimeUnixNano`. -/
  endTimeUnixNano : String
  /-- `attributes`. -/
  attributes : List KeyValue
  /-- `droppedAttributesCount`. -/
  droppedAttributesCount : Nat
  /-- `events`. -/
  events : List OtlpEvent
  /-- `droppedEventsCount`. -/
  droppedEventsCount : Nat
  /-- `status`. -/
  status : OtlpStatus
  /-- `links`. -/
  links : List OtlpLink
  /-- `droppedLinksCount`. -/
  droppedLinksCount : Nat
deriving DecidableEq, Repr

/-- The instrumentation scope (`OtlpTracer.ts:381-383`). -/
structure Scope where
  /-- `name`. -/
  name : String
deriving DecidableEq, Repr

/-- `ScopeSpan` (`OtlpTracer.ts:375-379`). -/
structure ScopeSpan where
  /-- `scope`. -/
  scope : Scope
  /-- `spans`. -/
  spans : List OtlpSpan
  /-- `schemaUrl?`. -/
  schemaUrl : Option String
deriving DecidableEq, Repr

/-- `ResourceSpan` (`OtlpTracer.ts:363-367`). -/
structure ResourceSpan where
  /-- `resource`. -/
  resource : Resource
  /-- `scopeSpans`. -/
  scopeSpans : List ScopeSpan
  /-- `schemaUrl?`. -/
  schemaUrl : Option String
deriving DecidableEq, Repr

/-- `TraceData` (`OtlpTracer.ts:353-355`), the root payload of an OTLP traces export. This
is the typed target the owed `Tape → TraceData` fold of the note's §3 row 5 needs. -/
structure TraceData where
  /-- `resourceSpans`. -/
  resourceSpans : List ResourceSpan
deriving DecidableEq, Repr

private def demoOtlpSpan : OtlpSpan :=
  { traceId := "000102030405060708090a0b0c0d0e0f", spanId := "1011121314151617"
    parentSpanId := none, name := "GET /checkout", kind := spanKindCode .server
    startTimeUnixNano := "1000000000", endTimeUnixNano := "1500000000"
    attributes := [⟨"http.route", .scalar (.str "/checkout")⟩,
                   ⟨"http.status_code", .scalar (.int 200)⟩]
    droppedAttributesCount := 0, events := [], droppedEventsCount := 0
    status := ⟨.ok, none⟩, links := [], droppedLinksCount := 0 }

private def demoTraceData : TraceData :=
  ⟨[⟨demoResource, [⟨⟨"@effect/opentelemetry"⟩, [demoOtlpSpan], none⟩], none⟩]⟩

#guard decide (demoTraceData.resourceSpans.length = 1)
#guard decide (demoOtlpSpan.kind = 2)
#guard decide (statusCodeNumber demoOtlpSpan.status.code = 1)

/-- The wrangler `observability.logs` block (`config-schema.json:1236-1252`). -/
structure WranglerObservabilityLogs where
  /-- `enabled` (`config-schema.json:1239-1241`). -/
  enabled : Option Bool
  /-- `head_sampling_rate` (`config-schema.json:1242-1245`), in thousandths —
  `OBS-FB-005`. -/
  headSamplingRatePerMille : Option Nat
  /-- `invocation_logs`: "Set to false to disable invocation logs"
  (`config-schema.json:1246-1249`). -/
  invocationLogs : Option Bool
deriving DecidableEq, Repr

/-- The wrangler `observability` block (`config-schema.json:1225-1255`);
`"additionalProperties": false` at `:1226`, so these three keys are the whole vocabulary. -/
structure WranglerObservability where
  /-- `enabled`: "If observability is enabled for this Worker"
  (`config-schema.json:1228-1231`). -/
  enabled : Option Bool
  /-- `head_sampling_rate` (`config-schema.json:1232-1235`), in thousandths —
  `OBS-FB-005`. -/
  headSamplingRatePerMille : Option Nat
  /-- `logs` (`config-schema.json:1236-1252`). -/
  logs : Option WranglerObservabilityLogs
deriving DecidableEq, Repr

/-- Every field of the block is optional, so the empty block is a value: wrangler's own
default is "no key at all". -/
def wranglerObservabilityEmpty : WranglerObservability := ⟨none, none, none⟩

private def demoWrangler : WranglerObservability :=
  ⟨some true, some 50, some ⟨some true, none, some false⟩⟩

#guard decide (demoWrangler.headSamplingRatePerMille = some 50)
#guard decide (wranglerObservabilityEmpty.logs = none)
#guard decide (demoWrangler ≠ wranglerObservabilityEmpty)

/-! ## §7 The exporter configuration row — the payoff

Every `Config.*` call the four rc.112 exporters make, as a `ConfigTerm String`, composed
exactly as the sources compose them: a fallback chain is `.orElse`, an optional read is
`.option`, a default is `.withDefault`, and `Config.all` over a record is a right-nested
`.zip` (`OBS-FB-009`).

**The operator contract of the observability stack is this residual.** `observabilityReads`
names twenty-eight environment variables; `required` — the sublist whose absence the term
cannot absorb — has exactly one element, `OTEL_SERVICE_NAME`, and
`required_nil_never_absent` is what makes that a statement about evaluation rather than a
table. rc.112 agrees by dying there: `fromConfig` is `Effect.orDie` over a required
`Config.string("OTEL_SERVICE_NAME")` (`OtlpResource.ts:111`, `:131`). The tri-state reader
sees the same fact as an *absence*, with the path, before the host dies. -/

/-- `OtlpEnv.headers(signal)` (`otlpEnv.ts:16-20`): the per-signal record, else the shared
one, else `undefined`. The record codec itself is `OBS-FB-006`. -/
def otlpHeaders (signal : String) : ConfigTerm String :=
  .withDefault
    (.orElse (.string ("OTEL_EXPORTER_OTLP_" ++ signal ++ "_HEADERS"))
             (.string "OTEL_EXPORTER_OTLP_HEADERS"))
    Val.none

/-- `OtlpEnv.endpoint(signal)` (`otlpEnv.ts:22-34`): the per-signal URL, else the shared one
with `v1/<signal>` appended to its path, else `undefined`. The URL parse and that path
mutation (`otlpEnv.ts:26-30`) are `OBS-FB-006`. -/
def otlpEndpoint (signal : String) : ConfigTerm String :=
  .withDefault
    (.orElse (.string ("OTEL_EXPORTER_OTLP_" ++ signal ++ "_ENDPOINT"))
             (.string "OTEL_EXPORTER_OTLP_ENDPOINT"))
    Val.none

/-- `OtlpEnv.exporters(signal)` (`otlpEnv.ts:36-39`): the exporter list, defaulting to the
empty array. The list's lower-casing and filtering (`otlpEnv.ts:9`) are `OBS-FB-006`; the
empty array is spelled `Val.str ""`. -/
def otlpExporters (signal : String) : ConfigTerm String :=
  .withDefault (.string ("OTEL_" ++ signal ++ "_EXPORTER")) (Val.str "")

/-- The three reads `internal/otlpEnv.ts` performs for one signal (`:16-39`). -/
def otlpExporterEnv (signal : String) : ConfigTerm String :=
  .zip (otlpHeaders signal) (.zip (otlpEndpoint signal) (otlpExporters signal))

/-- The `OTEL_SDK_DISABLED` read the three exporters share
(`OtlpTracer.ts:161`, `OtlpLogger.ts:144`, `OtlpMetrics.ts:506`). -/
def sdkDisabledRead : ConfigTerm String :=
  .withDefault (.bool "OTEL_SDK_DISABLED") (Val.bool false)

/-- `OtlpResource.fromConfig` (`OtlpResource.ts:91-131`).

The `??` chain at `:107-111` reads `OTEL_SERVICE_NAME` twice: once through
`Schema.UndefinedOr(Schema.String)` (`:109`), which is an *optional* read, and once through
the bare `Config.string` (`:111`), which is the required one and the reason the whole
constructor is `Effect.orDie` (`:131`). Both reads are kept, in that order, because the row
is about paths and both are paths this constructor may load. -/
def otlpResourceReads : ConfigTerm String :=
  .zip
    (.option (.string "OTEL_RESOURCE_ATTRIBUTES"))                    -- `:102-105`
    (.zip
      (.zip (.option (.string "OTEL_SERVICE_NAME"))                   -- `:109`
            (.string "OTEL_SERVICE_NAME"))                            -- `:111`, required
      (.option (.string "OTEL_SERVICE_VERSION")))                     -- `:115`

/-- `OtlpTracer.layerFromConfig` (`OtlpTracer.ts:160-189`). The second `Config.all`
(`:170-180`) is read unconditionally here — `OBS-FB-009` — and `Config.int` is signed —
`OBS-FB-006`. -/
def otlpTracerReads : ConfigTerm String :=
  .zip
    (.zip sdkDisabledRead                                             -- `:161`
          (.zip (otlpEndpoint "TRACES") (otlpExporters "TRACES")))    -- `:162-163`
    (.zip
      (.zip (.option (.nat "OTEL_EXPORTER_OTLP_TIMEOUT"))             -- `:171`
            (.option (.nat "OTEL_EXPORTER_OTLP_TRACES_TIMEOUT")))     -- `:172`
      (.zip
        (.zip (.option (.nat "OTEL_BSP_EXPORT_TIMEOUT"))              -- `:173`
              (.option (.nat "OTEL_BSP_SCHEDULE_DELAY")))             -- `:174-178`
        (.zip (.option (.nat "OTEL_BSP_MAX_EXPORT_BATCH_SIZE"))       -- `:179`
              (otlpHeaders "TRACES"))))                               -- `:189`

/-- `OtlpLogger.layerFromConfig` (`OtlpLogger.ts:143-169`). The batch keys are `BLRP`, not
`BSP`: the log record processor is a different processor from the batch span processor. -/
def otlpLoggerReads : ConfigTerm String :=
  .zip
    (.zip sdkDisabledRead                                             -- `:144`
          (.zip (otlpEndpoint "LOGS") (otlpExporters "LOGS")))        -- `:145-146`
    (.zip
      (.zip (.option (.nat "OTEL_EXPORTER_OTLP_TIMEOUT"))             -- `:154`
            (.option (.nat "OTEL_EXPORTER_OTLP_LOGS_TIMEOUT")))       -- `:155`
      (.zip
        (.zip (.option (.nat "OTEL_BLRP_EXPORT_TIMEOUT"))             -- `:156`
              (.option (.nat "OTEL_BLRP_SCHEDULE_DELAY")))            -- `:157`
        (.zip (.option (.nat "OTEL_BLRP_MAX_EXPORT_BATCH_SIZE"))      -- `:158`
              (otlpHeaders "LOGS"))))                                 -- `:169`

/-- `OtlpMetrics.layerFromConfig` (`OtlpMetrics.ts:505-535`). Unlike the other two this one
has no `MAX_EXPORT_BATCH_SIZE` and does have a temporality preference, read through
`Config.literals(["delta", "cumulative"], …)` (`:524`) — a scalar with an admission set, and
the admission set is `OBS-FB-006`. -/
def otlpMetricsReads : ConfigTerm String :=
  .zip
    (.zip sdkDisabledRead                                             -- `:506`
          (.zip (otlpEndpoint "METRICS") (otlpExporters "METRICS")))  -- `:507-508`
    (.zip
      (.zip (.option (.nat "OTEL_EXPORTER_OTLP_TIMEOUT"))             -- `:515`
            (.option (.nat "OTEL_EXPORTER_OTLP_METRICS_TIMEOUT")))    -- `:516`
      (.zip
        (.zip (.option (.nat "OTEL_METRIC_EXPORT_TIMEOUT"))           -- `:517`
              (.option (.nat "OTEL_METRIC_EXPORT_INTERVAL")))         -- `:518-522`
        (.zip (.option (.string "OTEL_EXPORTER_OTLP_METRICS_TEMPORALITY_PREFERENCE"))
              (otlpHeaders "METRICS"))))                              -- `:523-524`, `:535`

/-- The whole `OTEL_*` surface rc.112 reads: the resource plus the three exporters. -/
def observabilityReads : ConfigTerm String :=
  .zip otlpResourceReads (.zip otlpTracerReads (.zip otlpLoggerReads otlpMetricsReads))

/-- Every path the observability stack may load, in source order and with the duplicate
`OTEL_SERVICE_NAME` of `OtlpResource.ts:109`/`:111` and the shared keys repeated once per
signal — `reads` is a multiset of read *sites*, not a set of names. -/
def observabilityPaths : List (Path String) := reads [] observabilityReads

private def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as => let r := dedup as; if r.contains a then r else a :: r

/-- The index table the residual row is taken over: the distinct paths of
`observabilityPaths`. -/
def observabilityTable : List (Path String) := dedup observabilityPaths

/-- The environment variable names a term reads, deduplicated. Every path in these rows is
a single key segment, because rc.112 spells its `OTEL_*` reads flat. -/
def readNames (c : ConfigTerm String) : List String :=
  dedup ((reads [] c).filterMap
    (fun p => match p with | [Seg.key n] => some n | _ => none))

private def sameNames (a b : List String) : Bool :=
  a.length == b.length && a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

/-- The twenty-eight names, alphabetically. This is the census the note's §3 row 4 asks for:
one operator-visible surface, frozen at the pin. -/
def observabilityEnvNames : List String :=
  ["OTEL_BLRP_EXPORT_TIMEOUT",
   "OTEL_BLRP_MAX_EXPORT_BATCH_SIZE",
   "OTEL_BLRP_SCHEDULE_DELAY",
   "OTEL_BSP_EXPORT_TIMEOUT",
   "OTEL_BSP_MAX_EXPORT_BATCH_SIZE",
   "OTEL_BSP_SCHEDULE_DELAY",
   "OTEL_EXPORTER_OTLP_ENDPOINT",
   "OTEL_EXPORTER_OTLP_HEADERS",
   "OTEL_EXPORTER_OTLP_LOGS_ENDPOINT",
   "OTEL_EXPORTER_OTLP_LOGS_HEADERS",
   "OTEL_EXPORTER_OTLP_LOGS_TIMEOUT",
   "OTEL_EXPORTER_OTLP_METRICS_ENDPOINT",
   "OTEL_EXPORTER_OTLP_METRICS_HEADERS",
   "OTEL_EXPORTER_OTLP_METRICS_TEMPORALITY_PREFERENCE",
   "OTEL_EXPORTER_OTLP_METRICS_TIMEOUT",
   "OTEL_EXPORTER_OTLP_TIMEOUT",
   "OTEL_EXPORTER_OTLP_TRACES_ENDPOINT",
   "OTEL_EXPORTER_OTLP_TRACES_HEADERS",
   "OTEL_EXPORTER_OTLP_TRACES_TIMEOUT",
   "OTEL_LOGS_EXPORTER",
   "OTEL_METRICS_EXPORTER",
   "OTEL_METRIC_EXPORT_INTERVAL",
   "OTEL_METRIC_EXPORT_TIMEOUT",
   "OTEL_RESOURCE_ATTRIBUTES",
   "OTEL_SDK_DISABLED",
   "OTEL_SERVICE_NAME",
   "OTEL_SERVICE_VERSION",
   "OTEL_TRACES_EXPORTER"]

#guard decide (observabilityEnvNames.length = 28)
#guard sameNames (readNames observabilityReads) observabilityEnvNames
-- Each exporter's own share of the surface.
#guard decide ((readNames otlpResourceReads).length = 3)
#guard decide ((readNames otlpTracerReads).length = 11)
#guard decide ((readNames otlpLoggerReads).length = 11)
#guard decide ((readNames otlpMetricsReads).length = 11)
-- `internal/otlpEnv.ts` is the shared part: three per-signal names and two shared ones.
#guard sameNames (readNames (otlpExporterEnv "TRACES"))
  ["OTEL_EXPORTER_OTLP_TRACES_HEADERS", "OTEL_EXPORTER_OTLP_HEADERS",
   "OTEL_EXPORTER_OTLP_TRACES_ENDPOINT", "OTEL_EXPORTER_OTLP_ENDPOINT",
   "OTEL_TRACES_EXPORTER"]

/-! ### Which reads the operator must answer

`reads` is every path a term *may* load. `required` is the sublist whose absence the term
cannot absorb: a `withDefault` fills an absence (`Config.ts:847-852`), an `option` turns it
into `none` (`:887-888`), and an `orElse`'s absence falls through to its fallback
(`:570-572`), so none of the three can make a group absent by itself. The two lemmas below
are local copies of private lemmas of `Effect4/Program/Config.lean`; they are restated here
rather than exported because they say nothing about configuration, only about the shape of
`recover` and `zipRes`.

`required` bounds *absence* only. A partially supplied group is a **failure**, not an
absence (`E4-CONF-CE-005`, `Config.ts:674-675`), and `required` says nothing about it. -/

/-- The paths whose absence a term cannot absorb. `orElse` lists both branches, which
over-approximates — the term is absent only if both are — and is exact for these rows,
where every `orElse` sits under a `withDefault` and contributes nothing. -/
def required {Name : Type} (q : Path Name) : ConfigTerm Name → List (Path Name)
  | .string n => [q ++ [Seg.key n]]
  | .nat n => [q ++ [Seg.key n]]
  | .bool n => [q ++ [Seg.key n]]
  | .succeed _ => []
  | .fail _ => []
  | .withDefault _ _ => []
  | .orElse c d => required q c ++ required q d
  | .option _ => []
  | .nested n c => required (q ++ [Seg.key n]) c
  | .zip a b => required q a ++ required q b

private theorem recover_absent' {Name : Type} {f : Failure Name} {x : Outcome Name}
    {e : ConfigError Name} (h : recover f x = .ok (.absent e)) : x = .ok (.absent e) := by
  cases x with
  | error g => simp [recover] at h
  | ok r =>
    cases r with
    | resolved v hi => simp [recover] at h
    | absent e' =>
      simp only [recover] at h
      split at h
      · simp at h
      · exact h

private theorem zipRes_absent' {Name : Type} {x y : Outcome Name} {e : ConfigError Name}
    (h : zipRes x y = .ok (.absent e)) : x = .ok (.absent e) ∨ y = .ok (.absent e) := by
  cases x with
  | error f =>
    cases y with
    | error g => simp [zipRes] at h
    | ok s => cases s <;> simp [zipRes] at h
  | ok r =>
    cases r with
    | resolved v hi =>
      cases y with
      | error g => simp [zipRes] at h
      | ok s =>
        cases s with
        | resolved w k => simp [zipRes] at h
        | absent e' =>
          simp only [zipRes] at h
          split at h
          · simp at h
          · exact Or.inr h
    | absent e' =>
      cases y with
      | error g => simp [zipRes] at h
      | ok s =>
        cases s with
        | resolved w k =>
          simp only [zipRes] at h
          split at h
          · simp at h
          · exact Or.inl h
        | absent e2 =>
          simp only [zipRes] at h
          exact Or.inl h

/-- **A term with no required path never comes back absent.** This is what turns `required`
from a table someone typed into a statement about evaluation: it holds for *every* provider
and every prefix, so `required [] observabilityReads = [OTEL_SERVICE_NAME]` says that if the
operator sets that one name, no read of the observability stack can report an absence. It
says nothing about failure — a supplied value that does not decode, and a partially supplied
group, are both failures (`E4-CONF-CE-005`). -/
theorem required_nil_never_absent {Name : Type} (S : Scalars) (P : Provider Name) :
    ∀ (c : ConfigTerm Name) (q : Path Name) (e : ConfigError Name),
      required q c = [] → eval S c P q ≠ .ok (.absent e) := by
  intro c
  induction c with
  | string n => intro q e h; simp [required] at h
  | nat n => intro q e h; simp [required] at h
  | bool n => intro q e h; simp [required] at h
  | succeed v => intro q e _ h; simp [eval] at h
  | fail m => intro q e _ h; simp [eval] at h
  | withDefault c d _ =>
    intro q e _ h
    simp only [eval] at h
    revert h
    cases hc : eval S c P q with
    | error f => simp [defaultStep]
    | ok r => cases r <;> simp [defaultStep]
  | orElse c d ihc ihd =>
    intro q e hr h
    simp only [required, List.append_eq_nil_iff] at hr
    simp only [eval] at h
    revert h
    cases hc : eval S c P q with
    | error f =>
      intro h
      simp only [orElseStep] at h
      exact ihd q e hr.2 (recover_absent' h)
    | ok r =>
      cases r with
      | resolved v hi => intro h; simp [orElseStep] at h
      | absent e' =>
        intro h
        simp only [orElseStep] at h
        exact ihd q e hr.2 h
  | option c _ =>
    intro q e _ h
    simp only [eval] at h
    revert h
    cases hc : eval S c P q with
    | error f => simp [optionStep]
    | ok r => cases r <;> simp [optionStep]
  | nested n c ih => intro q e hr h; exact ih (q ++ [Seg.key n]) e hr h
  | zip a b iha ihb =>
    intro q e hr h
    simp only [required, List.append_eq_nil_iff] at hr
    simp only [eval] at h
    rcases zipRes_absent' h with ha | hb
    · exact iha q e hr.1 ha
    · exact ihb q e hr.2 hb

/-- The whole observability surface asks the operator for one value. -/
theorem observability_required :
    required [] observabilityReads = [[Seg.key "OTEL_SERVICE_NAME"]] := rfl

#guard decide (required [] otlpTracerReads = [])
#guard decide (required [] otlpLoggerReads = [])
#guard decide (required [] otlpMetricsReads = [])
#guard decide (required [] otlpResourceReads = [[Seg.key "OTEL_SERVICE_NAME"]])
#guard decide (required [] (otlpExporterEnv "LOGS") = [])

/-! ### The residual row

`E4-CONF-CE-002` of `Effect4/Program/Config.lean` is the reason the provider here is
`fromRecord` over one-segment paths and not `fromEnvRecord`: rc.112's env provider answers a
flat name at the joined spelling as well as at the split trie (`ConfigProvider.ts:1227` vs
`:1206-1207`), and the model keeps only the trie. `OTEL_SERVICE_NAME` is a read at *one*
segment, so the trie provider answers `none` for it while the host answers `"checkout"`. The
`E4-OBS-CE-002` pair below pins both readings. -/

/-- An environment as flat single-segment entries: the spelling rc.112 answers at
`ConfigProvider.ts:1227` and the one every `OTEL_*` read of §7 uses. -/
def flatEntries (env : List (String × String)) : List (Path String × String) :=
  env.map (fun kv => ([Seg.key kv.1], kv.2))

/-- The flat provider over such an environment. -/
def fromFlatEnv (env : List (String × String)) : Provider String :=
  fromRecord segName (flatEntries env)

/-- The row of required paths, over `observabilityTable`. -/
def requiredRow (c : ConfigTerm String) : Row ServiceKey :=
  Row.normalize ((required [] c).filterMap (fun p => (indexOf observabilityTable p).map keyOf))

/-- **The operator contract of the observability stack is this residual**: what the
deployment still owes, in the very carrier `Effect4/Machine/Context.lean` calls
`Requirement`. -/
def obsResidual (env : List (String × String)) : Row ServiceKey :=
  Row.diff (requiredRow observabilityReads) (providedRow observabilityTable (flatEntries env))

/-- Nothing is owed exactly when every required path is supplied — `Row.diff`'s law at this
instance, the same test a `Layer`'s closed-ness is. -/
theorem obsResidual_empty_of_subset (env : List (String × String))
    (h : Row.Subset (requiredRow observabilityReads)
      (providedRow observabilityTable (flatEntries env))) :
    obsResidual env = Row.empty :=
  (Row.diff_eq_empty_iff_subset _ _).mpr h

/-- **Absence names an unprovided path**, at the observability row: an absent read of the
stack is not a mystery, it is the name of an environment variable nobody set. This is
`Effect4/Program/Config.lean`'s `absent_names_missing` instantiated here, and it is the
other half of `required_nil_never_absent`. -/
theorem observability_absent_names_missing (S : Scalars) (env : List (String × String))
    (e : ConfigError String)
    (h : eval S observabilityReads (fromFlatEnv env) [] = .ok (.absent e)) :
    ∃ p, p ∈ observabilityPaths ∧ p ∉ provided (flatEntries env) :=
  absent_names_missing S segName (flatEntries env) observabilityReads [] e h

private def serviceNameOnly : List (String × String) := [("OTEL_SERVICE_NAME", "checkout")]

private def serviceNamePath : Path String := [Seg.key "OTEL_SERVICE_NAME"]

private def serviceNameKey : Option ServiceKey :=
  (indexOf observabilityTable serviceNamePath).map keyOf

#guard decide (observabilityTable.length = 28)
-- Thirty-seven read *sites*, twenty-eight distinct names: `OTEL_SDK_DISABLED`,
-- `OTEL_EXPORTER_OTLP_ENDPOINT`, `OTEL_EXPORTER_OTLP_TIMEOUT` and
-- `OTEL_EXPORTER_OTLP_HEADERS` are read once per exporter, and `OTEL_SERVICE_NAME` twice
-- in one constructor (`OtlpResource.ts:109`, `:111`).
#guard decide (observabilityPaths.length = 37)
-- The table indexes the required path, and the residual against an empty environment is
-- exactly that one row.
#guard decide ((indexOf observabilityTable serviceNamePath).isSome = true)
#guard decide (obsResidual [] = requiredRow observabilityReads)
#guard match serviceNameKey with
  | some k => decide (obsResidual [] = Row.singleton k)
  | none => false
#guard decide (obsResidual serviceNameOnly = Row.empty)
-- Setting anything else does not discharge it.
#guard decide (obsResidual [("OTEL_SERVICE_VERSION", "1.4.0")] = requiredRow observabilityReads)

/-! ### `E4-OBS-CE-001` — one variable is the whole contract

An environment that sets `OTEL_SERVICE_NAME` and nothing else resolves the entire
observability row; the empty environment is *absent*, and the absence names that very path.
The two `#guard`s would both have to change to fake the claim. -/

-- E4-OBS-CE-001: one name, and the whole stack resolves.
#guard match eval stdScalars observabilityReads (fromFlatEnv serviceNameOnly) [] with
  | .ok (.resolved _ _) => true
  | _ => false
-- E4-OBS-CE-001: nothing set, and the answer is an absence naming that same path.
#guard outcomeEq (eval stdScalars observabilityReads (fromFlatEnv []) [])
  (.ok (.absent (.missing serviceNamePath)))

/-! ### `E4-OBS-CE-002` — the flat spelling is what these reads need

`Config.string("OTEL_SERVICE_NAME")` is a read at the one-segment path
`["OTEL_SERVICE_NAME"]`. `fromEnvRecord` splits every env name on `_` into a trie
(`ConfigProvider.ts:1206-1207`) and does not answer the joined spelling (`E4-CONF-CE-002`),
so the trie provider reports the value *missing* where the host finds it. Anyone modelling
an `OTEL_*` row against `fromEnvRecord` gets a residual that is wrong in the dangerous
direction — it demands a variable the operator already set. -/

-- E4-OBS-CE-002: the flat provider answers, as rc.112's `fromEnv` does at `:1227`.
#guard outcomeEq (eval stdScalars (.string "OTEL_SERVICE_NAME") (fromFlatEnv serviceNameOnly) [])
  (.ok (.resolved (.str "checkout") true))
-- E4-OBS-CE-002: the segmented trie provider does not.
#guard outcomeEq
  (eval stdScalars (.string "OTEL_SERVICE_NAME") (fromEnvRecord serviceNameOnly) [])
  (.ok (.absent (.missing serviceNamePath)))

/-! ### `E4-OBS-CE-003` — a supplied value that does not decode is a failure, not an absence

`OTEL_SDK_DISABLED` carries a `withDefault(false)` (`OtlpTracer.ts:161`), and a reader might
conclude that a nonsense value is therefore harmless. It is not: `withDefault` replaces an
*absence*, and a supplied scalar that fails to decode is a hard failure with
`hasInput = true` (`Config.ts:1211-1212`, and `E4-CONF-CE-005`'s reading of `:847-852`). -/

-- E4-OBS-CE-003: unset, the default fires.
#guard outcomeEq (eval stdScalars sdkDisabledRead (fromFlatEnv []) [])
  (.ok (.resolved (.bool false) false))
-- E4-OBS-CE-003: set to a value `TrueValues`/`FalseValues` do not admit (`Config.ts:1224`,
-- `:1227`), it fails — the default does not rescue it.
#guard outcomeEq (eval stdScalars sdkDisabledRead (fromFlatEnv [("OTEL_SDK_DISABLED", "maybe")]) [])
  (.error ⟨.invalid [Seg.key "OTEL_SDK_DISABLED"] "expected a boolean", true⟩)

/-! ## §8 Trace-context propagation (`unstable/http/HttpTraceContext.ts:41-160`)

The identifiers are bytes. `traceparent`'s trace id is thirty-two hex digits and its span id
sixteen (`HttpTraceContext.ts:123-124`), i.e. sixteen and eight bytes; b3 uses the same two
identifiers. Modelling them as `String` would put `String` traversal inside the round trip
and therefore `Classical.choice` inside a theorem, so the law is stated on the structured
codec and the `String` faces are executable witnesses only. -/

/-- A W3C trace identifier: sixteen bytes, thirty-two hex digits
(`HttpTraceContext.ts:123`). The length is a hypothesis on the theorems rather than a field
of the type, so that the carrier stays a plain `List` and `decide` can run on it. -/
abbrev TraceId := List UInt8

/-- A span identifier: eight bytes, sixteen hex digits (`HttpTraceContext.ts:124`). -/
abbrev SpanId := List UInt8

/-- `Tracer.ExternalSpan` (`Tracer.ts:199-205`) with structural identifiers; its
`annotations` are `OBS-FB-010` and it has no parent, which is `OBS-FB-007`. -/
structure ExternalSpan where
  /-- `traceId` (`Tracer.ts:202`); sixteen bytes. -/
  traceId : TraceId
  /-- `spanId` (`Tracer.ts:201`); eight bytes. -/
  spanId : SpanId
  /-- `sampled`, defaulting to `true` when the header omits it (`Tracer.ts:507`,
  `HttpTraceContext.ts:97`, `:119`). -/
  sampled : Bool
deriving DecidableEq, Repr

/-- The W3C `traceparent` trace-flags octet (`HttpTraceContext.ts:153`: `parseInt(flags, 16)
& 1`). -/
abbrev Flags := UInt8

/-! ### The structured codec and its round trip

`traceparent` is `version "-" trace-id "-" parent-id "-" trace-flags`
(`HttpTraceContext.ts:49`, `:140-154`). Dropping the separators and the hex spelling leaves
exactly a byte string: one version byte, sixteen, eight, one. -/

/-- Take exactly `n` octets, or refuse: the total reading of a fixed-width field. -/
def splitN : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | n + 1, a :: rest => (splitN n rest).map (fun p => (a :: p.1, p.2))

private theorem splitN_append :
    ∀ (xs : List UInt8) (n : Nat) (ys : List UInt8), xs.length = n →
      splitN n (xs ++ ys) = some (xs, ys) := by
  intro xs
  induction xs with
  | nil =>
    intro n ys h
    cases n with
    | zero => rfl
    | succ m => exact absurd h.symm (Nat.succ_ne_zero m)
  | cons a as ih =>
    intro n ys h
    cases n with
    | zero => exact absurd h (Nat.succ_ne_zero as.length)
    | succ m =>
      have hm : as.length = m := Nat.succ.inj h
      show (splitN m (as ++ ys)).map (fun p => (a :: p.1, p.2)) = some (a :: as, ys)
      rw [ih m ys hm]
      rfl

/-- The `traceparent` octets: version `00` (`HttpTraceContext.ts:49`, `:146`), the trace id,
the span id, and the trace-flags octet whose low bit is `sampled` (`:153`). -/
def encodeW3c (s : ExternalSpan) : List UInt8 :=
  0 :: (s.traceId ++ (s.spanId ++ [if s.sampled then 1 else 0]))

/-- The inverse. A version other than `00` is refused, exactly as rc.112's `switch` refuses
it (`HttpTraceContext.ts:145-158`), and so is any length but 1 + 16 + 8 + 1. -/
def decodeW3c : List UInt8 → Option ExternalSpan
  | [] => none
  | ver :: rest =>
      if ver = 0 then
        match splitN 16 rest with
        | none => none
        | some (tid, body) =>
            match splitN 8 body with
            | some (sid, [f]) => some ⟨tid, sid, f % 2 == 1⟩
            | _ => none
      else none

/-- **The propagation round trip.** A well-formed external span survives `traceparent`
encoding and decoding on the nose. This is the law the note's §3 row 6 asks for, stated where
it can be proved: on the octets, not on the rendered header. -/
theorem decodeW3c_encodeW3c (s : ExternalSpan)
    (ht : s.traceId.length = 16) (hs : s.spanId.length = 8) :
    decodeW3c (encodeW3c s) = some s := by
  obtain ⟨tid, sid, sampled⟩ := s
  simp only at ht hs
  simp only [encodeW3c, decodeW3c, splitN_append tid 16 _ ht, splitN_append sid 8 _ hs]
  cases sampled <;> rfl

/-- The encoding has the shape the format fixes: twenty-six octets. -/
theorem encodeW3c_length (s : ExternalSpan)
    (ht : s.traceId.length = 16) (hs : s.spanId.length = 8) :
    (encodeW3c s).length = 26 := by
  simp [encodeW3c, ht, hs]

/-- A version octet other than `00` is refused (`HttpTraceContext.ts:145-158`). -/
theorem decodeW3c_version_ne (ver : UInt8) (rest : List UInt8) (h : ver ≠ 0) :
    decodeW3c (ver :: rest) = none := by
  simp [decodeW3c, h]

/-! ### The hex spelling and the `String` faces

The codec itself is the store's, `Effect4/Store/Digest.lean:204-207`: one hexadecimal codec in
the estate, proved there (`bytesOfHex_hexOfBytes` round trips, `hexOfBytes_bytesOfHex` is exact
up to case), read here through two thin faces because a trace header is a `String` and an
identifier is a byte list. The two names below keep their spellings and their guards; what they
no longer keep is a second nibble table.

Everything after them walks a `String` and is therefore *executable only*: `String.toList` and
`String.splitOn` reach `Classical.choice` on this toolchain, so no theorem mentions them.
They are pinned by `#guard`s, which is what the note's §5 calls the "probed" column. -/

/-- An identifier as its hex spelling: the store's printer, which writes lower case, which is
what rc.112 renders. -/
def hexOfBytes (bs : List UInt8) : String :=
  String.ofList (Effect4.Store.hexOfBytes bs)

/-- The octets a hex spelling denotes; an odd number of digits, or a non-hex digit, is
refused, and either case is read, because rc.112's identifier regexps carry the `i` flag
(`HttpTraceContext.ts:123-124`). The store's reader, exactly. -/
def bytesOfHex (cs : List Char) : Option (List UInt8) :=
  Effect4.Store.bytesOfHex cs

/-- An identifier of exactly `n` octets, or nothing: the structural reading of
`/^[0-9a-f]{32}$/i` and `/^[0-9a-f]{16}$/i` (`HttpTraceContext.ts:123-124`, `:147`). -/
def parseHexId (n : Nat) (s : String) : Option (List UInt8) :=
  match bytesOfHex s.toList with
  | some bs => if bs.length = n then some bs else none
  | none => none

/-- Exact-match header lookup — `OBS-FB-008`. -/
def lookupHeader (k : String) : List (String × String) → Option String
  | [] => none
  | (n, v) :: rest => if n = k then some v else lookupHeader k rest

/-- `toHeaders` (`HttpTraceContext.ts:41-50`): both the compact `b3` header and W3C
`traceparent`, in that record order. The fourth `b3` field, the parent's span id
(`:44-47`), is `OBS-FB-007`. -/
def toHeaders (s : ExternalSpan) : List (String × String) :=
  [("b3", hexOfBytes s.traceId ++ "-" ++ hexOfBytes s.spanId ++ "-" ++
      (if s.sampled then "1" else "0")),
   ("traceparent", "00-" ++ hexOfBytes s.traceId ++ "-" ++ hexOfBytes s.spanId ++ "-" ++
      (if s.sampled then "01" else "00"))]

/-- `w3c` (`HttpTraceContext.ts:136-159`): four dash-separated parts, version `00`, both
identifiers well formed, and `sampled` the low bit of the flags octet. -/
def w3c (hs : List (String × String)) : Option ExternalSpan :=
  match lookupHeader "traceparent" hs with
  | none => none
  | some raw =>
      match raw.splitOn "-" with
      | [version, tid, sid, flags] =>
          if version = "00" then
            match parseHexId 16 tid, parseHexId 8 sid, bytesOfHex flags.toList with
            | some t, some s, some [f] => some ⟨t, s, f % 2 == 1⟩
            | _, _, _ => none
          else none
      | _ => none

/-- `b3` (`HttpTraceContext.ts:86-99`): at least two dash-separated parts; a third part is
the sampling flag and *anything but the literal `"1"` means not sampled* — including the
Zipkin debug flag `"d"`, which rc.112 does not special-case (`:97`). A missing third part is
`true`. Unlike rc.112 this parser also validates the identifiers, because they are
structural here — the refusal is `OBS-FB-007`'s neighbour and is pinned by
`E4-OBS-CE-004`. -/
def b3 (hs : List (String × String)) : Option ExternalSpan :=
  match lookupHeader "b3" hs with
  | none => none
  | some raw =>
      match raw.splitOn "-" with
      | tid :: sid :: rest =>
          match parseHexId 16 tid, parseHexId 8 sid with
          | some t, some s =>
              some ⟨t, s, match rest with
                          | [] => true
                          | flag :: _ => flag == "1"⟩
          | _, _ => none
      | _ => none

/-- `xb3` (`HttpTraceContext.ts:112-121`): the multi-header form. -/
def xb3 (hs : List (String × String)) : Option ExternalSpan :=
  match lookupHeader "x-b3-traceid" hs, lookupHeader "x-b3-spanid" hs with
  | some tid, some sid =>
      match parseHexId 16 tid, parseHexId 8 sid with
      | some t, some s =>
          some ⟨t, s, match lookupHeader "x-b3-sampled" hs with
                      | none => true
                      | some v => v == "1"⟩
      | _, _ => none
  | _, _ => none

/-- `fromHeaders` (`HttpTraceContext.ts:63-73`): W3C first, then compact b3, then the
multi-header b3. -/
def fromHeaders (hs : List (String × String)) : Option ExternalSpan :=
  match w3c hs with
  | some s => some s
  | none =>
      match b3 hs with
      | some s => some s
      | none => xb3 hs

private def traceA : TraceId := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
private def spanA : SpanId := [16, 17, 18, 19, 20, 21, 22, 23]
private def traceB : TraceId := [255, 254, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204]
private def spanB : SpanId := [1, 0, 0, 0, 0, 0, 0, 255]

private def sampledSpan : ExternalSpan := ⟨traceA, spanA, true⟩
private def unsampledSpan : ExternalSpan := ⟨traceB, spanB, false⟩

#guard hexOfBytes traceA == "000102030405060708090a0b0c0d0e0f"
#guard hexOfBytes spanA == "1011121314151617"
#guard hexOfBytes traceB == "fffe0080112233445566778899aabbcc"
#guard decide (parseHexId 16 (hexOfBytes traceA) = some traceA)
#guard decide (parseHexId 8 (hexOfBytes spanB) = some spanB)
-- The identifier lengths are checked (`HttpTraceContext.ts:147`).
#guard decide (parseHexId 16 "00ff" = none)
#guard decide (parseHexId 8 "0102030405060708090a" = none)
-- An odd number of digits, and a non-hex digit, are refused.
#guard decide (bytesOfHex "abc".toList = none)
#guard decide (bytesOfHex "zz".toList = none)
-- Both cases parse (`HttpTraceContext.ts:123-124` carry the `i` flag).
#guard decide (bytesOfHex "AbCd".toList = bytesOfHex "abcd".toList)

-- The printed header shapes (`HttpTraceContext.ts:43-49`).
#guard decide ((toHeaders sampledSpan).map Prod.fst = ["b3", "traceparent"])
#guard lookupHeader "traceparent" (toHeaders sampledSpan) ==
  some "00-000102030405060708090a0b0c0d0e0f-1011121314151617-01"
#guard lookupHeader "b3" (toHeaders sampledSpan) ==
  some "000102030405060708090a0b0c0d0e0f-1011121314151617-1"
#guard lookupHeader "traceparent" (toHeaders unsampledSpan) ==
  some "00-fffe0080112233445566778899aabbcc-01000000000000ff-00"

-- The round trip through the `String` faces, on both spans.
#guard decide (fromHeaders (toHeaders sampledSpan) = some sampledSpan)
#guard decide (fromHeaders (toHeaders unsampledSpan) = some unsampledSpan)
-- The same round trip on the octets, the thing the theorem is about.
#guard decide (decodeW3c (encodeW3c sampledSpan) = some sampledSpan)
#guard decide (decodeW3c (encodeW3c unsampledSpan) = some unsampledSpan)

-- Malformed `traceparent`s answer `none` (`HttpTraceContext.ts:141-149`).
#guard decide (fromHeaders [("traceparent", "not-a-traceparent")] = none)
#guard decide (fromHeaders [("traceparent", "00-abc-def-01")] = none)
#guard decide (fromHeaders [("traceparent",
  "00-000102030405060708090a0b0c0d0e0f-1011121314151617")] = none)
-- Version `01` is refused, and nothing else in the record rescues it (`:156-158`).
#guard decide (fromHeaders [("traceparent",
  "01-000102030405060708090a0b0c0d0e0f-1011121314151617-01")] = none)

-- The fallback order: `traceparent` wins over a `b3` that names a different span (`:63-72`).
#guard decide (fromHeaders
  [("b3", "fffe0080112233445566778899aabbcc-01000000000000ff-0"),
   ("traceparent", "00-000102030405060708090a0b0c0d0e0f-1011121314151617-01")]
  = some sampledSpan)
-- With no `traceparent`, compact `b3` answers; with neither, the `x-b3-*` triple does.
#guard decide (fromHeaders
  [("b3", "000102030405060708090a0b0c0d0e0f-1011121314151617-1")] = some sampledSpan)
#guard decide (fromHeaders
  [("x-b3-traceid", "000102030405060708090a0b0c0d0e0f"),
   ("x-b3-spanid", "1011121314151617")] = some sampledSpan)
-- A missing sampling field is `true` (`:97`, `:119`).
#guard decide (fromHeaders
  [("b3", "000102030405060708090a0b0c0d0e0f-1011121314151617")] = some sampledSpan)
#guard decide (fromHeaders
  [("x-b3-traceid", "000102030405060708090a0b0c0d0e0f"),
   ("x-b3-spanid", "1011121314151617"), ("x-b3-sampled", "0")]
  = some ⟨traceA, spanA, false⟩)
-- Header names are matched verbatim (`OBS-FB-008`).
#guard decide (fromHeaders
  [("Traceparent", "00-000102030405060708090a0b0c0d0e0f-1011121314151617-01")] = none)

/-! ### `E4-OBS-CE-004` — the b3 debug flag is *not* sampled

Zipkin's b3 single-header format admits `d` in the sampling position to mean "debug, and
therefore sampled". rc.112 does not implement that: `sampled: parts[2] ? parts[2] === "1" :
true` (`HttpTraceContext.ts:97`) makes every spelling but the literal `"1"` unsampled, so a
debug-flagged request arrives with `sampled = false`. The pair below pins rc.112's reading
against the specification's. -/

-- E4-OBS-CE-004: rc.112 reads `d` as not sampled.
#guard decide (fromHeaders
  [("b3", "000102030405060708090a0b0c0d0e0f-1011121314151617-d")]
  = some ⟨traceA, spanA, false⟩)
-- E4-OBS-CE-004: only the literal `"1"` is sampled, and an omitted flag is.
#guard decide (fromHeaders
  [("b3", "000102030405060708090a0b0c0d0e0f-1011121314151617-1")]
  = some ⟨traceA, spanA, true⟩)

end Effect4.Surface.Observability
