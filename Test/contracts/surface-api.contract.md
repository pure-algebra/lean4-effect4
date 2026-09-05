# Surface API contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md`, §4.4 as revised by §13.1)

Implementation (owed): `src/Effect4/Surface/Api.lean`, `src/Effect4/Codegen/Target.lean`

Battery: `Test/Surface/ApiContract.lean`

Counterexamples: `E4-SURFACE-CE-016` through `E4-SURFACE-CE-037`,
`E4-SURFACE-CE-065`

Witnesses: `Test/Counterexamples/Surface/Api.lean`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet; this contract owns the endpoint, group and API clause names and
their order.

Pin: `effect` 4.0.0-rc.112,
`node_modules/effect/src/unstable/httpapi/HttpApiEndpoint.ts`

## Purpose

An HTTP surface as rows: methods, paths, four request slots, status-indexed
responses, a security list and the service names the handler needs. A Lean
term that elaborates and whose `check` is `.ok ()` is an endpoint rc.112
constructs without throwing.

Plan §13.1 is the design input, and it changes the shape from §4.4: responses
are status-indexed lists with a three-armed body and optional headers, so that
the carrier can *express* every shape rc.112's eleven construction-time throws
guard against. That is deliberate. A carrier that could not spell a streaming
success would delete `HttpApiEndpoint.ts:1201` by making the whole feature
unsayable, which is a narrower model wearing a stronger claim; a carrier that
can spell it and refuses it by a named clause retires the throw and says
exactly what it retired.

**Every one of the eleven throw sites is a representable attack with a named
refusal.** None is deleted by absence.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
inductive Method
  | get | post | put | patch | delete | head | options
deriving DecidableEq, Repr

def Method.name : Method → String
def Method.allowsPayload : Method → Bool

inductive Segment
  | literal (text : String)
  | param (name : String)
deriving DecidableEq, Repr

structure Path where
  segments : List Segment
deriving DecidableEq, Repr

def Path.render : Path → String
def Path.append : Path → Path → Path
def Path.paramNames : Path → List String

inductive PayloadEncoding
  | json | multipart | urlEncoded
deriving DecidableEq, Repr

def PayloadEncoding.contentType : PayloadEncoding → String

inductive Payload (refs : List Effect4.ReferenceEntry)
  | json (schema : Sch refs .json)
  | multipart (schema : Sch refs .multipart)
  | urlEncoded (schema : Sch refs .urlEncoded)

def Payload.encoding {refs} : Payload refs → PayloadEncoding

inductive ResponseBody (refs : List Effect4.ReferenceEntry)
  | void
  | json (schema : Sch refs .json)
  | stream (schema : Sch refs .stream) (contentType : String)
            (sseEventNames : List String)

def ResponseBody.isStream {refs} : ResponseBody refs → Bool
def ResponseBody.isVoid {refs} : ResponseBody refs → Bool
def ResponseBody.contentType {refs} : ResponseBody refs → String

structure Response (refs : List Effect4.ReferenceEntry) where
  status  : Nat
  body    : ResponseBody refs
  headers : Option (Sch refs .text) := none

inductive SecurityIn
  | header | query | cookie
deriving DecidableEq, Repr

inductive Security
  | bearer
  | apiKey (location : SecurityIn) (name : String)
  | basic
deriving DecidableEq, Repr

structure Endpoint (refs : List Effect4.ReferenceEntry) where
  id          : String
  method      : Method
  path        : Path
  annotations : Effect4.Annotations := none
  params      : Option (Sch refs .text) := none
  query       : Option (Sch refs .text) := none
  headers     : Option (Sch refs .text) := none
  payloads    : List (Payload refs) := []
  success     : List (Response refs)
  errors      : List (Response refs) := []
  security    : List Security := []
  requires    : List String := []

structure Group (refs : List Effect4.ReferenceEntry) where
  id          : String
  annotations : Effect4.Annotations := none
  pathPrefix  : Option Path := none
  endpoints   : List (Endpoint refs)
  topLevel    : Bool := false

structure Api (refs : List Effect4.ReferenceEntry) where
  id          : String
  annotations : Effect4.Annotations := none
  pathPrefix  : Option Path := none
  groups      : List (Group refs)

def Endpoint.check {refs} (e : Endpoint refs) : Except Refusal Unit
def Endpoint.WellFormed {refs} (e : Endpoint refs) : Prop :=
  Endpoint.check e = .ok ()

def Group.check {refs} (g : Group refs) : Except Refusal Unit
def Group.WellFormed {refs} (g : Group refs) : Prop := Group.check g = .ok ()

def Api.check {refs} (a : Api refs) : Except Refusal Unit
def Api.WellFormed {refs} (a : Api refs) : Prop := Api.check a = .ok ()

def Api.fullPath {refs} (a : Api refs) (g : Group refs) (e : Endpoint refs) : Path
def Api.routes {refs} (a : Api refs) : List (Method × String)
def Api.endpoint? {refs} (a : Api refs) (groupId endpointId : String) :
    Option (Endpoint refs)
def Api.requirements {refs} (a : Api refs) : List String

-- the lifted clauses
def Endpoint.Described {refs} (e : Endpoint refs) : Prop
def Endpoint.ParamsMatchPath {refs} (e : Endpoint refs) : Prop
def Endpoint.BodylessHasNoPayload {refs} (e : Endpoint refs) : Prop
def Endpoint.StatusesDistinct {refs} (e : Endpoint refs) : Prop
def Endpoint.ResponsesWellShaped {refs} (e : Endpoint refs) : Prop
def Api.RoutesDistinct {refs} (a : Api refs) : Prop

theorem Endpoint.wellFormed_iff {refs} (e : Endpoint refs) :
    Endpoint.WellFormed e ↔
      (Endpoint.Described e ∧ Endpoint.ParamsMatchPath e ∧
        Endpoint.BodylessHasNoPayload e ∧ Endpoint.StatusesDistinct e ∧
        Endpoint.ResponsesWellShaped e)

theorem Endpoint.wellFormed_params_match {refs} (e : Endpoint refs) :
    Endpoint.WellFormed e →
      e.path.paramNames = (e.params.map Sch.propertyNames).getD []

theorem Api.routes_nodup {refs} (a : Api refs) :
    Api.WellFormed a → (Api.routes a).Nodup

-- src/Effect4/Codegen/Target.lean
def httpApiModule {refs} (a : Api refs) (dom : Domain) : Option TypeScript.Module
def clientModule {refs} (a : Api refs) : Option TypeScript.Module
def openApi {refs} (a : Api refs) (dom : Domain) : Option Effect4.Json
```

The plan §4.4 names the two prefix fields `prefix`. `prefix` is a reserved
token in Lean 4 (the `prefix:max … => …` notation command), so neither
`{ prefix := p }` nor `g.prefix` parses; the field is frozen as `pathPrefix`.
See finding 6 of the wave-1b report.

## Observations

1. `Endpoint.check e`, `Group.check g`, `Api.check a`, each
   `Except Refusal Unit`, compared against `.ok ()` or an exact `.error`.
2. `Api.routes a`, compared against a literal list of `(method, rendered
   path)` pairs.
3. `Path.render p`: exact bytes, including the leading slash and the `"/"`
   answer for the empty path.
4. The slot types, read by an ascribed definition, so a widening or a
   narrowing of a slot breaks the witness file.
5. `httpApiModule`, `clientModule`, `openApi`: `isSome` in this packet; exact
   bytes and host agreement in the harness.

## Clause order for `Endpoint.check`

`check` returns the **first** refusal, so this order is part of the contract.

| # | clause | refusal | id |
| --- | --- | --- | --- |
| 1 | `annotations` carries `identifier` | `identifierMissing "endpoint" e.id` | `E4-SURFACE-CE-065` |
| 2 | `annotations` carries `description` | `descriptionMissing "endpoint" e.id` | `E4-SURFACE-CE-065` |
| 3 | `e.id` is a legal target identifier | `nameIllegal "endpoint" e.id` | |
| 4 | path variables have no duplicates | `pathParamDuplicate e.id p` | `E4-SURFACE-CE-018` |
| 5 | every path variable is a property of `params` | `pathParamWithoutSchema e.id p` | `E4-SURFACE-CE-016` |
| 6 | every property of `params` is a path variable | `schemaParamWithoutPath e.id p` | `E4-SURFACE-CE-017` |
| 7 | `Method.allowsPayload e.method` or `e.payloads = []` | `payloadOnBodylessMethod e.id` | `019`, `020`, `021` |
| 8 | at most one payload per content type | `payloadEncodingDuplicate e.id ct` | `E4-SURFACE-CE-027` |
| 9 | at most one multipart payload | `multipartPayloadDuplicate e.id ct` | `E4-SURFACE-CE-028` |
| 10 | `e.success ≠ []` | `successEmpty e.id` | |
| 11 | every status is in `100..599` | `statusOutOfRange e.id s` | `025`, `026` |
| 12 | no status appears twice across successes and errors | `statusCollision e.id s` | `023`, `024` |
| 13 | at most one streaming success | `streamSuccessDuplicate e.id` | `E4-SURFACE-CE-030` |
| 14 | no status carries both a void body and a stream | `streamWithVoidStatus e.id s` | `031`, `033` |
| 15 | no status carries both a buffered body and a stream of one content type | `streamWithBufferedStatus e.id s` | `032`, `034` |
| 16 | no error body is a stream | `errorBodyStreams e.id s` | `E4-SURFACE-CE-029` |
| 17 | at most one response with headers per status | `responseHeadersDuplicate e.id s` | `E4-SURFACE-CE-035` |
| 18 | `e.method ≠ head` or no streaming success | `streamOnHeadMethod e.id` | `E4-SURFACE-CE-036` |
| 19 | no SSE event name is `effect/httpapi/stream/failure` | `sseEventNameReserved e.id n` | `E4-SURFACE-CE-037` |
| 20 | every `requires` name is legal | `requirementNameIllegal e.id s` | |

Clauses 12 and 14 stay separate from each other even though a void body is
also a body: `statusCollision` is about two responses claiming one status,
`streamWithVoidStatus` is about the rc.112 branch that reaches the same status
from the stream side. rc.112 has two code paths (`:1206` and `:1219`) and one
message; this packet keeps one clause and two counterexample rows, one per
rc.112 path, so a future streaming arm cannot reopen one path silently.

A `void` success is admitted at any status: rc.112 `HttpApiSchema.Empty(code)`
admits any code. The battery pins a `200` void success as admitted so a later
tightening is a visible change.

`Group.check`: identifier and description on the bag; endpoint ids distinct
(`endpointIdDuplicate`); every endpoint's own `check`.

`Api.check`: identifier and description; group ids distinct
(`groupIdDuplicate`); every group's `check`; no two endpoints share
`(method, fullPath)` over `a.pathPrefix ++ g.pathPrefix ++ e.path`
(`routeCollision`, `E4-SURFACE-CE-022`).

## The eleven throw sites of `HttpApiEndpoint.ts:1134-1306`

| line | rc.112 message | clause that retires it | id |
| --- | --- | --- | --- |
| 1134 | Multiple payload encodings for content-type | 8, `payloadEncodingDuplicate` | `E4-SURFACE-CE-027` |
| 1137 | Multiple multipart payloads for content-type | 9, `multipartPayloadDuplicate` | `E4-SURFACE-CE-028` |
| 1180 | Streaming schemas are not supported in error responses | 16, `errorBodyStreams` | `E4-SURFACE-CE-029` |
| 1201 | Multiple streaming success responses are not supported | 13, `streamSuccessDuplicate` | `E4-SURFACE-CE-030` |
| 1206 | Cannot combine no-content and streaming success responses (stream first) | 14, `streamWithVoidStatus` | `E4-SURFACE-CE-031` |
| 1209 | Cannot combine buffered and streaming success responses (stream first) | 15, `streamWithBufferedStatus` | `E4-SURFACE-CE-032` |
| 1219 | Cannot combine no-content and streaming success responses (buffered first) | 14, `streamWithVoidStatus` | `E4-SURFACE-CE-033` |
| 1225 | Cannot combine buffered and streaming success responses (buffered first) | 15, `streamWithBufferedStatus` | `E4-SURFACE-CE-034` |
| 1290 | Cannot declare multiple responses with headers for status | 17, `responseHeadersDuplicate` | `E4-SURFACE-CE-035` |
| 1303 | HEAD endpoints cannot declare streaming success responses | 18, `streamOnHeadMethod` | `E4-SURFACE-CE-036` |
| 1306 | SSE event name is reserved | 19, `sseEventNameReserved` | `E4-SURFACE-CE-037` |

The plan §3 says "nine construction-time throws". There are eleven in the
cited range. See finding 2 of the wave-1b report.

## Assurance allocation

Graph edge `SURFACE-PG-API`, with leaf receipts underneath.

- Admission and refusal is a judgment: graph, obligations
  `admission-positive` (the fixture endpoints hold by `decide`) and
  `admission-negative` (every counterexample above, each pinning its refusal
  value, not a Boolean).
- `Endpoint.wellFormed_iff`, `Endpoint.wellFormed_params_match` and
  `Api.routes_nodup` carry the `laws` obligation. The first is what lets a
  capability (`surface-derive.contract.md`) ask for three clauses instead of
  the whole check; the other two are what a router generator relies on.
- `httpApiModule`, `clientModule`, `openApi` are three emitter rules with
  `Stance.emitted` at landing; their receipts are named in
  `surface-emit.contract.md`. They contribute to the `targets` edge, which
  stays open in this packet.

## What this contract does not claim

It does not claim an emitted `HttpApi` module behaves as the rows say at run
time; there is no run-agreement claim in this slice. It does not claim the
v1 *emitters* handle everything the carrier expresses: `multipart`,
`urlEncoded` and `stream` are expressible and are refused by rule id in
`surface-emit.contract.md`, and an endpoint that uses them is well formed and
emits nothing. It does not model middlewares, annotations beyond the two
mandatory keys, `disableCodecs`, or the string-tree codec transformation
rc.112 applies to params, query and headers. It does not model handlers;
`src/Effect4/Surface/Handler.lean` (plan §13.2) is wave 2d and has no contract in
this packet, which is finding 9 of the wave-1b report.
