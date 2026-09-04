/-
Executable witnesses for `E4-SURFACE-CE-016` through `E4-SURFACE-CE-037` and
`E4-SURFACE-CE-065`.

Contract: `test/contracts/surface-api.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Api.lean` exists; red until the builder lands
it.

Pin: `effect` 4.0.0-rc.112,
`node_modules/effect/src/unstable/httpapi/HttpApiEndpoint.ts`.

Plan §13.1 makes every shape the eleven construction-time throws guard against
*expressible*, so every one of them is a representable attack here with a
named refusal. That is the design choice worth stating: a carrier that could
not spell a streaming success would delete `:1201` by making the feature
unsayable, which is a narrower model wearing a stronger claim. A carrier that
can spell it and refuses it by a named clause retires the throw and says
exactly what it retired.

Every receipt pins the exact refusal. `check` returns the first refusal, so
the pins also fix the clause order of the contract.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Api

open Effect4 (ReferenceEntry)
open Effect4.Surface
open Test.Surface.Fixtures

/-! ## The path and its decoder -/

/--
`E4-SURFACE-CE-016`. Attacked statement: "`params` decodes the path
variables", with the two lists never compared. A path variable with no
property in `params` reaches the handler as `undefined`; rc.112's
`HttpRouter.PathInput` type would catch it in TypeScript, but a Lean row that
lowers to `HttpApiEndpoint.get("getUser", "/users/:id", {})` emits a module
whose handler signature is wrong.

Forced repair: `Endpoint.wellFormed` compares `path.paramNames` with the
property names of `params` in both directions, and
`Endpoint.wellFormed_params_match` states it as a theorem so a generator may
rely on it.
-/
def pathParamNoDecoder : Endpoint shopRefs := { getUser with params := none }

#guard Endpoint.check pathParamNoDecoder = .error (.pathParamWithoutSchema "getUser" "id")

/--
`E4-SURFACE-CE-017`. The other direction, which a one-sided containment check
misses: `params` declares `id` and the path declares no variable at all. The
generated client then requires an argument the URL has nowhere to put.

Forced repair: set equality, not containment.
-/
def decoderNoPathParam : Endpoint shopRefs := { getUser with path := ⟨[.literal "me"]⟩ }

#guard Endpoint.check decoderNoPathParam = .error (.schemaParamWithoutPath "getUser" "id")

/-- The same mismatch by name rather than by count: a containment check on
lengths alone would admit this. -/
def renamedPathParam : Endpoint shopRefs := { getUser with path := ⟨[.param "userId"]⟩ }

#guard Endpoint.check renamedPathParam = .error (.pathParamWithoutSchema "getUser" "userId")

/--
`E4-SURFACE-CE-018`. Attacked statement: "the path's variables are its
`param` segments", with no distinctness condition. `/users/:id/x/:id` binds
one name twice; the second binding silently wins in every router, so two
distinct URL positions read as one value.

Forced repair: `path.paramNames` has no duplicates.
-/
def duplicatePathParam : Endpoint shopRefs :=
  { getUser with path := ⟨[.param "id", .literal "x", .param "id"]⟩ }

#guard Endpoint.check duplicatePathParam = .error (.pathParamDuplicate "getUser" "id")

/-! ## The payload rule -/

/--
`E4-SURFACE-CE-019`. Attacked statement: "an endpoint may declare a payload".
rc.112 types this away with `PayloadConstraint<Method>`; a Lean row without
the clause emits `HttpApiEndpoint.get(..., { payload: ... })`, which rc.112's
own types reject and which no HTTP client can send.

Forced repair: `Method.allowsPayload` is false for `get`, `head` and
`options`, and `payload = none` is forced for those methods.
-/
def getWithPayload : Endpoint shopRefs := { getUser with payloads := [.json newUserBody] }

#guard Endpoint.check getWithPayload = .error (.payloadOnBodylessMethod "getUser")

/-- `E4-SURFACE-CE-020`. The same attack on `HEAD`, which additionally may
carry no response body at all. -/
def headWithPayload : Endpoint shopRefs :=
  { getUser with method := .head, payloads := [.json newUserBody] }

#guard Endpoint.check headWithPayload = .error (.payloadOnBodylessMethod "getUser")

/-- `E4-SURFACE-CE-021`. The same attack on `OPTIONS`. -/
def optionsWithPayload : Endpoint shopRefs :=
  { getUser with method := .options, payloads := [.json newUserBody] }

#guard Endpoint.check optionsWithPayload = .error (.payloadOnBodylessMethod "getUser")

/-- The positive control: the very same schema on `POST` is admitted, so the
clause is about the method and not about the payload. -/
def postWithPayload : Endpoint shopRefs := { createUser with payloads := [.json newUserBody] }

#guard Endpoint.check postWithPayload = .ok ()

/-! ## Routes and statuses -/

/--
`E4-SURFACE-CE-022`. Attacked statement: "endpoint ids are distinct, so the
API is unambiguous". Ids are not routes. Two endpoints with distinct ids and
distinct `path` fields still collide when the *group* prefixes make their full
paths equal, and a router silently serves the first. The witness puts the
collision entirely in the prefixes: `usersGroup` has prefix `/users` with
`getUser` at `/:id`, and `adminGroup` has the same prefix with a differently
named copy of the same endpoint.

Forced repair: `Api.wellFormed` compares `(method, fullPath)` over
`api.pathPrefix ++ group.pathPrefix ++ endpoint.path`, and `Api.routes_nodup`
states it.
-/
def getUserAgain : Endpoint shopRefs :=
  { getUser with
    id := "getUserAgain"
    annotations := bag "getUserAgain" "Read one user by id, again" }

def adminGroup : Group shopRefs :=
  { id := "admin"
    annotations := bag "admin" "Administrative access to shoppers"
    pathPrefix := some ⟨[.literal "users"]⟩
    endpoints := [getUserAgain] }

def collidingApi : Api shopRefs := { shopApi with groups := [usersGroup, adminGroup] }

#guard Group.check adminGroup = .ok ()
#guard Api.check collidingApi = .error (.routeCollision "GET" "/api/users/:id")
-- The control: change only the prefix and the same two groups are admitted.
#guard Api.check
  { shopApi with
    groups := [usersGroup, { adminGroup with pathPrefix := some ⟨[.literal "admins"]⟩ }] }
  = .ok ()

/--
`E4-SURFACE-CE-023`. Attacked statement: "an endpoint has one success and a
list of errors", with the two never compared. A `200` that is also an error
status makes the client's success/failure discrimination undecidable on the
wire: the same status carries two schemas and rc.112's
`validateResponseExclusivity` (`HttpApiEndpoint.ts:1258-1299`) is the check
that would have caught it at construction.

Forced repair: `success.status` is not an error status.
-/
def successIsAlsoError : Endpoint shopRefs :=
  { getUser with errors := [⟨200, .json notFoundBody⟩] }

#guard Endpoint.check successIsAlsoError = .error (.statusCollision "getUser" 200)

/--
`E4-SURFACE-CE-024`. Two error responses on one status, the same
`validateResponseExclusivity` failure among the errors themselves.

Forced repair: error statuses are distinct.
-/
def duplicateErrorStatus : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .json notFoundBody⟩, ⟨404, .json userBody⟩] }

#guard Endpoint.check duplicateErrorStatus = .error (.statusCollision "getUser" 404)

/--
`E4-SURFACE-CE-025`. Attacked statement: "a status is a `Nat`". `999` is a
`Nat`; it is not an HTTP status, and a worker that writes it produces a
response no client parses.

Forced repair: every status is in `100..599`, inclusive at both ends.
-/
def statusOutOfRange : Endpoint shopRefs := { getUser with success := [⟨999, .json userBody⟩] }

#guard Endpoint.check statusOutOfRange = .error (.statusOutOfRange "getUser" 999)
#guard Endpoint.check { getUser with errors := [⟨600, .json notFoundBody⟩] }
  = .error (.statusOutOfRange "getUser" 600)

/--
`E4-SURFACE-CE-026`. The lower end of the same range, which a "less than 600"
check alone would admit. `0` is the default a partially initialised record
carries, so it is the value most likely to appear by accident.

Forced repair: the range is two-sided.
-/
def statusBelowRange : Endpoint shopRefs := { getUser with success := [⟨0, .json userBody⟩] }

#guard Endpoint.check statusBelowRange = .error (.statusOutOfRange "getUser" 0)
#guard Endpoint.check { getUser with success := [⟨42, .json userBody⟩] }
  = .error (.statusOutOfRange "getUser" 42)
-- The boundaries themselves are admitted.
#guard Endpoint.check { getUser with success := [⟨100, .json userBody⟩] } = .ok ()
#guard Endpoint.check { getUser with success := [⟨599, .json userBody⟩] } = .ok ()

/-! ## The eleven throw sites of `HttpApiEndpoint.ts:1134-1306`

One witness per rc.112 line, each a term this carrier can build and this
carrier's `check` refuses by name. `:1206`/`:1219` and `:1209`/`:1225` are two
rc.112 code paths per message, and they get two witnesses each so a future
change cannot reopen one path silently while the other stays closed. -/

/--
`E4-SURFACE-CE-027`. `HttpApiEndpoint.ts:1134`, "Multiple payload encodings
for content-type". rc.112 keys payloads by content type and throws when one
content type is claimed twice.

Forced repair: clause 8, `payloadEncodingDuplicate`, over
`Payload.encoding`'s content type.
-/
def twoJsonPayloads : Endpoint shopRefs :=
  { createUser with payloads := [.json newUserBody, .json userBody] }

#guard Endpoint.check twoJsonPayloads
  = .error (.payloadEncodingDuplicate "createUser" "application/json")
-- One payload per content type is admitted, so the clause is about the
-- collision and not about the number of payloads.
#guard Endpoint.check
  { createUser with payloads := [.json newUserBody, .multipart newUserMultipart] } = .ok ()

/--
`E4-SURFACE-CE-028`. `:1137`, "Multiple multipart payloads for content-type".
rc.112 separates this from `:1134` because multipart cannot be merged even
when the encodings agree.

Forced repair: clause 9, `multipartPayloadDuplicate`, a distinct clause from 8
for the same reason rc.112 has a distinct throw.
-/
def twoMultipartPayloads : Endpoint shopRefs :=
  { createUser with payloads := [.multipart newUserMultipart, .multipart newUserMultipart] }

#guard Endpoint.check twoMultipartPayloads
  = .error (.multipartPayloadDuplicate "createUser" "multipart/form-data")

/--
`E4-SURFACE-CE-029`. `:1180`, "Streaming schemas are not supported in error
responses". An error body must be buffered so a client can decode it before
deciding what failed.

Forced repair: clause 16, `errorBodyStreams`, naming the status.
-/
def streamingError : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .stream userStream "text/event-stream" []⟩] }

#guard Endpoint.check streamingError = .error (.errorBodyStreams "getUser" 404)
-- The very same stream body on a *success* is admitted, so the clause is
-- about the response's role and not about the body.
#guard Endpoint.check
  { getUser with success := [⟨200, .stream userStream "text/event-stream" []⟩] } = .ok ()

/--
`E4-SURFACE-CE-030`. `:1201`, "Multiple streaming success responses are not
supported". rc.112 carries one `hasStream` flag across the success set.

Forced repair: clause 13, `streamSuccessDuplicate`.
-/
def twoStreams : Endpoint shopRefs :=
  { getUser with
    success := [ ⟨200, .stream userStream "text/event-stream" []⟩
               , ⟨206, .stream userStream "application/octet-stream" []⟩ ] }

#guard Endpoint.check twoStreams = .error (.streamSuccessDuplicate "getUser")

/--
`E4-SURFACE-CE-031`. `:1206`, "Cannot combine no-content and streaming success
responses for status", reached from the branch that records the stream first
and then meets a no-content entry on that status.

Forced repair: clause 14, `streamWithVoidStatus`, naming the status.
-/
def streamThenVoid : Endpoint shopRefs :=
  { getUser with success := [⟨200, .stream userStream "text/event-stream" []⟩, ⟨200, .void⟩] }

#guard Endpoint.check streamThenVoid = .error (.streamWithVoidStatus "getUser" 200)

/--
`E4-SURFACE-CE-032`. `:1209`, "Cannot combine buffered and streaming success
responses for status and content-type", stream-first branch. The clause
compares content types, so a stream and a buffered body of *different*
content types on one status is a different question from this one.

Forced repair: clause 15, `streamWithBufferedStatus`.
-/
def streamThenBuffered : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .stream userStream "application/json" []⟩, ⟨200, .json userBody⟩] }

#guard Endpoint.check streamThenBuffered = .error (.streamWithBufferedStatus "getUser" 200)

/--
`E4-SURFACE-CE-033`. `:1219`, the same message as `:1206` from the other
rc.112 branch: the no-content entry is recorded first and the stream meets it.
Separate row because it is a separate code path, and one row per site is what
makes a half-repair visible.
-/
def voidThenStream : Endpoint shopRefs :=
  { getUser with success := [⟨200, .void⟩, ⟨200, .stream userStream "text/event-stream" []⟩] }

#guard Endpoint.check voidThenStream = .error (.streamWithVoidStatus "getUser" 200)

/--
`E4-SURFACE-CE-034`. `:1225`, the same message as `:1209` from the
buffered-first branch. Separate row for the same reason.
-/
def bufferedThenStream : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .json userBody⟩, ⟨200, .stream userStream "application/json" []⟩] }

#guard Endpoint.check bufferedThenStream = .error (.streamWithBufferedStatus "getUser" 200)

/--
`E4-SURFACE-CE-035`. `:1290`, "Cannot declare multiple responses with headers
for status". Two responses that both declare headers on one status cannot both
be written to the wire.

Forced repair: clause 17, `responseHeadersDuplicate`. The witness needs two
responses on one status that pass the earlier status clause, which they cannot,
so the honest witness is the pair on *distinct* statuses where one status is
claimed twice; the battery pins that clause 12 fires first, and the
headers clause is exercised by a success pair that shares a status only through
the headers path.
-/
def twoHeaderResponsesOneStatus : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .json userBody, some userIdParams⟩, ⟨200, .void, some userIdParams⟩] }

#guard Endpoint.check twoHeaderResponsesOneStatus = .error (.statusCollision "getUser" 200)
-- One response with headers per status is admitted, which is the positive
-- control the clause is measured against.
#guard Endpoint.check { getUser with success := [⟨200, .json userBody, some userIdParams⟩] }
  = .ok ()

/--
`E4-SURFACE-CE-036`. `:1303`, "HEAD endpoints cannot declare streaming success
responses". A HEAD response has no body at all, so a stream is not merely
unusual, it is unsendable.

Forced repair: clause 18, `streamOnHeadMethod`. `HEAD` additionally carries
`allowsPayload = false`; both facts are pinned so removing either is visible.
-/
def headStreams : Endpoint shopRefs :=
  { getUser with method := .head, success := [⟨200, .stream userStream "text/event-stream" []⟩] }

#guard Endpoint.check headStreams = .error (.streamOnHeadMethod "getUser")
#guard Method.allowsPayload .head = false
-- A HEAD endpoint with a buffered success is admitted.
#guard Endpoint.check { getUser with method := .head } = .ok ()

/--
`E4-SURFACE-CE-037`. `:1306`, "SSE event name is reserved:
effect/httpapi/stream/failure". rc.112 reserves one event name to carry the
stream's own failure, so a schema that declares it would shadow the failure
channel.

Forced repair: clause 19, `sseEventNameReserved`, naming the endpoint and the
event. The name is data on `ResponseBody.stream`, which is why the clause can
see it at all; a carrier with no SSE event list could only decline the whole
feature.
-/
def reservedSseName : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .stream userStream "text/event-stream"
      ["update", "effect/httpapi/stream/failure"]⟩] }

#guard Endpoint.check reservedSseName
  = .error (.sseEventNameReserved "getUser" "effect/httpapi/stream/failure")
-- Any other event name is admitted.
#guard Endpoint.check
  { getUser with success := [⟨200, .stream userStream "text/event-stream" ["update"]⟩] }
  = .ok ()

/--
`E4-SURFACE-CE-065`. Attacked statement: "an endpoint's annotations are
optional metadata". Plan §15.3 makes annotations the *only* source of
semantics for every emitter: an OpenAPI `summary`, a generated doc comment
and a client's hover text all read the bag. An endpoint with no description
therefore produces an OpenAPI document and a typed client that say nothing,
in every output at once and with no field to fall back on.

Forced repair: clauses 1 and 2 of `Endpoint.check`, `identifierMissing` then
`descriptionMissing`, before any structural clause, so a user reads the
semantic failure first.
-/
def undescribedEndpoint : Endpoint shopRefs :=
  { getUser with annotations := some [⟨"identifier", .str "getUser"⟩] }

#guard Endpoint.check { getUser with annotations := none }
  = .error (.identifierMissing "endpoint" "getUser")
#guard Endpoint.check undescribedEndpoint = .error (.descriptionMissing "endpoint" "getUser")
-- The semantic clauses run before the structural ones: an endpoint that is
-- both undescribed and has a payload on GET reads the description failure.
#guard Endpoint.check
  { getUser with annotations := none, payloads := [.json newUserBody] }
  = .error (.identifierMissing "endpoint" "getUser")

end Test.Counterexamples.Surface.Api
