/-
Contract: `Test/contracts/surface-api.contract.md`.

Frozen by the wave-1b breaker before `src/Effect4/Surface/Api.lean` and
`src/Effect4/Codegen/Target.lean` exist, from
`docs/research/2026-09-04-surface-library-plan.md` §4.4 as revised by §13.1.
Red until the builder lands the modules.

Pin: `effect` 4.0.0-rc.112,
`node_modules/effect/src/unstable/httpapi/HttpApiEndpoint.ts`. All eleven
construction-time throws of `:1134-1306` are representable attacks here, each
refused by a named clause; the witnesses are in
`Test/Counterexamples/Surface/Api.lean`.

Every negative receipt pins the exact refusal, not a Boolean, because `check`
returns the first refusal and the clause order is part of the contract.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Surface.ApiContract

open Effect4 (Representation ReferenceEntry Json)
open Effect4.Surface
open Test.Surface.Fixtures
open Effect4.Schema (struct property string number reference)

/-! ## Paths render exactly -/

#guard Path.render ⟨[]⟩ = "/"
#guard Path.render ⟨[.literal "users"]⟩ = "/users"
#guard Path.render ⟨[.literal "users", .param "id"]⟩ = "/users/:id"
#guard Path.render ⟨[.literal "a", .param "id", .literal "b"]⟩ = "/a/:id/b"
#guard Path.paramNames ⟨[.literal "a", .param "id", .literal "b", .param "rev"]⟩ = ["id", "rev"]
#guard Path.paramNames ⟨[]⟩ = []
#guard Path.append ⟨[.literal "api"]⟩ ⟨[.literal "users", .param "id"]⟩
  = ⟨[.literal "api", .literal "users", .param "id"]⟩

/-! ## The method alphabet and the payload rule -/

#guard Method.name .get = "GET"
#guard Method.name .post = "POST"
#guard Method.name .put = "PUT"
#guard Method.name .patch = "PATCH"
#guard Method.name .delete = "DELETE"
#guard Method.name .head = "HEAD"
#guard Method.name .options = "OPTIONS"
#guard Method.allowsPayload .get = false
#guard Method.allowsPayload .head = false
#guard Method.allowsPayload .options = false
#guard Method.allowsPayload .post = true
#guard Method.allowsPayload .put = true
#guard Method.allowsPayload .patch = true
#guard Method.allowsPayload .delete = true

/-! ## Payload encodings and response bodies -/

#guard PayloadEncoding.contentType .json = "application/json"
#guard PayloadEncoding.contentType .multipart = "multipart/form-data"
#guard PayloadEncoding.contentType .urlEncoded = "application/x-www-form-urlencoded"
#guard Payload.encoding (Payload.json newUserBody) = PayloadEncoding.json
#guard Payload.encoding (Payload.multipart newUserMultipart) = PayloadEncoding.multipart
#guard Payload.encoding (Payload.urlEncoded newUserUrlEncoded) = PayloadEncoding.urlEncoded

#guard ResponseBody.isVoid (ResponseBody.void : ResponseBody shopRefs) = true
#guard ResponseBody.isVoid (ResponseBody.json userBody) = false
#guard ResponseBody.isStream (ResponseBody.stream userStream "text/event-stream" []) = true
#guard ResponseBody.isStream (ResponseBody.json userBody) = false
#guard ResponseBody.contentType (ResponseBody.json userBody) = "application/json"
#guard ResponseBody.contentType (ResponseBody.void : ResponseBody shopRefs) = ""
#guard ResponseBody.contentType (ResponseBody.stream userStream "text/event-stream" [])
  = "text/event-stream"

/-! ## The fixture API is well formed -/

#guard Endpoint.check getUser = .ok ()
#guard Endpoint.check createUser = .ok ()
#guard Endpoint.check deleteUser = .ok ()
#guard Group.check usersGroup = .ok ()
#guard Api.check shopApi = .ok ()

theorem getUser_wf : Endpoint.WellFormed getUser := by decide
theorem createUser_wf : Endpoint.WellFormed createUser := by decide
theorem deleteUser_wf : Endpoint.WellFormed deleteUser := by decide
theorem usersGroup_wf : Group.WellFormed usersGroup := by decide
theorem shopApi_wf : Api.WellFormed shopApi := by decide

/-! ## The route table, prefixes composed -/

#guard Api.fullPath shopApi usersGroup getUser
  = ⟨[.literal "api", .literal "users", .param "id"]⟩
#guard Api.routes shopApi =
  [ (Method.get, "/api/users/:id")
  , (Method.post, "/api/users")
  , (Method.delete, "/api/users/:id") ]
#guard (Api.endpoint? shopApi "users" "getUser").map Endpoint.id = some "getUser"
#guard (Api.endpoint? shopApi "users" "absent").isNone
#guard (Api.endpoint? shopApi "absent" "getUser").isNone
#guard Api.requirements shopApi = ["Db"]

/-! ## The refusals, one named mutant per attack, each pinning its clause -/

-- `E4-SURFACE-CE-065`: the semantic layer is not optional (plan §15.2).
#guard Endpoint.check { getUser with annotations := none }
  = .error (.identifierMissing "endpoint" "getUser")
#guard Endpoint.check { getUser with annotations := some [⟨"identifier", .str "getUser"⟩] }
  = .error (.descriptionMissing "endpoint" "getUser")

-- `E4-SURFACE-CE-016`: a path variable with no decoder.
def pathParamNoDecoder : Endpoint shopRefs := { getUser with params := none }
#guard Endpoint.check pathParamNoDecoder = .error (.pathParamWithoutSchema "getUser" "id")

-- `E4-SURFACE-CE-017`: a decoder for a variable the path does not carry.
def decoderNoPathParam : Endpoint shopRefs := { getUser with path := ⟨[.literal "me"]⟩ }
#guard Endpoint.check decoderNoPathParam = .error (.schemaParamWithoutPath "getUser" "id")

-- The same mismatch by name rather than by count.
def renamedPathParam : Endpoint shopRefs := { getUser with path := ⟨[.param "userId"]⟩ }
#guard Endpoint.check renamedPathParam = .error (.pathParamWithoutSchema "getUser" "userId")

-- `E4-SURFACE-CE-018`: one name bound twice by the path.
def duplicatePathParam : Endpoint shopRefs :=
  { getUser with path := ⟨[.param "id", .literal "x", .param "id"]⟩ }
#guard Endpoint.check duplicatePathParam = .error (.pathParamDuplicate "getUser" "id")

-- `E4-SURFACE-CE-019`, `020`, `021`: a body on a method that has none.
def getWithPayload : Endpoint shopRefs := { getUser with payloads := [.json newUserBody] }
#guard Endpoint.check getWithPayload = .error (.payloadOnBodylessMethod "getUser")

def headWithPayload : Endpoint shopRefs :=
  { getUser with method := .head, payloads := [.json newUserBody] }
#guard Endpoint.check headWithPayload = .error (.payloadOnBodylessMethod "getUser")

def optionsWithPayload : Endpoint shopRefs :=
  { getUser with method := .options, payloads := [.json newUserBody] }
#guard Endpoint.check optionsWithPayload = .error (.payloadOnBodylessMethod "getUser")

-- The control: the same body on POST is admitted, so the clause is about the
-- method and not about the schema.
#guard Endpoint.check { createUser with payloads := [.json newUserBody] } = .ok ()

-- `E4-SURFACE-CE-027`: `HttpApiEndpoint.ts:1134`, two payloads on one content type.
def twoJsonPayloads : Endpoint shopRefs :=
  { createUser with payloads := [.json newUserBody, .json userBody] }
#guard Endpoint.check twoJsonPayloads
  = .error (.payloadEncodingDuplicate "createUser" "application/json")

-- `E4-SURFACE-CE-028`: `:1137`, two multipart payloads.
def twoMultipartPayloads : Endpoint shopRefs :=
  { createUser with payloads := [.multipart newUserMultipart, .multipart newUserMultipart] }
#guard Endpoint.check twoMultipartPayloads
  = .error (.multipartPayloadDuplicate "createUser" "multipart/form-data")

-- The control: one payload per content type is admitted, and the endpoint is
-- well formed even though the v1 emitters refuse multipart by rule id.
#guard Endpoint.check
  { createUser with payloads := [.json newUserBody, .multipart newUserMultipart] } = .ok ()

-- An endpoint with no success at all has no response to describe.
#guard Endpoint.check { getUser with success := [] } = .error (.successEmpty "getUser")

-- `E4-SURFACE-CE-023`: one status cannot mean both success and failure.
def successIsAlsoError : Endpoint shopRefs :=
  { getUser with errors := [⟨200, .json notFoundBody⟩] }
#guard Endpoint.check successIsAlsoError = .error (.statusCollision "getUser" 200)

-- `E4-SURFACE-CE-024`: two error bodies for one status.
def duplicateErrorStatus : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .json notFoundBody⟩, ⟨404, .json userBody⟩] }
#guard Endpoint.check duplicateErrorStatus = .error (.statusCollision "getUser" 404)

-- `E4-SURFACE-CE-025`, `026`: a status outside 100..599.
#guard Endpoint.check { getUser with success := [⟨999, .json userBody⟩] }
  = .error (.statusOutOfRange "getUser" 999)
#guard Endpoint.check { getUser with success := [⟨42, .json userBody⟩] }
  = .error (.statusOutOfRange "getUser" 42)
#guard Endpoint.check { getUser with success := [⟨0, .json userBody⟩] }
  = .error (.statusOutOfRange "getUser" 0)
#guard Endpoint.check { getUser with errors := [⟨600, .json notFoundBody⟩] }
  = .error (.statusOutOfRange "getUser" 600)

-- The boundary is inclusive at both ends.
#guard Endpoint.check { getUser with success := [⟨100, .json userBody⟩] } = .ok ()
#guard Endpoint.check { getUser with success := [⟨599, .json userBody⟩] } = .ok ()

-- rc.112 `HttpApiSchema.Empty(code)` admits any code, so a void success is not
-- restricted to 201/202/204. Pinned so a later tightening is a visible change.
#guard Endpoint.check { deleteUser with success := [⟨200, .void⟩] } = .ok ()

-- `E4-SURFACE-CE-030`: `:1201`, two streaming successes.
def twoStreams : Endpoint shopRefs :=
  { getUser with
    success := [ ⟨200, .stream userStream "text/event-stream" []⟩
               , ⟨206, .stream userStream "application/octet-stream" []⟩ ] }
#guard Endpoint.check twoStreams = .error (.streamSuccessDuplicate "getUser")

-- `E4-SURFACE-CE-031`, `033`: `:1206` and `:1219`, a void body and a stream on
-- one status, reached from either side.
def streamThenVoid : Endpoint shopRefs :=
  { getUser with success := [⟨200, .stream userStream "text/event-stream" []⟩, ⟨200, .void⟩] }
def voidThenStream : Endpoint shopRefs :=
  { getUser with success := [⟨200, .void⟩, ⟨200, .stream userStream "text/event-stream" []⟩] }
#guard Endpoint.check streamThenVoid = .error (.streamWithVoidStatus "getUser" 200)
#guard Endpoint.check voidThenStream = .error (.streamWithVoidStatus "getUser" 200)

-- `E4-SURFACE-CE-032`, `034`: `:1209` and `:1225`, a buffered body and a
-- stream of one content type on one status.
def streamThenBuffered : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .stream userStream "application/json" []⟩, ⟨200, .json userBody⟩] }
def bufferedThenStream : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .json userBody⟩, ⟨200, .stream userStream "application/json" []⟩] }
#guard Endpoint.check streamThenBuffered = .error (.streamWithBufferedStatus "getUser" 200)
#guard Endpoint.check bufferedThenStream = .error (.streamWithBufferedStatus "getUser" 200)

-- `E4-SURFACE-CE-029`: `:1180`, an error body that streams.
def streamingError : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .stream userStream "text/event-stream" []⟩] }
#guard Endpoint.check streamingError = .error (.errorBodyStreams "getUser" 404)

-- `E4-SURFACE-CE-035`: `:1290`, two responses with headers on one status.
def twoHeaderResponses : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .json userBody, some userIdParams⟩]
  , errors := [⟨200, .json notFoundBody, some userIdParams⟩] }
#guard Endpoint.check twoHeaderResponses = .error (.statusCollision "getUser" 200)
-- With distinct statuses the headers clause is the one that fires.
def twoHeaderResponsesDistinctStatus : Endpoint shopRefs :=
  { getUser with
    success := [⟨200, .json userBody, some userIdParams⟩, ⟨201, .void, some userIdParams⟩]
  , errors := [⟨201, .json notFoundBody, some userIdParams⟩] }
#guard Endpoint.check twoHeaderResponsesDistinctStatus = .error (.statusCollision "getUser" 201)
-- One response with headers per status is admitted.
#guard Endpoint.check { getUser with success := [⟨200, .json userBody, some userIdParams⟩] }
  = .ok ()

-- `E4-SURFACE-CE-036`: `:1303`, a HEAD endpoint that streams.
def headStreams : Endpoint shopRefs :=
  { getUser with method := .head, success := [⟨200, .stream userStream "text/event-stream" []⟩] }
#guard Endpoint.check headStreams = .error (.streamOnHeadMethod "getUser")
-- A HEAD endpoint with a buffered success is admitted.
#guard Endpoint.check { getUser with method := .head } = .ok ()

-- `E4-SURFACE-CE-037`: `:1306`, the reserved SSE event name.
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

-- `E4-SURFACE-CE-022`: two endpoints on one `(method, full path)`, and the
-- collision is created by the group prefixes, not by the endpoint paths.
def getUserAgain : Endpoint shopRefs :=
  { getUser with
    id := "getUserAgain"
    annotations := bag "getUserAgain" "Read one user by id, again" }

def adminGroup : Group shopRefs :=
  { id := "admin"
  , annotations := bag "admin" "Administrative access to shoppers"
  , pathPrefix := some ⟨[.literal "users"]⟩
  , endpoints := [getUserAgain] }
def collidingApi : Api shopRefs := { shopApi with groups := [usersGroup, adminGroup] }
#guard Group.check adminGroup = .ok ()
#guard Api.check collidingApi = .error (.routeCollision "GET" "/api/users/:id")

-- The control: a different prefix removes the collision.
def distinctGroup : Group shopRefs := { adminGroup with pathPrefix := some ⟨[.literal "admins"]⟩ }
#guard Api.check { shopApi with groups := [usersGroup, distinctGroup] } = .ok ()

-- Two groups of one id.
#guard Api.check { shopApi with groups := [usersGroup, usersGroup] }
  = .error (.groupIdDuplicate "Shop" "users")

-- Two endpoints of one id inside a group.
#guard Group.check { usersGroup with endpoints := [getUser, getUser] }
  = .error (.endpointIdDuplicate "users" "getUser")

/-! ## The slot types

The refusals above are only as strong as the shapes they range over. These
definitions are ascribed to the frozen slot types, so a builder who widened or
narrowed a slot breaks this file rather than silently changing what the clauses
can see. -/

def payloadSlot : ∀ refs : List ReferenceEntry, Endpoint refs → List (Payload refs) :=
  @Endpoint.payloads
def successSlot : ∀ refs : List ReferenceEntry, Endpoint refs → List (Response refs) :=
  @Endpoint.success
def errorSlot : ∀ refs : List ReferenceEntry, Endpoint refs → List (Response refs) :=
  @Endpoint.errors
def responseBodySlot : ∀ refs : List ReferenceEntry, Response refs → ResponseBody refs :=
  @Response.body
def responseHeaderSlot :
    ∀ refs : List ReferenceEntry, Response refs → Option (Sch refs .text) :=
  @Response.headers
def paramsSlot : ∀ refs : List ReferenceEntry, Endpoint refs → Option (Sch refs .text) :=
  @Endpoint.params

#guard (payloadSlot shopRefs createUser).length = 1
#guard (successSlot shopRefs getUser).length = 1
#guard (errorSlot shopRefs getUser).length = 1
#guard (responseHeaderSlot shopRefs (Endpoint.success getUser).head!).isNone

/-! ## The laws -/

theorem getUser_params_match :
    getUser.path.paramNames = (getUser.params.map Sch.propertyNames).getD [] :=
  Endpoint.wellFormed_params_match getUser getUser_wf

theorem shopApi_routes_nodup : (Api.routes shopApi).Nodup :=
  Api.routes_nodup shopApi shopApi_wf

theorem getUser_clauses :
    Endpoint.Described getUser ∧ Endpoint.ParamsMatchPath getUser ∧
      Endpoint.BodylessHasNoPayload getUser ∧ Endpoint.StatusesDistinct getUser ∧
      Endpoint.ResponsesWellShaped getUser :=
  (Endpoint.wellFormed_iff getUser).mp getUser_wf

/-! ## The emitters, `isSome` only: their bytes are the harness's business -/

#guard (httpApiModule shopApi shop).isSome
#guard (clientModule shopApi).isSome
#guard (openApi shopApi shop).isSome

end Test.Surface.ApiContract
