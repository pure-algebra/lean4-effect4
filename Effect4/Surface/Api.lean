import Effect4.Surface.Entity

/-!
# Surface.Api: methods, paths, endpoints, groups and apis

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.4 as revised by
§13.1 and ruled by §13.7.

An **endpoint** is a first-order row: an id, a method, a path, the three text
slots rc.112 decodes from the request line, at most one payload, a list of
success responses and a list of error responses indexed by status, the security
schemes it demands, the service names its handler will need, and its annotation
bag. A **group** is a prefixed list of endpoints; an **api** is a prefixed list
of groups. Well-formedness follows `Effect4/Surface/Facts.lean`: `check` is a
list of named clauses read left to right and answers the *first* refusal,
`WellFormed` is `check = .ok ()`, and `wellFormed_iff` proves it equal to the
conjunction of its clauses.

Every clause is named after the rc.112 line it retires, so a construction-time
throw of `HttpApiEndpoint.ts` becomes a refusal a user reads before any bytes
exist.

| clause | refusal | rc.112 |
| --- | --- | --- |
| `idLegal` | `nameIllegal` | `HttpApiEndpoint.ts:979` (`Identifier extends string`) |
| `identified` | `identifierMissing` | plan §15.2 |
| `described` | `descriptionMissing` | plan §15.2 |
| `pathParamsDistinct` | `pathParamDuplicate` | `unstable/http/HttpRouter.ts:701` (`PathInput`) |
| `pathParamsHaveSchema` | `pathParamWithoutSchema` | `HttpApiEndpoint.ts:1103` (`ensureStruct`), `OpenApi.ts:598` (`processParameters(endpoint.params, "path")`) |
| `schemaParamsInPath` | `schemaParamWithoutPath` | the same pair, read the other way |
| `bodylessHasNoPayload` | `payloadOnBodylessMethod` | `unstable/http/HttpMethod.ts:33` (`NoBody`), `HttpApiEndpoint.ts:1046` (`PayloadConstraintCodecs<Method>`) |
| `successNonEmpty` | `successEmpty` | `HttpApiEndpoint.ts:1009` (`Success = HttpApiSchema.NoContent` default) |
| `statusesInRange` | `statusOutOfRange` | `HttpApiSchema.ts:100` (`status`), `unstable/http/HttpStatus.ts` |
| `successStatusesDistinct` | `statusCollision` | `HttpApiEndpoint.ts:1252` (`validateResponseExclusivity`) |
| `errorStatusesDistinct` | `statusCollision` | `HttpApiEndpoint.ts:1252` |
| `statusesDisjoint` | `statusCollision` | `HttpApiEndpoint.ts:1252` |
| `noStreamInErrors` | `streamInError` | `HttpApiEndpoint.ts:1180` |
| `atMostOneStreamSuccess` | `multipleStreamSuccess` | `HttpApiEndpoint.ts:1201` |
| `noVoidAndStream` | `voidAndStreamAtStatus` | `HttpApiEndpoint.ts:1206`, `:1219` |
| `noBufferedAndStream` | `streamWithBufferedStatus` | `HttpApiEndpoint.ts:1209`, `:1225` |
| `headNeverStreams` | `streamOnHead` | `HttpApiEndpoint.ts:1303` |
| `sseEventNamesFree` | `sseEventNameReserved` | `HttpApiEndpoint.ts:1146`, `:1306` |
| `atMostOneHeadersPerStatus` | `multipleHeadersAtStatus` | `HttpApiEndpoint.ts:1290` |
| `requirementsLegal` | `requirementNameIllegal` | plan §4.4 (the estate's own row; no rc.112 site) |
| `Group.endpointIdsDistinct` | `endpointIdDuplicate` | `HttpApiGroup.ts:318` (`Record.map` over `endpoints`) |
| `Api.groupIdsDistinct` | `groupIdDuplicate` | `HttpApi.ts:172` (`Record.map` over `groups`) |
| `Api.routesDistinct` | `routeCollision` | `OpenApi.ts:629` (`Duplicate OpenAPI operation`) |

| | |
| --- | --- |
| Carrier | `Method` (7), `Segment` (2), `Path`, `ApiKeyLocation` (3), `Security` (3), `ResponseBody refs` (3), `Response refs` (4 fields), `Payload refs` (3), `Endpoint refs` (12 fields), `Group refs` (5 fields), `Api refs` (4 fields) |
| Operations | `Path.render`, `Path.parse?`, the three `check`s, `Endpoint.fullPath`, `Api.endpointTable`, `Api.requirements`, `Api.requirementNames`, `Endpoint.successEntities`, `Endpoint.errorEntities`, `Api.json` |
| Laws | `Path.parse?_render`, `Endpoint.wellFormed_iff`, `Group.wellFormed_iff`, `Api.wellFormed_iff`, `Group.checkEndpoints_ok_iff`, `Api.checkGroups_ok_iff`, `Api.wellFormed_endpoint` |
| Structure | a three-level finite tree whose only cross-level law is route distinctness, decided on the rendered `(method, fullPath)` pair |
| Payoff | retires the construction-time throws of `HttpApiEndpoint.ts:1134-1310` as a class, and gives the client, server and OpenAPI emitters one row set to read |
| Anti-vacuity | the `shopApi` fixture: `decide` receipts for `WellFormed`, an `Arch.accepts` receipt for the view, and one refused mutant per clause |
| Generation | none here; `Effect4/Surface/Api/Emit.lean` owns the three rules |

## Rulings applied (plan §13.7, coordinator, 2026-09-04)

* `Kind` is **not** extended. Multipart, url-encoded and stream are carried by
  the slot constructors: `Payload | json (Sch .json) | multipart (Sch .struct)
  | urlEncoded (Sch .text)` and `ResponseBody | void | json (Sch .json) |
  stream (Sch .json) (sseEventNames)`. The representation has no node for those
  encodings, so a kind would have been a marker with no decision procedure.
* The field is `pathPrefix`, never `prefix`: `prefix` is a reserved token.
* One payload per endpoint in v1. rc.112's per-content-type payload map
  (`HttpApiEndpoint.ts:1111-1144`) is a v2 row, and its two duplicate-encoding
  throws (`:1136`, `:1139`) are unrepresentable here rather than checked.

## What this module deliberately does not model

* **Middleware.** rc.112 attaches security through `HttpApiMiddleware.Security`
  subclasses (`HttpApiEndpoint.ts:213`), not through a field on the endpoint.
  `Endpoint.security` is the estate's own row: it is read by the OpenAPI
  emitter, which is where rc.112 also reads it, and the `HttpApi` module
  emitter refuses an endpoint that carries one rather than inventing a
  middleware class.
* **Response content types.** Every non-void body here is `application/json`;
  `HttpApiSchema.asText`/`asUint8Array` are a later row, and the two clauses
  that would need them (`validateResponseExclusivity`'s content-type keys) are
  decided on the status alone.
* **`topLevel`'s effect on the client.** `Group.topLevel` is stored because
  rc.112 reads it (`HttpApiGroup.ts:394`, `HttpApiClient.ts:527`) and the
  emitters do; no clause here depends on it.

## The identifier profile, said out loud

`Segment.spelled` asks a `param` name for **both** `Spell.identifier` (the
byte-level generated-binding profile) and "no `/` among its characters". The
second is implied by the first, because `/` is byte 47 and no identifier byte
is 47, but the implication relates `String.toUTF8` to `String.toList` and is
not proved here. It is the same owed row `Effect4/Surface/Spell.lean`'s header
already carries for `TypeScript.targetIdentifier`, and `Path.parse?_render`
consumes the char-level half directly rather than resting on it.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema Effect4.Store
open Effect4.Arch (accepts)

/-! ## Comparing kinded schemas

`Effect4/Surface/Kind.lean` gives `Sch` no `DecidableEq`, because its second
field is a proof and the carrier that is stored and addressed is `rep`. The
carriers below are ordinary rows that happen to hold a `Sch`, and the estate
asks every carrier for a `DecidableEq`, so the instance is supplied here: two
kinded schemas are equal exactly when their representations are, and the proof
fields are equal by proof irrelevance. This adds no data to `Sch` and is
declared here rather than in `Kind.lean` so wave 1a's module is untouched.
-/

instance decidableEqSch {refs : List ReferenceEntry} {k : Kind} :
    DecidableEq (Sch refs k) := fun first second =>
  if h : first.rep = second.rep then
    isTrue (by cases first; cases second; cases h; rfl)
  else
    isFalse (by intro equal; exact h (equal ▸ rfl))

/-! ## Methods -/

/--
The HTTP methods a surface endpoint may declare.

Seven, not rc.112's eight: `TRACE` is in `HttpMethod`
(`unstable/http/HttpMethod.ts:18`) but `HttpApiEndpoint` exports no constructor
for it (`HttpApiEndpoint.ts:1397-1449` list `get`, `post`, `put`, `patch`,
`del as delete`, `head`, `options`), so an endpoint that declared it could not
be emitted. The departure is recorded here rather than smoothed over.
-/
inductive Method where
  /-- `GET`; carries no payload. -/
  | get
  /-- `POST`. -/
  | post
  /-- `PUT`. -/
  | put
  /-- `PATCH`. -/
  | patch
  /-- `DELETE`. -/
  | delete
  /-- `HEAD`; carries no payload and never streams. -/
  | head
  /-- `OPTIONS`; carries no payload. -/
  | options
deriving DecidableEq, Repr, Inhabited

namespace Method

/-- The uppercase token of `unstable/http/HttpMethod.ts:18`. -/
def spelling : Method → String
  | .get => "GET"
  | .post => "POST"
  | .put => "PUT"
  | .patch => "PATCH"
  | .delete => "DELETE"
  | .head => "HEAD"
  | .options => "OPTIONS"

/-- The `HttpApiEndpoint` constructor name, which is also the OpenAPI operation
key (`OpenApi.ts:393`: `endpoint.method.toLowerCase()`). -/
def lower : Method → String
  | .get => "get"
  | .post => "post"
  | .put => "put"
  | .patch => "patch"
  | .delete => "delete"
  | .head => "head"
  | .options => "options"

/-- The methods rc.112 treats as carrying no request body
(`unstable/http/HttpMethod.ts:33`, `NoBody`, minus the unmodelled `TRACE`). -/
def bodyless : Method → Bool
  | .get => true
  | .head => true
  | .options => true
  | _ => false

/-- The closed method alphabet. -/
def census : List Method := [.get, .post, .put, .patch, .delete, .head, .options]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 7 := by decide

/-- The census repeats no method. -/
theorem census_nodup : census.Nodup := by decide

/-- The census covers the alphabet. -/
theorem mem_census (method : Method) : method ∈ census := by
  cases method <;> decide

/-- Recognise a method's uppercase token; nothing else is a method. -/
def ofSpelling? : String → Option Method
  | "GET" => some .get
  | "POST" => some .post
  | "PUT" => some .put
  | "PATCH" => some .patch
  | "DELETE" => some .delete
  | "HEAD" => some .head
  | "OPTIONS" => some .options
  | _ => none

/-- Every token is recognised, and recognised as its own method. -/
theorem ofSpelling?_spelling (method : Method) : ofSpelling? method.spelling = some method := by
  cases method <;> decide

/-- Tokens are distinct. Derived from `ofSpelling?_spelling`, not from a `simp`
over string disequalities, which reaches `Classical.choice` on this toolchain. -/
theorem spelling_injective {first second : Method} (h : first.spelling = second.spelling) :
    first = second := by
  have recovered := ofSpelling?_spelling first
  rw [h, ofSpelling?_spelling second] at recovered
  exact (Option.some.inj recovered).symm

/-- Exactly three methods are bodyless. -/
theorem bodyless_census : census.filter bodyless = [.get, .head, .options] := by decide

end Method

/-! ## Paths

A path is a list of segments; a `param` segment is the `:name` spelling
`unstable/http/HttpRouter.ts:701` calls `PathInput`. `render` and `parse?` are
inverse on the *spelled* fragment (`Path.parse?_render`), which is the fragment
every emitter below writes and every ingest of a later wave reads.

The walk is over characters, not bytes: `splitSlash` and `segmentOf?` are the
only two functions that see the wire form, and the round trip is a list
induction over them rather than a claim about `String`.
-/

/-- One path segment: a literal, or a `:name` parameter. -/
inductive Segment where
  /-- A literal segment, spelled verbatim. -/
  | literal (text : String)
  /-- A parameter segment, spelled `:name`. -/
  | param (name : String)
deriving DecidableEq, Repr, Inhabited

namespace Segment

/-- The segment's characters, without its leading separator. -/
def chars : Segment → List Char
  | .literal text => text.toList
  | .param name => ':' :: name.toList

/-- The segment's spelling as text. -/
def spelling (segment : Segment) : String := String.ofList segment.chars

/--
The segment is in the fragment `render` and `parse?` invert on.

A literal is non-empty, does not begin with `:` (which would re-read as a
parameter), is not the router wildcard `*`, and holds no `/`. A parameter's
name is a legal generated binding and holds no `/`; the second conjunct is
implied by the first and is asked for anyway, for the reason in this module's
header.
-/
def spelled : Segment → Bool
  | .literal text =>
    !text.toList.isEmpty && !(text.toList.head? == some ':') && !(text == "*") &&
      text.toList.all (fun character => character != '/')
  | .param name => identifier name && name.toList.all (fun character => character != '/')

/-- The parameter name of a segment, when it is one. -/
def paramName? : Segment → Option String
  | .literal _ => none
  | .param name => some name

end Segment

/-- A path: the segments between its separators. The empty list renders `"/"`. -/
structure Path where
  /-- The segments, in order. -/
  segments : List Segment := []
deriving DecidableEq, Repr, Inhabited

/-- The characters of a non-empty segment list: one `/` before each segment. -/
def bodyChars : List Segment → List Char
  | [] => []
  | segment :: rest => '/' :: (segment.chars ++ bodyChars rest)

namespace Path

/-- The path's characters. The empty path is `"/"`, not `""`. -/
def chars (path : Path) : List Char :=
  match path.segments with
  | [] => ['/']
  | segments => bodyChars segments

/-- The path as text: `"/"`, or `"/a/:id/b"`. -/
def render (path : Path) : String := String.ofList path.chars

/-- Every segment is in the invertible fragment. -/
def spelled (path : Path) : Bool := path.segments.all Segment.spelled

/-- The parameter names of the path, in order. -/
def paramNames (path : Path) : List String := path.segments.filterMap Segment.paramName?

/-- Append two paths' segments. -/
def append (first second : Path) : Path := ⟨first.segments ++ second.segments⟩

/-- An optional prefix, appended when it is there. -/
def prefixWith (outer : Option Path) (inner : Path) : Path :=
  match outer with
  | none => inner
  | some path => path.append inner

end Path

/-- Split a character list on `/`: the characters before the first separator,
then one piece per separator. -/
def splitSlash : List Char → List Char × List (List Char)
  | [] => ([], [])
  | character :: rest =>
    let tail := splitSlash rest
    if character == '/' then ([], tail.1 :: tail.2) else (character :: tail.1, tail.2)

/-- Read one piece back as a segment, or refuse it. -/
def segmentOf? : List Char → Option Segment
  | [] => none
  | first :: rest =>
    if first == ':' then
      let text := String.ofList rest
      if identifier text && rest.all (fun character => character != '/') then
        some (.param text)
      else none
    else
      let text := String.ofList (first :: rest)
      if !(text == "*") && (first :: rest).all (fun character => character != '/') then
        some (.literal text)
      else none

/-- Read every piece back, refusing as soon as one refuses. -/
def segmentsOf? : List (List Char) → Option (List Segment)
  | [] => some []
  | piece :: rest =>
    match segmentOf? piece, segmentsOf? rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/-- Read a `/`-prefixed template back as a path, or refuse it. -/
def parseChars : List Char → Option Path
  | [] => none
  | first :: rest =>
    if first == '/' then
      if rest.isEmpty then some ⟨[]⟩
      else
        match segmentsOf? ((splitSlash rest).1 :: (splitSlash rest).2) with
        | some segments => some ⟨segments⟩
        | none => none
    else none

/-- Read a path template. Refuses anything that does not begin with `/`, an
empty segment, the router wildcard `*`, and a parameter name that is not a
legal generated binding. -/
def Path.parse? (text : String) : Option Path := parseChars text.toList

/-! ### The round trip on the spelled fragment -/

/-- A spelled segment's characters hold no separator. -/
theorem Segment.chars_noSlash (segment : Segment) (h : segment.spelled = true) :
    segment.chars.all (fun character => character != '/') = true := by
  cases segment with
  | literal text =>
    simp only [Segment.spelled, Bool.and_eq_true] at h
    exact h.2
  | param name =>
    simp only [Segment.spelled, Bool.and_eq_true] at h
    simpa [Segment.chars] using h.2

/-- A spelled segment's characters are non-empty. -/
theorem Segment.chars_ne_nil (segment : Segment) (h : segment.spelled = true) :
    segment.chars ≠ [] := by
  cases segment with
  | literal text =>
    simp only [Segment.spelled, Bool.and_eq_true] at h
    intro empty
    have := h.1.1.1
    simp [Segment.chars] at empty
    simp [empty] at this
  | param name => simp [Segment.chars]

/-- Splitting a separator-free prefix leaves the rest of the split alone. -/
theorem splitSlash_append (piece : List Char)
    (h : piece.all (fun character => character != '/') = true) (rest : List Char) :
    splitSlash (piece ++ rest) = (piece ++ (splitSlash rest).1, (splitSlash rest).2) := by
  induction piece with
  | nil => simp
  | cons character tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have notSlash : (character == '/') = false := by simpa using h.1
    simp [splitSlash, notSlash, ih h.2]

/-- The pieces of a segment list's characters are the segments' characters. -/
theorem splitSlash_bodyChars :
    ∀ segments : List Segment, segments.all Segment.spelled = true →
      splitSlash (bodyChars segments) = ([], segments.map Segment.chars)
  | [], _ => by simp [bodyChars, splitSlash]
  | segment :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have inner :=
      splitSlash_append segment.chars (Segment.chars_noSlash segment h.1) (bodyChars rest)
    simp [bodyChars, splitSlash, inner, splitSlash_bodyChars rest h.2]

/-- A spelled segment is read back from its own characters. -/
theorem segmentOf?_chars (segment : Segment) (h : segment.spelled = true) :
    segmentOf? segment.chars = some segment := by
  cases segment with
  | literal text =>
    simp only [Segment.spelled, Bool.and_eq_true] at h
    obtain ⟨⟨⟨nonEmpty, notParam⟩, notStar⟩, noSlash⟩ := h
    cases characters : text.toList with
    | nil => simp [characters] at nonEmpty
    | cons first tail =>
      have notColon : (first == ':') = false := by
        rw [characters] at notParam
        simpa using notParam
      have : String.ofList (first :: tail) = text := by
        rw [← characters, String.ofList_toList]
      simp only [Segment.chars, characters, segmentOf?, notColon, this]
      rw [characters] at noSlash
      simp [notStar, noSlash]
  | param name =>
    simp only [Segment.spelled, Bool.and_eq_true] at h
    simp [Segment.chars, segmentOf?, String.ofList_toList, h.1, h.2]

/-- Every spelled segment list is read back from its pieces. -/
theorem segmentsOf?_map :
    ∀ segments : List Segment, segments.all Segment.spelled = true →
      segmentsOf? (segments.map Segment.chars) = some segments
  | [], _ => rfl
  | segment :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [segmentsOf?, segmentOf?_chars segment h.1, segmentsOf?_map rest h.2]

/--
`parse?` inverts `render` on the spelled fragment.

The fragment is exactly `Path.spelled`: no empty segment, no wildcard, no
segment beginning with `:` that is not a parameter, no `/` inside a segment,
and every parameter name a legal generated binding. Outside it `parse?`
refuses rather than answering a different path, which is what the `#guard`s
below pin.
-/
theorem Path.parse?_render (path : Path) (h : path.spelled = true) :
    Path.parse? path.render = some path := by
  have characters : (Path.render path).toList = path.chars := by
    simp [Path.render, String.toList_ofList]
  cases path with
  | mk segments =>
    cases segments with
    | nil => simp [Path.parse?, characters, Path.chars, parseChars]
    | cons segment rest =>
      simp only [Path.spelled, List.all_cons, Bool.and_eq_true] at h
      have body : Path.chars ⟨segment :: rest⟩ = '/' :: (segment.chars ++ bodyChars rest) := by
        simp [Path.chars, bodyChars]
      have inner :=
        splitSlash_append segment.chars (Segment.chars_noSlash segment h.1) (bodyChars rest)
      have tailSplit :
          splitSlash (bodyChars rest) = ([], rest.map Segment.chars) :=
        splitSlash_bodyChars rest h.2
      have notEmpty : (segment.chars ++ bodyChars rest).isEmpty = false := by
        cases pieces : segment.chars with
        | nil => exact absurd pieces (Segment.chars_ne_nil segment h.1)
        | cons first tail => simp
      simp only [Path.parse?, characters, body, parseChars, beq_self_eq_true, if_true,
        notEmpty, if_false, inner, tailSplit]
      simp [segmentsOf?, segmentOf?_chars segment h.1, segmentsOf?_map rest h.2]

end Effect4.Surface
