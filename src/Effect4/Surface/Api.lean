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
| `successStatusesDistinct` | `statusCollision` | `HttpApiEndpoint.ts:1252-1288` (`validateResponseExclusivity`, keyed by status and content type) |
| `errorStatusesDistinct` | `statusCollision` | `HttpApiEndpoint.ts:1252-1288` |
| `statusesDisjoint` | `statusCollision` | the estate's own row: rc.112 keys successes and errors in two independent maps (`:1247`, `:1180`), and a client cannot decide which decoder a shared status wants |
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
| Laws | `parseChars_bodyChars`, `Path.parse?_render`, `identifier_bytes`, `Endpoint.wellFormed_iff`, `Group.wellFormed_iff`, `Api.wellFormed_iff`, `Group.checkEndpoints_ok_iff`, `Api.checkGroups_ok_iff`, `Api.wellFormed_endpoint` |
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

`segmentOf?` asks a `param` piece for **both** `Spell.identifier` (the
byte-level generated-binding profile) and "no `/` among its characters". The
second is implied by the first, because `/` is byte 47 and no identifier byte
is 47. That implication used to be an owed row here, because it appeared to
relate `String.toUTF8` to `String.toList`; it does not, now that the reader is
`asciiChars?` over bytes, and `identifier_bytes` is the theorem. `Segment.spelled`
therefore asks a `param` name for `identifier` alone.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
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
`unstable/http/HttpRouter.ts:701` calls `PathInput`. `render` is built from
`String.append` and `String.intercalate` alone, so every clause that reads a
rendered route stays inside the estate's axiom budget; `parse?` reads the
template's UTF-8 bytes, and the round trip is a theorem both over characters
and at the `String`.

## The axiom budget, and what it costs this module

On this toolchain `String.toList`, `String.splitOn`, `String.startsWith`,
`String.drop` and `String.length` all reach `Classical.choice`, which this
tree's axiom gate refuses in a declaration. `String.append`,
`String.intercalate`, `String.toUTF8`, `String.ofList` and `String.decEq` do
not. So:

* `Path.render` and `Segment.spelled` use only the clean primitives, and are
  therefore usable inside `Endpoint.check`, `Api.check` and every theorem about
  them;
* `Path.parse?` walks `text.toUTF8.data.toList` through `asciiChars?`, the byte
  route `Effect4/Surface/Spell.lean` and `Effect4/Surface/Site.lean` take, and
  reaches no axiom. It refuses a byte above 127: `Char.ofNat` is exact below
  128 and says nothing above it, and rebuilding a non-ASCII `String` from bytes
  needs a decoder this tree does not have. A route template carrying such a
  byte is refused rather than half-read, and `Segment.spelled` refuses to spell
  one, so `render` and `parse?` still invert on the whole fragment `spelled`
  admits;
* the round trip is proved twice. `parseChars_bodyChars` says that parsing the
  `/`-joined characters of a piece list returns exactly the segments those
  pieces denote, and `Path.parse?_render` carries it to the `String`:
  `path.spelled = true → Path.parse? path.render = some path`. The second was
  an owed row while `parse?` went through `String.toList`, on the grounds that
  the byte and character views of a `String` are not related by anything this
  tree may cite. They are: `String.toByteArray_ofList` and
  `String.toByteArray_inj` relate them, `utf8EncodeChar` is one byte below 128
  by its own definition, and none of those names `String.toList`. What the tree
  may not cite is the *decoding*, and the ASCII refusal is exactly the price of
  not citing it.
-/

/-- One path segment: a literal, or a `:name` parameter. -/
inductive Segment where
  /-- A literal segment, spelled verbatim. -/
  | literal (text : String)
  /-- A parameter segment, spelled `:name`. -/
  | param (name : String)
deriving DecidableEq, Repr, Inhabited

namespace Segment

/-- The segment's spelling in a rendered path. -/
def spelling : Segment → String
  | .literal text => text
  | .param name => ":" ++ name

/--
The segment is in the fragment `render` and `parse?` invert on.

A literal is non-empty, does not begin with `:` (which would re-read as a
parameter), is not the router wildcard `*`, holds no `/`, and is ASCII. A
parameter's name is a legal generated binding, which is ASCII already: every
byte `Effect4/Surface/Spell.lean`'s `identifierStart` and `identifierContinue`
admit is below 128, and `identifier_bytes` is the theorem. Decided over UTF-8
bytes, by the route that module takes: `:` is 58 and `/` is 47.

The ASCII clause is not decoration. `Path.parse?` reads a template over its
bytes and refuses one above 127, because the character view of a `String` is
out of reach of this tree's axiom ceiling above ASCII; a literal segment
carrying such a byte is therefore genuinely *not* in the fragment the two
invert on, and `Path.parse?_render` is the theorem that says the rest of it is.
-/
def spelled : Segment → Bool
  | .literal text =>
    match text.toUTF8.data.toList with
    | [] => false
    | first :: rest =>
      first != 58 && !(text == "*") &&
        (first :: rest).all (fun byte => byte != 47 && byte < 128)
  | .param name => identifier name

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

namespace Path

/-- The path as text: `"/"`, or `"/a/:id/b"`. -/
def render (path : Path) : String :=
  "/" ++ String.intercalate "/" (path.segments.map Segment.spelling)

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

/-! ### Reading a path template back

The walk is over characters, and every function below is total. `segmentOf?`
rebuilds a `String` with `String.ofList`, which is clean; only `Path.parse?`
itself, which turns the caller's `String` into characters, is not.
-/

/-- Split a character list on `/`: the characters before the first separator,
then one piece per separator. -/
def splitSlash : List Char → List Char × List (List Char)
  | [] => ([], [])
  | character :: rest =>
    let tail := splitSlash rest
    if character == '/' then ([], tail.1 :: tail.2) else (character :: tail.1, tail.2)

/-- The characters of a piece list: one `/` before each piece. -/
def bodyChars : List (List Char) → List Char
  | [] => []
  | piece :: rest => '/' :: (piece ++ bodyChars rest)

/-- Read one piece back as a segment, or refuse it.

Both branches ask the piece to hold no separator. For a parameter that is
implied by `identifier` (no identifier byte is 47, which is `identifier_bytes`),
but the clause is asked for outright anyway so that `segmentOf?_noSlash` holds
of every piece this function admits, including one no `identifier` produced. -/
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

/-- Read a `/`-prefixed template's characters back as a path, or refuse them. -/
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

/--
The character an ASCII byte denotes.

`Char.ofNat` agrees with the UTF-8 decoding exactly below 128 and reaches no
axiom; `charOfByte_inj` is the injectivity that makes it a reader rather than a
guess, and `encodeChar_charOfByte` is the encoding half.
-/
def charOfByte (byte : UInt8) : Char := Char.ofNat byte.toNat

/--
Read ASCII bytes back as characters, refusing the first byte that is not ASCII.

With `String.ofList`, which reaches no axiom either, this is the whole route
from a `String`'s content to its characters that stays inside the axiom
ceiling. Above 128 it has nothing to say and refuses, which is what makes
`Path.parse?` an ASCII reader; this module's header says so.
-/
def asciiChars? : List UInt8 → Option (List Char)
  | [] => some []
  | byte :: rest =>
    if byte < 128 then
      match asciiChars? rest with
      | some tail => some (charOfByte byte :: tail)
      | none => none
    else none

/--
Read a path template. Refuses anything that does not begin with `/`, an empty
segment, the router wildcard `*`, a parameter name that is not a legal
generated binding, and any template carrying a byte above 127.

The walk to characters is `text.toUTF8.data.toList` through `asciiChars?`, the
byte route `Effect4/Surface/Spell.lean` and `Effect4/Surface/Site.lean` already
take, because `String.toList` reaches `Classical.choice` on this toolchain.
-/
def Path.parse? (text : String) : Option Path :=
  match asciiChars? text.toUTF8.data.toList with
  | some characters => parseChars characters
  | none => none

/-! ### The round trip, over characters -/

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

/-- Every piece a `segmentOf?` admits holds no separator. -/
theorem segmentOf?_noSlash (piece : List Char) (segment : Segment)
    (h : segmentOf? piece = some segment) :
    piece.all (fun character => character != '/') = true := by
  cases piece with
  | nil => simp [segmentOf?] at h
  | cons first rest =>
    by_cases colon : (first == ':') = true
    · have isColon : first = ':' := by simpa using colon
      simp only [segmentOf?, colon, if_true] at h
      split at h
      · next admitted =>
        have restFree := (Bool.and_eq_true _ _).mp admitted
        simp [isColon, restFree.2]
      · exact absurd h (by simp)
    · simp only [segmentOf?, colon, if_false, Bool.false_eq_true] at h
      split at h
      · next admitted => exact ((Bool.and_eq_true _ _).mp admitted).2
      · exact absurd h (by simp)

/-- The pieces of a piece list's characters are the pieces themselves. -/
theorem splitSlash_bodyChars (pieces : List (List Char))
    (h : pieces.all (fun piece => piece.all (fun character => character != '/')) = true) :
    splitSlash (bodyChars pieces) = ([], pieces) := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have inner := splitSlash_append piece h.1 (bodyChars rest)
    show ([], (splitSlash (piece ++ bodyChars rest)).1 ::
      (splitSlash (piece ++ bodyChars rest)).2) = ([], piece :: rest)
    rw [inner, ih h.2, List.append_nil]

/-- Every piece list a `segmentsOf?` admits holds no separator. -/
theorem segmentsOf?_noSlash :
    ∀ (pieces : List (List Char)) (segments : List Segment),
      segmentsOf? pieces = some segments →
        pieces.all (fun piece => piece.all (fun character => character != '/')) = true
  | [], _, _ => by simp
  | piece :: rest, segments, h => by
    simp only [segmentsOf?] at h
    cases head : segmentOf? piece with
    | none => rw [head] at h; simp at h
    | some segment =>
      cases tail : segmentsOf? rest with
      | none => rw [head, tail] at h; simp at h
      | some tailSegments =>
        simp [segmentOf?_noSlash piece segment head, segmentsOf?_noSlash rest tailSegments tail]

/--
Parsing the `/`-joined characters of a piece list returns exactly the segments
those pieces denote.

This is the invertibility law of the path spelling at the character level:
`parseChars` undoes `bodyChars` on every piece list `segmentsOf?` admits. The
`String`-level corollary is `Path.parse?_render`, below.
-/
theorem parseChars_bodyChars (pieces : List (List Char)) (segments : List Segment)
    (nonEmpty : pieces ≠ []) (read : segmentsOf? pieces = some segments) :
    parseChars (bodyChars pieces) = some ⟨segments⟩ := by
  cases pieces with
  | nil => exact absurd rfl nonEmpty
  | cons piece rest =>
    have free := segmentsOf?_noSlash (piece :: rest) segments read
    simp only [List.all_cons, Bool.and_eq_true] at free
    have pieceFree := free.1
    have restFree := free.2
    have headSome : segmentOf? piece ≠ none := by
      intro absent
      simp only [segmentsOf?, absent] at read
      exact absurd read (by simp)
    have pieceNonEmpty : piece ≠ [] := by
      intro empty
      exact headSome (by rw [empty]; rfl)
    have notEmpty : (piece ++ bodyChars rest).isEmpty = false := by
      cases characters : piece with
      | nil => exact absurd characters pieceNonEmpty
      | cons first tail => rfl
    have inner := splitSlash_append piece pieceFree (bodyChars rest)
    have tailSplit := splitSlash_bodyChars rest restFree
    have splitFst : (splitSlash (piece ++ bodyChars rest)).1 = piece := by
      rw [inner, tailSplit]
      exact List.append_nil piece
    have splitSnd : (splitSlash (piece ++ bodyChars rest)).2 = rest := by
      rw [inner, tailSplit]
    show (if (piece ++ bodyChars rest).isEmpty then some ⟨[]⟩
        else match segmentsOf? ((splitSlash (piece ++ bodyChars rest)).1 ::
            (splitSlash (piece ++ bodyChars rest)).2) with
          | some found => some (⟨found⟩ : Path)
          | none => none) = some ⟨segments⟩
    rw [splitFst, splitSnd, read, notEmpty]
    rfl

/-! ### The round trip, all the way to the `String`

`Path.parse?_render` was an owed row until the byte reader replaced
`String.toList`. What unblocked it is that the byte view of a `String` is no
longer opaque: `String.toByteArray_ofList` says the bytes of `String.ofList` are
`List.utf8Encode`, and `String.toByteArray_inj` says the bytes determine the
`String`. Below 128 `utf8EncodeChar` is a single byte by its own definition, so
`asciiChars?` is a section of the encoding on ASCII and `ofList_charOfByte` is
the retraction. Nothing here names `String.toList`, which is what keeps the
whole section inside the ceiling: a theorem that mentioned it would inherit its
`Classical.choice` and the gate would refuse the theorem.
-/

/-- Below 128 `Char.ofNat` is exact: the character's code point is the byte. -/
theorem val_charOfByte {byte : UInt8} (h : byte.toNat < 128) :
    (charOfByte byte).val.toNat = byte.toNat := by
  rw [charOfByte, Char.ofNat, dif_pos (by unfold Nat.isValidChar; omega)]
  rfl

/-- Distinct ASCII bytes denote distinct characters. -/
theorem charOfByte_inj {a b : UInt8} (ha : a.toNat < 128) (hb : b.toNat < 128)
    (h : charOfByte a = charOfByte b) : a = b := by
  have step := congrArg (fun character => (Char.val character).toNat) h
  simp only [val_charOfByte ha, val_charOfByte hb] at step
  exact UInt8.toNat_inj.mp step

/-- On an all-ASCII byte list the reader is total, and reads byte by byte. -/
theorem asciiChars?_map : ∀ {bs : List UInt8}, bs.all (fun byte => byte < 128) = true →
    asciiChars? bs = some (bs.map charOfByte) := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons byte rest ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [asciiChars?, if_pos h.1, ih h.2, List.map_cons]

/-- An ASCII character encodes back to the one byte it came from. This is
`String.utf8EncodeChar`'s own first branch, taken rather than cited: the core
lemma `String.utf8EncodeChar_eq_singleton` reaches `Classical.choice`. -/
theorem encodeChar_charOfByte {byte : UInt8} (h : byte.toNat < 128) :
    String.utf8EncodeChar (charOfByte byte) = [byte] := by
  unfold charOfByte String.utf8EncodeChar
  simp only [show (Char.ofNat byte.toNat).val.toNat = byte.toNat from val_charOfByte h]
  rw [if_pos (Nat.le_of_lt_succ h), UInt8.ofNat_toNat]

/-- The reader is a section of UTF-8 encoding on ASCII bytes. -/
theorem flatMap_charOfByte : ∀ {bs : List UInt8}, bs.all (fun byte => byte < 128) = true →
    (bs.map charOfByte).flatMap String.utf8EncodeChar = bs := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons byte rest ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hb : byte.toNat < 128 := UInt8.lt_iff_toNat_lt.mp h.1
    rw [List.map_cons, List.flatMap_cons, encodeChar_charOfByte hb, ih h.2,
      List.cons_append, List.nil_append]

/-- A byte array is its data. -/
theorem byteArray_eq_of_data {first second : ByteArray} (h : first.data = second.data) :
    first = second := by
  cases first; cases second; simp_all

/-- The retraction: reading an all-ASCII `String`'s bytes and spelling the
characters back returns the `String` it started from. -/
theorem ofList_charOfByte {text : String}
    (h : (text.toUTF8.data.toList).all (fun byte => byte < 128) = true) :
    String.ofList ((text.toUTF8.data.toList).map charOfByte) = text := by
  rw [← String.toByteArray_inj, String.toByteArray_ofList, List.utf8Encode,
    flatMap_charOfByte h]
  exact byteArray_eq_of_data (by rw [List.data_toByteArray, Array.toArray_toList]; rfl)

/-- Concatenation of `String`s is concatenation of their bytes. -/
theorem utf8_append (first second : String) :
    (first ++ second).toUTF8.data.toList =
      first.toUTF8.data.toList ++ second.toUTF8.data.toList := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.toList_data_append]
  rfl

/-! ### The identifier profile is ASCII, and holds no separator

These three are facts about `Effect4/Surface/Spell.lean`'s byte profile, proved
here because this is the module that consumes them: `Segment.spelled` asks a
`param` name for `identifier` alone, and the round trip needs to know that a
name so admitted carries no `/` and nothing above 127. The header's "identifier
profile, said out loud" used to record the first of those as an owed row; the
byte reader is what made it a statement about bytes on both sides, and so a
theorem.
-/

/-- The ranges `identifierStart` and `identifierContinue` admit are ASCII and
miss 47. Stated over `Nat` because `omega` reaches `Classical.choice` when it
has to case on a `UInt8`. -/
private theorem ascii_of_ranges {n : Nat}
    (h : ((65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)) ∨ n = 95 ∨ n = 36 ∨ (48 ≤ n ∧ n ≤ 57)) :
    n < 128 ∧ n ≠ 47 := ⟨by omega, by omega⟩

/-- An identifier start byte is ASCII and is not `/`. -/
theorem identifierStart_ascii (byte : UInt8) (h : identifierStart byte = true) :
    byte.toNat < 128 ∧ byte.toNat ≠ 47 := by
  unfold identifierStart at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    UInt8.le_iff_toNat_le, show (65 : UInt8).toNat = 65 from rfl,
    show (90 : UInt8).toNat = 90 from rfl, show (97 : UInt8).toNat = 97 from rfl,
    show (122 : UInt8).toNat = 122 from rfl] at h
  refine ascii_of_ranges ?_
  rcases h with ((range | range) | letter) | letter
  · exact Or.inl (Or.inl range)
  · exact Or.inl (Or.inr range)
  · exact Or.inr (Or.inl (by rw [letter]; rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [letter]; rfl)))

/-- An identifier continuation byte is ASCII and is not `/`. -/
theorem identifierContinue_ascii (byte : UInt8) (h : identifierContinue byte = true) :
    byte.toNat < 128 ∧ byte.toNat ≠ 47 := by
  unfold identifierContinue at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le, show (48 : UInt8).toNat = 48 from rfl,
    show (57 : UInt8).toNat = 57 from rfl] at h
  rcases h with start | digit
  · exact identifierStart_ascii byte start
  · exact ascii_of_ranges (Or.inr (Or.inr (Or.inr digit)))

/-- The `Bool` shape of the clause `Segment.spelled` asks a literal for. -/
private theorem byte_ok {byte : UInt8} (h : byte.toNat < 128 ∧ byte.toNat ≠ 47) :
    (byte != 47 && byte < 128) = true := by
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [bne_iff_ne]
    intro eq
    exact h.2 (by rw [eq]; rfl)
  · rw [decide_eq_true_eq, UInt8.lt_iff_toNat_lt]
    exact h.1

/-- Every byte of a legal generated binding is ASCII and is not `/`. This is the
implication this module's header used to owe. -/
theorem identifier_bytes {name : String} (h : identifier name = true) :
    (name.toUTF8.data.toList).all (fun byte => byte != 47 && byte < 128) = true := by
  unfold identifier at h
  split at h
  · exact absurd h (by simp)
  · rename_i first rest heq
    rw [heq, List.all_cons, Bool.and_eq_true]
    simp only [Bool.and_eq_true] at h
    refine ⟨byte_ok (identifierStart_ascii first h.1.1), ?_⟩
    rw [List.all_eq_true] at h ⊢
    intro byte mem
    exact byte_ok (identifierContinue_ascii byte (h.1.2 byte mem))

/-! ### From a spelled path to its characters -/

/-- Byte 58 is `:`. -/
theorem charOfByte_colon : charOfByte 58 = ':' := by decide

/-- Byte 47 is `/`. -/
theorem charOfByte_slash : charOfByte 47 = '/' := by decide

/-- The bytes of `":"`. -/
theorem bytes_colon : (":" : String).toUTF8.data.toList = [58] := by decide

/-- The bytes of `"/"`. -/
theorem bytes_slash : ("/" : String).toUTF8.data.toList = [47] := by decide

/-- An admitted byte list is ASCII. -/
theorem all_lt_of_all_ok {bs : List UInt8}
    (h : bs.all (fun byte => byte != 47 && byte < 128) = true) :
    bs.all (fun byte => byte < 128) = true := by
  rw [List.all_eq_true] at h ⊢
  intro byte mem
  exact (Bool.and_eq_true _ _ |>.mp (h byte mem)).2

/-- No admitted byte denotes `/`. -/
theorem map_charOfByte_noSlash {bs : List UInt8}
    (h : bs.all (fun byte => byte != 47 && byte < 128) = true) :
    (bs.map charOfByte).all (fun character => character != '/') = true := by
  rw [List.all_eq_true] at h ⊢
  intro character mem
  obtain ⟨byte, memByte, rfl⟩ := List.exists_of_mem_map mem
  obtain ⟨notSlash, ascii⟩ := Bool.and_eq_true _ _ |>.mp (h byte memByte)
  rw [bne_iff_ne]
  intro eq
  rw [← charOfByte_slash] at eq
  have bound : byte.toNat < 128 := UInt8.lt_iff_toNat_lt.mp (decide_eq_true_eq.mp ascii)
  exact (bne_iff_ne.mp notSlash) (charOfByte_inj bound (by decide) eq)

/-- The bytes of a segment's spelling. -/
def spellingBytes (segment : Segment) : List UInt8 :=
  segment.spelling.toUTF8.data.toList

/-- The characters of a segment's spelling. -/
def spellingChars (segment : Segment) : List Char := (spellingBytes segment).map charOfByte

/-- A spelled segment spells in ASCII, with no `/`. For a literal that is
`Segment.spelled`'s own clause; for a parameter it is `identifier_bytes` after
the leading `:`. -/
theorem spellingBytes_ok {segment : Segment} (h : segment.spelled = true) :
    (spellingBytes segment).all (fun byte => byte != 47 && byte < 128) = true := by
  cases segment with
  | literal text =>
    simp only [Segment.spelled] at h
    split at h
    · exact absurd h (by simp)
    · rename_i first rest heq
      simp only [Bool.and_eq_true] at h
      show (text.toUTF8.data.toList).all _ = true
      rw [heq]
      exact h.2
  | param name =>
    show ((":" ++ name).toUTF8.data.toList).all _ = true
    rw [utf8_append, bytes_colon, List.cons_append, List.nil_append, List.all_cons,
      Bool.and_eq_true]
    exact ⟨by decide, identifier_bytes h⟩

/-- One spelled segment reads back as itself. -/
theorem segmentOf?_spellingChars {segment : Segment} (h : segment.spelled = true) :
    segmentOf? (spellingChars segment) = some segment := by
  have ok := spellingBytes_ok h
  have noSlash : (spellingChars segment).all (fun character => character != '/') = true :=
    map_charOfByte_noSlash ok
  cases segment with
  | literal text =>
    simp only [Segment.spelled] at h
    split at h
    · exact absurd h (by simp)
    · rename_i first rest heq
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨notColon, notStar⟩, all⟩ := h
      have chars : spellingChars (.literal text) = charOfByte first :: rest.map charOfByte := by
        show (text.toUTF8.data.toList).map charOfByte = _
        rw [heq, List.map_cons]
      have spelledBack : String.ofList (charOfByte first :: rest.map charOfByte) = text := by
        rw [← chars]
        exact ofList_charOfByte (all_lt_of_all_ok ok)
      have head : (first != 47 && first < 128) = true :=
        (List.all_eq_true.mp all) first (by simp)
      have bound : first.toNat < 128 :=
        UInt8.lt_iff_toNat_lt.mp (decide_eq_true_eq.mp (Bool.and_eq_true _ _ |>.mp head).2)
      have notColonChar : (charOfByte first == ':') = false := by
        rw [beq_eq_false_iff_ne]
        intro eq
        rw [← charOfByte_colon] at eq
        exact (bne_iff_ne.mp notColon) (charOfByte_inj bound (by decide) eq)
      rw [chars]
      show (if (charOfByte first == ':') then _ else _) = _
      rw [notColonChar, if_neg (by simp), spelledBack]
      rw [chars] at noSlash
      rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨notStar, noSlash⟩)]
  | param name =>
    have bytes := identifier_bytes h
    have chars : spellingChars (.param name) =
        ':' :: (name.toUTF8.data.toList).map charOfByte := by
      show ((":" ++ name).toUTF8.data.toList).map charOfByte = _
      rw [utf8_append, bytes_colon, List.cons_append, List.nil_append, List.map_cons,
        charOfByte_colon]
    have spelledBack : String.ofList ((name.toUTF8.data.toList).map charOfByte) = name :=
      ofList_charOfByte (all_lt_of_all_ok bytes)
    rw [chars]
    simp only [segmentOf?]
    rw [if_pos (by decide : ((':' : Char) == ':') = true), spelledBack,
      if_pos (by rw [Bool.and_eq_true]; exact ⟨h, map_charOfByte_noSlash bytes⟩)]

/-- Every spelled segment of a list reads back as itself. -/
theorem segmentsOf?_spellingChars : ∀ {segments : List Segment},
    segments.all Segment.spelled = true →
      segmentsOf? (segments.map spellingChars) = some segments := by
  intro segments
  induction segments with
  | nil => intro _; rfl
  | cons segment rest ih =>
    intro h
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons]
    simp only [segmentsOf?, segmentOf?_spellingChars h.1, ih h.2]

/-- The bytes of a rendered path body: one `/` before each segment's spelling. -/
def bodyBytes : List Segment → List UInt8
  | [] => []
  | segment :: rest => 47 :: (spellingBytes segment ++ bodyBytes rest)

/-- A non-empty path renders to exactly those bytes. `String.intercalate` is
peeled by core's own `String.intercalate_cons_cons`; the tail of that peel is
the render of the shorter path, which is what makes the induction close. -/
theorem bytes_render : ∀ {segments : List Segment}, segments ≠ [] →
    (Path.render ⟨segments⟩).toUTF8.data.toList = bodyBytes segments := by
  intro segments
  induction segments with
  | nil => intro absent; exact absurd rfl absent
  | cons segment rest ih =>
    intro _
    cases rest with
    | nil =>
      show ("/" ++ String.intercalate "/" [segment.spelling]).toUTF8.data.toList = _
      rw [show String.intercalate "/" [segment.spelling] = segment.spelling from rfl,
        utf8_append, bytes_slash]
      show 47 :: spellingBytes segment = 47 :: (spellingBytes segment ++ bodyBytes [])
      rw [show bodyBytes [] = [] from rfl, List.append_nil]
    | cons next more =>
      have step : Path.render ⟨segment :: next :: more⟩ =
          "/" ++ (segment.spelling ++ Path.render ⟨next :: more⟩) := by
        show "/" ++ String.intercalate "/"
          (segment.spelling :: next.spelling :: more.map Segment.spelling) = _
        rw [String.intercalate_cons_cons, String.append_assoc]
        rfl
      rw [step, utf8_append, bytes_slash, utf8_append, ih (by simp)]
      rfl

/-- Those bytes are ASCII: the separator is 47 and every spelling is ASCII. -/
theorem bodyBytes_ascii : ∀ {segments : List Segment},
    segments.all Segment.spelled = true →
      (bodyBytes segments).all (fun byte => byte < 128) = true := by
  intro segments
  induction segments with
  | nil => intro _; rfl
  | cons segment rest ih =>
    intro h
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [show bodyBytes (segment :: rest) = 47 :: (spellingBytes segment ++ bodyBytes rest) from rfl,
      List.all_cons, Bool.and_eq_true]
    refine ⟨by decide, ?_⟩
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨all_lt_of_all_ok (spellingBytes_ok h.1), ih h.2⟩

/-- And they denote exactly the characters `parseChars_bodyChars` speaks about. -/
theorem map_bodyBytes : ∀ (segments : List Segment),
    (bodyBytes segments).map charOfByte = bodyChars (segments.map spellingChars) := by
  intro segments
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
    rw [show bodyBytes (segment :: rest) = 47 :: (spellingBytes segment ++ bodyBytes rest) from rfl,
      List.map_cons, List.map_append, ih, charOfByte_slash, List.map_cons]
    rfl

/--
Reading a spelled path's rendering returns the path.

This is the row this module's header owed. `Path.spelled` is exactly the
hypothesis it needs and nothing more: a literal segment that is empty, starts
`:`, is `*`, holds `/`, or carries a byte above 127 is refused by `spelled` and
is genuinely outside the fragment `render` and `parse?` invert on, and a
parameter name that is not a legal generated binding is refused for the same
reason.
-/
theorem Path.parse?_render (path : Path) (spelled : path.spelled = true) :
    Path.parse? path.render = some path := by
  cases path with
  | mk segments =>
    cases segments with
    | nil => rfl
    | cons segment rest =>
      show (match asciiChars? (Path.render ⟨segment :: rest⟩).toUTF8.data.toList with
            | some characters => parseChars characters
            | none => none) = _
      rw [bytes_render (by simp), asciiChars?_map (bodyBytes_ascii spelled), map_bodyBytes]
      exact parseChars_bodyChars ((segment :: rest).map spellingChars) (segment :: rest)
        (by simp) (segmentsOf?_spellingChars spelled)

/-! ## Security

`HttpApiSecurity.ts:126-205`: three constructors, `Http` (whose `bearer` is
`http({ scheme: "Bearer" })`), `ApiKey` and `Basic`. `Http` is narrowed to
`bearer` here because the surface has no row for an arbitrary scheme token and
`OpenApi.ts:918` reads nothing else off it.
-/

/-- Where an api key rides (`HttpApiSecurity.ts:178`). -/
inductive ApiKeyLocation where
  /-- A request header. -/
  | header
  /-- A query parameter. -/
  | query
  /-- A cookie. -/
  | cookie
deriving DecidableEq, Repr, Inhabited

namespace ApiKeyLocation

/-- The spelling OpenAPI's `in` takes. -/
def name : ApiKeyLocation → String
  | .header => "header"
  | .query => "query"
  | .cookie => "cookie"

/-- The closed alphabet. -/
def census : List ApiKeyLocation := [.header, .query, .cookie]

/-- The census covers the alphabet. -/
theorem mem_census (location : ApiKeyLocation) : location ∈ census := by
  cases location <;> decide

/-- Recognise a spelling; nothing else is a location. -/
def ofName? : String → Option ApiKeyLocation
  | "header" => some .header
  | "query" => some .query
  | "cookie" => some .cookie
  | _ => none

/-- Every spelling is recognised, and recognised as its own location. -/
theorem ofName?_name (location : ApiKeyLocation) : ofName? location.name = some location := by
  cases location <;> decide

end ApiKeyLocation

/-- One security scheme an endpoint demands (`HttpApiSecurity.ts:126-205`). -/
inductive Security where
  /-- `Authorization: Bearer …` (`HttpApiSecurity.ts:155`). -/
  | bearer
  /-- An api key in a header, a query parameter or a cookie
  (`HttpApiSecurity.ts:178`). -/
  | apiKey (location : ApiKeyLocation) (name : String)
  /-- `Authorization: Basic …` (`HttpApiSecurity.ts:203`). -/
  | basic
deriving DecidableEq, Repr, Inhabited

namespace Security

/-- The key this scheme takes in `components.securitySchemes`. rc.112 takes it
from the middleware's `security` record key (`OpenApi.ts:541`); the surface has
no middleware row, so the scheme names itself. -/
def schemeName : Security → String
  | .bearer => "bearer"
  | .apiKey _ name => name
  | .basic => "basic"

/-- The OpenAPI scheme object (`OpenApi.ts:904-937`). -/
def json : Security → Json
  | .bearer => .obj [("type", .str "http"), ("scheme", .str "Bearer")]
  | .apiKey location name =>
    .obj [("type", .str "apiKey"), ("name", .str name), ("in", .str location.name)]
  | .basic => .obj [("type", .str "http"), ("scheme", .str "basic")]

end Security

/-! ## Response bodies and payloads

Per the coordinator's ruling of plan §13.7, the encodings are carried by the
slot constructors rather than by new kinds. A `multipart` payload is a struct
(`HttpApiSchema.ts:782`: `asMultipart` brands a schema and annotates it with
`"~httpApiEncoding": { _tag: "Multipart", … }`); a `urlEncoded` payload is a
text struct (`HttpApiSchema.ts:884`: `asFormUrlEncoded`, whose encoded side must
be a record of strings); a `stream` body carries the JSON shape of what is
streamed together with the SSE event names it declares, because rc.112's stream
marker is a property on the schema *object*
(`HttpApiSchema.ts:392`, `:419` `isStreamSchema`) and never reaches the AST.
-/

/-- The body of one response. -/
inductive ResponseBody (refs : List ReferenceEntry) where
  /-- No content: `HttpApiSchema.Empty(<code>)` (`HttpApiSchema.ts:133`). -/
  | void
  /-- A buffered JSON body. -/
  | json (schema : Sch refs .json)
  /-- A streaming body, with the SSE event names it declares
  (`HttpApiSchema.ts:352-418`). An empty list is a `StreamUint8Array`. -/
  | stream (schema : Sch refs .json) (sseEventNames : List String)
deriving DecidableEq

namespace ResponseBody

/-- Whether the body streams. -/
def isStream {refs : List ReferenceEntry} : ResponseBody refs → Bool
  | .stream _ _ => true
  | _ => false

/-- Whether the body is buffered content, that is, neither void nor a stream. -/
def isBuffered {refs : List ReferenceEntry} : ResponseBody refs → Bool
  | .json _ => true
  | _ => false

/-- Whether the body is the no-content marker. -/
def isVoid {refs : List ReferenceEntry} : ResponseBody refs → Bool
  | .void => true
  | _ => false

/-- The SSE event names the body declares; `[]` when it does not stream. -/
def eventNames {refs : List ReferenceEntry} : ResponseBody refs → List String
  | .stream _ names => names
  | _ => []

/-- The body's representation, when it has one. -/
def rep? {refs : List ReferenceEntry} : ResponseBody refs → Option Representation
  | .void => none
  | .json schema => some schema.rep
  | .stream schema _ => some schema.rep

/-- The body's spelling in the view. -/
def kindName {refs : List ReferenceEntry} : ResponseBody refs → String
  | .void => "void"
  | .json _ => "json"
  | .stream _ _ => "stream"

end ResponseBody

/-- One declared response, indexed by its status. -/
structure Response (refs : List ReferenceEntry) where
  /-- The HTTP status (`HttpApiSchema.ts:100`, `status`). -/
  status : Nat
  /-- What the response carries. -/
  body : ResponseBody refs
  /-- The response headers, at most one declaration per status
  (`HttpApiEndpoint.ts:1290`). -/
  headers : Option (Sch refs .text) := none
  /-- The semantic layer: `description` becomes the OpenAPI response
  description (`OpenApi.ts:398`). -/
  annotations : Annotations := none
deriving DecidableEq

/-- The one request payload an endpoint may declare. -/
inductive Payload (refs : List ReferenceEntry) where
  /-- `application/json` (`HttpApiSchema.ts:875`, `asJson`). -/
  | json (schema : Sch refs .json)
  /-- `multipart/form-data` (`HttpApiSchema.ts:782`, `asMultipart`). -/
  | multipart (schema : Sch refs .struct)
  /-- `application/x-www-form-urlencoded` (`HttpApiSchema.ts:884`,
  `asFormUrlEncoded`). -/
  | urlEncoded (schema : Sch refs .text)
deriving DecidableEq

namespace Payload

/-- The payload's content type (`HttpApiSchema.ts:848-860`). -/
def contentType {refs : List ReferenceEntry} : Payload refs → String
  | .json _ => "application/json"
  | .multipart _ => "multipart/form-data"
  | .urlEncoded _ => "application/x-www-form-urlencoded"

/-- The payload's representation. -/
def rep {refs : List ReferenceEntry} : Payload refs → Representation
  | .json schema => schema.rep
  | .multipart schema => schema.rep
  | .urlEncoded schema => schema.rep

/-- The payload's spelling in the view. -/
def kindName {refs : List ReferenceEntry} : Payload refs → String
  | .json _ => "json"
  | .multipart _ => "multipart"
  | .urlEncoded _ => "urlEncoded"

end Payload

/-! ## The three carriers -/

/-- One endpoint: the rows rc.112's `HttpApiEndpoint.make` takes, plus the two
the estate adds (`requires`, `security`). -/
structure Endpoint (refs : List ReferenceEntry) where
  /-- The endpoint's identifier; a legal generated binding. -/
  id : String
  /-- Its method. -/
  method : Method
  /-- Its path, relative to its group's prefix. -/
  path : Path
  /-- The path parameters, whose property names are exactly the path's. -/
  params : Option (Sch refs .text) := none
  /-- The query parameters. -/
  query : Option (Sch refs .text) := none
  /-- The request headers. -/
  headers : Option (Sch refs .text) := none
  /-- The one request payload; never on a bodyless method. -/
  payload : Option (Payload refs) := none
  /-- The success responses, by status. -/
  success : List (Response refs) := []
  /-- The error responses, by status. -/
  errors : List (Response refs) := []
  /-- The security schemes the endpoint demands. -/
  security : List Security := []
  /-- The service names the handler will need, bound by a deployment. -/
  requires : List String := []
  /-- The semantic layer: `identifier` and `description` are required. -/
  annotations : Annotations := none
deriving DecidableEq

/-- One group: a prefixed list of endpoints. -/
structure Group (refs : List ReferenceEntry) where
  /-- The group's identifier; a legal generated binding. -/
  id : String
  /-- The prefix prepended to every endpoint's path
  (`HttpApiGroup.ts:318`). -/
  pathPrefix : Option Path := none
  /-- Its endpoints, in declaration order. -/
  endpoints : List (Endpoint refs) := []
  /-- Whether the generated client exposes the endpoints directly
  (`HttpApiGroup.ts:394`). -/
  topLevel : Bool := false
  /-- The semantic layer. -/
  annotations : Annotations := none
deriving DecidableEq

/-- One api: a prefixed list of groups. -/
structure Api (refs : List ReferenceEntry) where
  /-- The api's identifier; a legal generated binding (`HttpApi.ts:228`). -/
  id : String
  /-- The prefix prepended to every group (`HttpApi.ts:172`). -/
  pathPrefix : Option Path := none
  /-- Its groups, in declaration order. -/
  groups : List (Group refs) := []
  /-- The semantic layer. -/
  annotations : Annotations := none
deriving DecidableEq

/-! ## Reading the semantic layer

§15.3: emitters and clauses read semantics only through the annotation keys of
`Effect4/Surface/Annotate.lean`, never from a second field on a carrier.
-/

/-- The `title` on a bag, when it carries one. -/
def titleIn (annotations : Annotations) : Option String :=
  match annotations with
  | none => none
  | some bag => bagValue? titleKey (some bag)

/-- Build the bag the clauses require: an `identifier` and a `description`.

Fixture-local: `Effect4/Surface/Agent.lean` carries the same construction for its
own battery. One canonical spelling in `Annotate.lean` is owed before wave 3a's
DSL needs it (plan §13.6 rule 2). -/
private def describedBag (identity description : String) : Annotations :=
  descriptionKey.append description (identifierKey.singleton identity)

/-! ## Well-formedness, as named clauses

The clause order is the order a check reads them, and it is the order of the
table in this module's header. A mutant that breaks two clauses answers the
earlier one, which is what the `#guard`s at the end pin.
-/

/-- The reserved SSE event name (`HttpApiEndpoint.ts:1146`,
`reservedStreamFailureEvent`, thrown at `:1306`). -/
def reservedStreamFailureEvent : String := "effect/httpapi/stream/failure"

/-- No status twice. The `List String` twin is `namesUnique`. -/
def statusesUnique : List Nat → Bool
  | [] => true
  | first :: rest => !rest.contains first && statusesUnique rest

/-- The first status that occurs twice, or `0` when there is none. -/
def firstDuplicateStatus : List Nat → Nat
  | [] => 0
  | first :: rest => if rest.contains first then first else firstDuplicateStatus rest

/-- No `(status, body class)` pair twice. rc.112 keys its response exclusivity
map by status *and* normalised content type
(`HttpApiEndpoint.ts:1252-1288`), so two responses may share a status when they
carry different content; the surface's three body classes are its content
alphabet. -/
def statusClassesUnique : List (Nat × String) → Bool
  | [] => true
  | first :: rest => !rest.contains first && statusClassesUnique rest

/-- The status of the first `(status, body class)` pair that occurs twice. -/
def firstDuplicateStatusClass : List (Nat × String) → Nat
  | [] => 0
  | first :: rest => if rest.contains first then first.1 else firstDuplicateStatusClass rest

/-- The first status that does not satisfy a predicate, or `0`. -/
def firstFailingStatus (holds : Nat → Bool) : List Nat → Nat
  | [] => 0
  | first :: rest => if holds first then firstFailingStatus holds rest else first

/-- The property names of an optional text slot, `[]` when it is absent. -/
def slotNames (refs : List ReferenceEntry) (slot : Option (Sch refs .text)) : List String :=
  match slot with
  | none => []
  | some schema => propertyNames ((objectProperties? refs 64 schema.rep).getD [])

namespace Endpoint

variable {refs : List ReferenceEntry}

/-- The parameter names the path declares. -/
def pathParams (endpoint : Endpoint refs) : List String := endpoint.path.paramNames

/-- The property names the `params` schema declares. -/
def paramProperties (endpoint : Endpoint refs) : List String := slotNames refs endpoint.params

/-- Every declared status, successes before errors. -/
def statuses (endpoint : Endpoint refs) : List Nat :=
  (endpoint.success ++ endpoint.errors).map Response.status

/-- The success statuses. -/
def successStatuses (endpoint : Endpoint refs) : List Nat :=
  endpoint.success.map Response.status

/-- The error statuses. -/
def errorStatuses (endpoint : Endpoint refs) : List Nat :=
  endpoint.errors.map Response.status

/-- Every response, successes before errors. -/
def responses (endpoint : Endpoint refs) : List (Response refs) :=
  endpoint.success ++ endpoint.errors

/-- Clause: the endpoint's id is a legal generated binding. -/
def idLegal (endpoint : Endpoint refs) : Bool := identifier endpoint.id

/-- Clause (§15.2): the annotation bag carries an `identifier`. -/
def identified (endpoint : Endpoint refs) : Bool :=
  (identifierIn endpoint.annotations).isSome

/-- Clause (§15.2): the annotation bag carries a `description`. -/
def described (endpoint : Endpoint refs) : Bool :=
  (descriptionIn endpoint.annotations).isSome

/-- Clause: no path parameter name occurs twice. -/
def pathParamsDistinct (endpoint : Endpoint refs) : Bool :=
  namesUnique endpoint.pathParams

/-- Clause: every path parameter is a property of the `params` schema. -/
def pathParamsHaveSchema (endpoint : Endpoint refs) : Bool :=
  endpoint.pathParams.all fun name => endpoint.paramProperties.contains name

/-- Clause: every property of the `params` schema is a path parameter. -/
def schemaParamsInPath (endpoint : Endpoint refs) : Bool :=
  endpoint.paramProperties.all fun name => endpoint.pathParams.contains name

/-- Clause: a bodyless method declares no payload. -/
def bodylessHasNoPayload (endpoint : Endpoint refs) : Bool :=
  !(endpoint.method.bodyless && endpoint.payload.isSome)

/-- Clause: the endpoint declares at least one success response. -/
def successNonEmpty (endpoint : Endpoint refs) : Bool := !endpoint.success.isEmpty

/-- Clause: every status is a real HTTP status. -/
def statusesInRange (endpoint : Endpoint refs) : Bool :=
  endpoint.statuses.all fun status => 100 ≤ status && status ≤ 599

/-- The `(status, body class)` pairs of the success responses. -/
def successClasses (endpoint : Endpoint refs) : List (Nat × String) :=
  endpoint.success.map fun response => (response.status, response.body.kindName)

/-- The `(status, body class)` pairs of the error responses. -/
def errorClasses (endpoint : Endpoint refs) : List (Nat × String) :=
  endpoint.errors.map fun response => (response.status, response.body.kindName)

/-- Clause: no success status carries the same body class twice. -/
def successStatusesDistinct (endpoint : Endpoint refs) : Bool :=
  statusClassesUnique endpoint.successClasses

/-- Clause: no error status carries the same body class twice. -/
def errorStatusesDistinct (endpoint : Endpoint refs) : Bool :=
  statusClassesUnique endpoint.errorClasses

/-- Clause: no status is both a success and an error. -/
def statusesDisjoint (endpoint : Endpoint refs) : Bool :=
  endpoint.successStatuses.all fun status => !endpoint.errorStatuses.contains status

/-- Clause: no error response streams (`HttpApiEndpoint.ts:1180`). -/
def noStreamInErrors (endpoint : Endpoint refs) : Bool :=
  endpoint.errors.all fun response => !response.body.isStream

/-- Clause: at most one success response streams
(`HttpApiEndpoint.ts:1201`). -/
def atMostOneStreamSuccess (endpoint : Endpoint refs) : Bool :=
  (endpoint.success.filter fun response => response.body.isStream).length ≤ 1

/-- The success statuses that carry a body of the given shape. -/
def statusesWith (endpoint : Endpoint refs) (holds : ResponseBody refs → Bool) : List Nat :=
  (endpoint.success.filter fun response => holds response.body).map Response.status

/-- Clause: no status carries both a no-content and a streaming success
(`HttpApiEndpoint.ts:1206`, `:1219`). -/
def noVoidAndStream (endpoint : Endpoint refs) : Bool :=
  (endpoint.statusesWith ResponseBody.isVoid).all fun status =>
    !(endpoint.statusesWith ResponseBody.isStream).contains status

/-- Clause: no status carries both a buffered and a streaming success
(`HttpApiEndpoint.ts:1209`, `:1225`). -/
def noBufferedAndStream (endpoint : Endpoint refs) : Bool :=
  (endpoint.statusesWith ResponseBody.isBuffered).all fun status =>
    !(endpoint.statusesWith ResponseBody.isStream).contains status

/-- Clause: a `HEAD` endpoint never streams (`HttpApiEndpoint.ts:1303`). -/
def headNeverStreams (endpoint : Endpoint refs) : Bool :=
  !(endpoint.method == Method.head &&
    endpoint.success.any fun response => response.body.isStream)

/-- Clause: no SSE event carries the reserved name
(`HttpApiEndpoint.ts:1306`). -/
def sseEventNamesFree (endpoint : Endpoint refs) : Bool :=
  endpoint.success.all fun response =>
    response.body.eventNames.all fun name => !(name == reservedStreamFailureEvent)

/-- The statuses at which more than one response declares headers. -/
def headerStatuses (endpoint : Endpoint refs) : List Nat :=
  (endpoint.responses.filter fun response => response.headers.isSome).map Response.status

/-- Clause: at most one response per status declares headers
(`HttpApiEndpoint.ts:1290`). -/
def atMostOneHeadersPerStatus (endpoint : Endpoint refs) : Bool :=
  statusesUnique endpoint.headerStatuses

/-- Clause: every service name the handler requires is a legal binding. -/
def requirementsLegal (endpoint : Endpoint refs) : Bool :=
  endpoint.requires.all identifier

/-! ### The offending names a refusal carries -/

/-- The first path parameter with no matching schema property. -/
def firstUnschemedParam (endpoint : Endpoint refs) : String :=
  firstFailing (fun name => endpoint.paramProperties.contains name) endpoint.pathParams

/-- The first schema property that is not a path parameter. -/
def firstUnpathedParam (endpoint : Endpoint refs) : String :=
  firstFailing (fun name => endpoint.pathParams.contains name) endpoint.paramProperties

/-- The first status outside `100..599`. -/
def firstBadStatus (endpoint : Endpoint refs) : Nat :=
  firstFailingStatus (fun status => 100 ≤ status && status ≤ 599) endpoint.statuses

/-- The first status declared by both a success and an error. -/
def firstSharedStatus (endpoint : Endpoint refs) : Nat :=
  firstFailingStatus (fun status => !endpoint.errorStatuses.contains status)
    endpoint.successStatuses

/-- The status of the first streaming error response. -/
def firstStreamErrorStatus (endpoint : Endpoint refs) : Nat :=
  match endpoint.errors.find? fun response => response.body.isStream with
  | some response => response.status
  | none => 0

/-- The first status carrying both a no-content and a streaming success. -/
def firstVoidStreamStatus (endpoint : Endpoint refs) : Nat :=
  firstFailingStatus (fun status => !(endpoint.statusesWith ResponseBody.isStream).contains status)
    (endpoint.statusesWith ResponseBody.isVoid)

/-- The first status carrying both a buffered and a streaming success. -/
def firstBufferedStreamStatus (endpoint : Endpoint refs) : Nat :=
  firstFailingStatus (fun status => !(endpoint.statusesWith ResponseBody.isStream).contains status)
    (endpoint.statusesWith ResponseBody.isBuffered)

/-- The first SSE event name that is the reserved one. -/
def firstReservedEvent (endpoint : Endpoint refs) : String :=
  match endpoint.success.find? fun response =>
      response.body.eventNames.contains reservedStreamFailureEvent with
  | some _ => reservedStreamFailureEvent
  | none => ""

/-- The first service name that is not a legal binding. -/
def firstBadRequirement (endpoint : Endpoint refs) : String :=
  firstFailing identifier endpoint.requires

/-- The clauses of an endpoint, in the order a check reads them. -/
def clauses (endpoint : Endpoint refs) : List (Bool × Refusal) :=
  [ (endpoint.idLegal, .nameIllegal "endpoint" endpoint.id)
  , (endpoint.identified, .identifierMissing "endpoint" endpoint.id)
  , (endpoint.described, .descriptionMissing "endpoint" endpoint.id)
  , (endpoint.pathParamsDistinct,
      .pathParamDuplicate endpoint.id (firstDuplicate endpoint.pathParams))
  , (endpoint.pathParamsHaveSchema,
      .pathParamWithoutSchema endpoint.id endpoint.firstUnschemedParam)
  , (endpoint.schemaParamsInPath,
      .schemaParamWithoutPath endpoint.id endpoint.firstUnpathedParam)
  , (endpoint.bodylessHasNoPayload, .payloadOnBodylessMethod endpoint.id)
  , (endpoint.successNonEmpty, .successEmpty endpoint.id)
  , (endpoint.statusesInRange, .statusOutOfRange endpoint.id endpoint.firstBadStatus)
  , (endpoint.successStatusesDistinct,
      .statusCollision endpoint.id (firstDuplicateStatusClass endpoint.successClasses))
  , (endpoint.errorStatusesDistinct,
      .statusCollision endpoint.id (firstDuplicateStatusClass endpoint.errorClasses))
  , (endpoint.statusesDisjoint, .statusCollision endpoint.id endpoint.firstSharedStatus)
  , (endpoint.noStreamInErrors, .streamInError endpoint.id endpoint.firstStreamErrorStatus)
  , (endpoint.atMostOneStreamSuccess, .multipleStreamSuccess endpoint.id)
  , (endpoint.noVoidAndStream, .voidAndStreamAtStatus endpoint.id endpoint.firstVoidStreamStatus)
  , (endpoint.noBufferedAndStream,
      .streamWithBufferedStatus endpoint.id endpoint.firstBufferedStreamStatus)
  , (endpoint.headNeverStreams, .streamOnHead endpoint.id)
  , (endpoint.sseEventNamesFree, .sseEventNameReserved endpoint.id endpoint.firstReservedEvent)
  , (endpoint.atMostOneHeadersPerStatus,
      .multipleHeadersAtStatus endpoint.id (firstDuplicateStatus endpoint.headerStatuses))
  , (endpoint.requirementsLegal,
      .requirementNameIllegal endpoint.id endpoint.firstBadRequirement) ]

/-- Check an endpoint: the clauses in order, first refusal wins. -/
def check (endpoint : Endpoint refs) : Except Refusal Unit :=
  firstRefusal endpoint.clauses

/-- The proposition a handler capability opts into. -/
def WellFormed (endpoint : Endpoint refs) : Prop := Endpoint.check endpoint = .ok ()

instance (endpoint : Endpoint refs) : Decidable (Endpoint.WellFormed endpoint) := by
  unfold Endpoint.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one. -/
def wellFormed (endpoint : Endpoint refs) : Bool := decide (Endpoint.WellFormed endpoint)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (endpoint : Endpoint refs) :
    Endpoint.wellFormed endpoint = true ↔ Endpoint.WellFormed endpoint := by
  simp [Endpoint.wellFormed]

/-! ### The clauses as propositions -/

/-- The endpoint's id is a legal generated binding. -/
def IdLegal (endpoint : Endpoint refs) : Prop := endpoint.idLegal = true
/-- The annotation bag carries an `identifier`. -/
def Identified (endpoint : Endpoint refs) : Prop := endpoint.identified = true
/-- The annotation bag carries a `description`. -/
def Described (endpoint : Endpoint refs) : Prop := endpoint.described = true
/-- No path parameter name occurs twice. -/
def PathParamsDistinct (endpoint : Endpoint refs) : Prop := endpoint.pathParamsDistinct = true
/-- Every path parameter is a property of the `params` schema. -/
def PathParamsHaveSchema (endpoint : Endpoint refs) : Prop := endpoint.pathParamsHaveSchema = true
/-- Every property of the `params` schema is a path parameter. -/
def SchemaParamsInPath (endpoint : Endpoint refs) : Prop := endpoint.schemaParamsInPath = true
/-- A bodyless method declares no payload. -/
def BodylessHasNoPayload (endpoint : Endpoint refs) : Prop := endpoint.bodylessHasNoPayload = true
/-- The endpoint declares at least one success response. -/
def SuccessNonEmpty (endpoint : Endpoint refs) : Prop := endpoint.successNonEmpty = true
/-- Every status is a real HTTP status. -/
def StatusesInRange (endpoint : Endpoint refs) : Prop := endpoint.statusesInRange = true
/-- No success status is declared twice. -/
def SuccessStatusesDistinct (endpoint : Endpoint refs) : Prop :=
  endpoint.successStatusesDistinct = true
/-- No error status is declared twice. -/
def ErrorStatusesDistinct (endpoint : Endpoint refs) : Prop := endpoint.errorStatusesDistinct = true
/-- No status is both a success and an error. -/
def StatusesDisjoint (endpoint : Endpoint refs) : Prop := endpoint.statusesDisjoint = true
/-- No error response streams. -/
def NoStreamInErrors (endpoint : Endpoint refs) : Prop := endpoint.noStreamInErrors = true
/-- At most one success response streams. -/
def AtMostOneStreamSuccess (endpoint : Endpoint refs) : Prop :=
  endpoint.atMostOneStreamSuccess = true
/-- No status carries both a no-content and a streaming success. -/
def NoVoidAndStream (endpoint : Endpoint refs) : Prop := endpoint.noVoidAndStream = true
/-- No status carries both a buffered and a streaming success. -/
def NoBufferedAndStream (endpoint : Endpoint refs) : Prop := endpoint.noBufferedAndStream = true
/-- A `HEAD` endpoint never streams. -/
def HeadNeverStreams (endpoint : Endpoint refs) : Prop := endpoint.headNeverStreams = true
/-- No SSE event carries the reserved name. -/
def SseEventNamesFree (endpoint : Endpoint refs) : Prop := endpoint.sseEventNamesFree = true
/-- At most one response per status declares headers. -/
def AtMostOneHeadersPerStatus (endpoint : Endpoint refs) : Prop :=
  endpoint.atMostOneHeadersPerStatus = true
/-- Every service name the handler requires is a legal binding. -/
def RequirementsLegal (endpoint : Endpoint refs) : Prop := endpoint.requirementsLegal = true

/--
Well-formedness is exactly the conjunction of the named clauses.

This is what lets a capability of plan §14.3 ask for `PathParamsHaveSchema` and
`BodylessHasNoPayload` and nothing else, and still be handed them by a value
that was checked once.
-/
theorem wellFormed_iff (endpoint : Endpoint refs) :
    Endpoint.WellFormed endpoint ↔
      (Endpoint.IdLegal endpoint ∧ Endpoint.Identified endpoint ∧
        Endpoint.Described endpoint ∧ Endpoint.PathParamsDistinct endpoint ∧
        Endpoint.PathParamsHaveSchema endpoint ∧ Endpoint.SchemaParamsInPath endpoint ∧
        Endpoint.BodylessHasNoPayload endpoint ∧ Endpoint.SuccessNonEmpty endpoint ∧
        Endpoint.StatusesInRange endpoint ∧ Endpoint.SuccessStatusesDistinct endpoint ∧
        Endpoint.ErrorStatusesDistinct endpoint ∧ Endpoint.StatusesDisjoint endpoint ∧
        Endpoint.NoStreamInErrors endpoint ∧ Endpoint.AtMostOneStreamSuccess endpoint ∧
        Endpoint.NoVoidAndStream endpoint ∧ Endpoint.NoBufferedAndStream endpoint ∧
        Endpoint.HeadNeverStreams endpoint ∧ Endpoint.SseEventNamesFree endpoint ∧
        Endpoint.AtMostOneHeadersPerStatus endpoint ∧ Endpoint.RequirementsLegal endpoint) := by
  rw [Endpoint.WellFormed, Endpoint.check, firstRefusal_ok_iff]
  simp [Endpoint.clauses, Endpoint.IdLegal, Endpoint.Identified, Endpoint.Described,
    Endpoint.PathParamsDistinct, Endpoint.PathParamsHaveSchema, Endpoint.SchemaParamsInPath,
    Endpoint.BodylessHasNoPayload, Endpoint.SuccessNonEmpty, Endpoint.StatusesInRange,
    Endpoint.SuccessStatusesDistinct, Endpoint.ErrorStatusesDistinct,
    Endpoint.StatusesDisjoint, Endpoint.NoStreamInErrors, Endpoint.AtMostOneStreamSuccess,
    Endpoint.NoVoidAndStream, Endpoint.NoBufferedAndStream, Endpoint.HeadNeverStreams,
    Endpoint.SseEventNamesFree, Endpoint.AtMostOneHeadersPerStatus,
    Endpoint.RequirementsLegal]

end Endpoint

namespace Group

variable {refs : List ReferenceEntry}

/-- Clause: the group's id is a legal generated binding. -/
def idLegal (group : Group refs) : Bool := identifier group.id

/-- Clause (§15.2): the annotation bag carries an `identifier`. -/
def identified (group : Group refs) : Bool := (identifierIn group.annotations).isSome

/-- Clause (§15.2): the annotation bag carries a `description`. -/
def described (group : Group refs) : Bool := (descriptionIn group.annotations).isSome

/-- The ids of the group's endpoints, in order. -/
def endpointIds (group : Group refs) : List String := group.endpoints.map Endpoint.id

/-- Clause: no two endpoints of the group share an id
(`HttpApiGroup.ts:318`: the endpoints are a record keyed by id). -/
def endpointIdsDistinct (group : Group refs) : Bool := namesUnique group.endpointIds

/-- The clauses of a group, in the order a check reads them. -/
def clauses (group : Group refs) : List (Bool × Refusal) :=
  [ (group.idLegal, .nameIllegal "group" group.id)
  , (group.identified, .identifierMissing "group" group.id)
  , (group.described, .descriptionMissing "group" group.id)
  , (group.endpointIdsDistinct,
      .endpointIdDuplicate group.id (firstDuplicate group.endpointIds)) ]

/-- Check every endpoint of a group, first refusal wins. -/
def checkEndpoints : List (Endpoint refs) → Except Refusal Unit
  | [] => .ok ()
  | endpoint :: rest =>
    match Endpoint.check endpoint with
    | .error refusal => .error refusal
    | .ok _ => checkEndpoints rest

/-- Check a group: its own clauses, then every endpoint's. -/
def check (group : Group refs) : Except Refusal Unit :=
  Except.bind (firstRefusal group.clauses) fun _ => checkEndpoints group.endpoints

/-- The proposition an api's clause opts into. -/
def WellFormed (group : Group refs) : Prop := Group.check group = .ok ()

instance (group : Group refs) : Decidable (Group.WellFormed group) := by
  unfold Group.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one. -/
def wellFormed (group : Group refs) : Bool := decide (Group.WellFormed group)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (group : Group refs) :
    Group.wellFormed group = true ↔ Group.WellFormed group := by
  simp [Group.wellFormed]

/-! ### The clauses as propositions -/

/-- The group's id is a legal generated binding. -/
def IdLegal (group : Group refs) : Prop := group.idLegal = true
/-- The annotation bag carries an `identifier`. -/
def Identified (group : Group refs) : Prop := group.identified = true
/-- The annotation bag carries a `description`. -/
def Described (group : Group refs) : Prop := group.described = true
/-- No two endpoints of the group share an id. -/
def EndpointIdsDistinct (group : Group refs) : Prop := group.endpointIdsDistinct = true

/-- The endpoint walk succeeds exactly when every endpoint is well-formed. -/
theorem checkEndpoints_ok_iff :
    ∀ endpoints : List (Endpoint refs),
      Group.checkEndpoints endpoints = .ok () ↔
        ∀ endpoint ∈ endpoints, Endpoint.WellFormed endpoint
  | [] => by simp [Group.checkEndpoints]
  | endpoint :: rest => by
    simp only [Group.checkEndpoints]
    cases answer : Endpoint.check endpoint with
    | error refusal => simp [Endpoint.WellFormed, answer]
    | ok value =>
      cases value
      simp [Endpoint.WellFormed, answer, checkEndpoints_ok_iff rest]

/-- Well-formedness is exactly the conjunction of the group's own clauses and
its endpoints' well-formedness. -/
theorem wellFormed_iff (group : Group refs) :
    Group.WellFormed group ↔
      (Group.IdLegal group ∧ Group.Identified group ∧ Group.Described group ∧
        Group.EndpointIdsDistinct group ∧
        ∀ endpoint ∈ group.endpoints, Endpoint.WellFormed endpoint) := by
  rw [Group.WellFormed, Group.check, exceptSeq_ok_iff, firstRefusal_ok_iff,
    checkEndpoints_ok_iff group.endpoints]
  simp [Group.clauses, Group.IdLegal, Group.Identified, Group.Described,
    Group.EndpointIdsDistinct, and_assoc]

end Group

/-! ## Paths across the three levels -/

/-- The endpoint's path under its api's and its group's prefixes. This is the
one canonical spelling of "where the endpoint lives"; every other appearance is
a projection of it. -/
def Endpoint.fullPath {refs : List ReferenceEntry}
    (api : Api refs) (group : Group refs) (endpoint : Endpoint refs) : Path :=
  Path.prefixWith api.pathPrefix (Path.prefixWith group.pathPrefix endpoint.path)

namespace Api

variable {refs : List ReferenceEntry}

/-- Clause: the api's id is a legal generated binding. -/
def idLegal (api : Api refs) : Bool := identifier api.id

/-- Clause (§15.2): the annotation bag carries an `identifier`. -/
def identified (api : Api refs) : Bool := (identifierIn api.annotations).isSome

/-- Clause (§15.2): the annotation bag carries a `description`. -/
def described (api : Api refs) : Bool := (descriptionIn api.annotations).isSome

/-- The ids of the api's groups, in order. -/
def groupIds (api : Api refs) : List String := api.groups.map Group.id

/-- Clause: no two groups share an id (`HttpApi.ts:172`). -/
def groupIdsDistinct (api : Api refs) : Bool := namesUnique api.groupIds

/-- Every route the api serves: the method token and the rendered full path,
in declaration order. -/
def routes (api : Api refs) : List (String × String) :=
  api.groups.flatMap fun group =>
    group.endpoints.map fun endpoint =>
      (endpoint.method.spelling, (endpoint.fullPath api group).render)

/-- The routes as single keys, which is what distinctness is decided on. -/
def routeKeys (api : Api refs) : List String :=
  api.routes.map fun route => route.1 ++ " " ++ route.2

/-- Clause: no two endpoints share a method and a full path
(`OpenApi.ts:629`: `Duplicate OpenAPI operation`). -/
def routesDistinct (api : Api refs) : Bool := namesUnique api.routeKeys

/-- The first route declared twice, for the refusal to name. -/
def firstDuplicateRoute (api : Api refs) : String × String :=
  match api.routes.find? fun route =>
      route.1 ++ " " ++ route.2 == firstDuplicate api.routeKeys with
  | some route => route
  | none => ("", "")

/-- The clauses of an api, in the order a check reads them. -/
def clauses (api : Api refs) : List (Bool × Refusal) :=
  [ (api.idLegal, .nameIllegal "api" api.id)
  , (api.identified, .identifierMissing "api" api.id)
  , (api.described, .descriptionMissing "api" api.id)
  , (api.groupIdsDistinct, .groupIdDuplicate api.id (firstDuplicate api.groupIds))
  , (api.routesDistinct,
      .routeCollision api.id api.firstDuplicateRoute.1 api.firstDuplicateRoute.2) ]

/-- Check every group of an api, first refusal wins. -/
def checkGroups : List (Group refs) → Except Refusal Unit
  | [] => .ok ()
  | group :: rest =>
    match Group.check group with
    | .error refusal => .error refusal
    | .ok _ => checkGroups rest

/-- Check an api: its own clauses, then every group's. -/
def check (api : Api refs) : Except Refusal Unit :=
  Except.bind (firstRefusal api.clauses) fun _ => checkGroups api.groups

/-- The proposition every emitter below requires. -/
def WellFormed (api : Api refs) : Prop := Api.check api = .ok ()

instance (api : Api refs) : Decidable (Api.WellFormed api) := by
  unfold Api.WellFormed; infer_instance

/-- The Bool projection, for a battery and for the emitters. -/
def wellFormed (api : Api refs) : Bool := decide (Api.WellFormed api)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (api : Api refs) :
    Api.wellFormed api = true ↔ Api.WellFormed api := by
  simp [Api.wellFormed]

/-! ### The clauses as propositions -/

/-- The api's id is a legal generated binding. -/
def IdLegal (api : Api refs) : Prop := api.idLegal = true
/-- The annotation bag carries an `identifier`. -/
def Identified (api : Api refs) : Prop := api.identified = true
/-- The annotation bag carries a `description`. -/
def Described (api : Api refs) : Prop := api.described = true
/-- No two groups share an id. -/
def GroupIdsDistinct (api : Api refs) : Prop := api.groupIdsDistinct = true
/-- No two endpoints share a method and a full path. -/
def RoutesDistinct (api : Api refs) : Prop := api.routesDistinct = true

/-- The group walk succeeds exactly when every group is well-formed. -/
theorem checkGroups_ok_iff :
    ∀ groups : List (Group refs),
      Api.checkGroups groups = .ok () ↔ ∀ group ∈ groups, Group.WellFormed group
  | [] => by simp [Api.checkGroups]
  | group :: rest => by
    simp only [Api.checkGroups]
    cases answer : Group.check group with
    | error refusal => simp [Group.WellFormed, answer]
    | ok value =>
      cases value
      simp [Group.WellFormed, answer, checkGroups_ok_iff rest]

/-- Well-formedness is exactly the conjunction of the api's own clauses and its
groups' well-formedness. -/
theorem wellFormed_iff (api : Api refs) :
    Api.WellFormed api ↔
      (Api.IdLegal api ∧ Api.Identified api ∧ Api.Described api ∧
        Api.GroupIdsDistinct api ∧ Api.RoutesDistinct api ∧
        ∀ group ∈ api.groups, Group.WellFormed group) := by
  rw [Api.WellFormed, Api.check, exceptSeq_ok_iff, firstRefusal_ok_iff,
    checkGroups_ok_iff api.groups]
  simp [Api.clauses, Api.IdLegal, Api.Identified, Api.Described, Api.GroupIdsDistinct,
    Api.RoutesDistinct, and_assoc]

end Api

/-- Every group of a well-formed api is well-formed. -/
theorem Api.wellFormed_group {refs : List ReferenceEntry} (api : Api refs)
    (h : Api.WellFormed api) (group : Group refs) (mem : group ∈ api.groups) :
    Group.WellFormed group :=
  ((Api.wellFormed_iff api).mp h).2.2.2.2.2 group mem

/-- Every endpoint of a well-formed api is well-formed. This is the theorem the
emitters lean on: they never re-check an endpoint they reached through an api. -/
theorem Api.wellFormed_endpoint {refs : List ReferenceEntry} (api : Api refs)
    (h : Api.WellFormed api) (group : Group refs) (mem : group ∈ api.groups)
    (endpoint : Endpoint refs) (inner : endpoint ∈ group.endpoints) :
    Endpoint.WellFormed endpoint :=
  ((Group.wellFormed_iff group).mp (Api.wellFormed_group api h group mem)).2.2.2.2 endpoint inner

/-- A well-formed api's routes are distinct, which is what makes the emitted
router total. -/
theorem Api.routes_unique {refs : List ReferenceEntry} (api : Api refs)
    (h : Api.WellFormed api) : namesUnique api.routeKeys = true :=
  ((Api.wellFormed_iff api).mp h).2.2.2.2.1

/-! ## Plain projections the later waves join on -/

namespace ResponseBody

variable {refs : List ReferenceEntry}

/-- The entity a buffered body names, when its schema is a bare `$ref`. A
stream body names none: wave 2d's handler type reads the stream's element
schema through `rep?`, not through this. -/
def entity? : ResponseBody refs → Option String
  | .json schema =>
    match schema.rep with
    | .reference key => some key.value
    | _ => none
  | _ => none

end ResponseBody

namespace Endpoint

variable {refs : List ReferenceEntry}

/-- The entity names the endpoint answers on success: wave 2d's `answerTy`. -/
def successEntities (endpoint : Endpoint refs) : List String :=
  endpoint.success.filterMap fun response => response.body.entity?

/-- The entity names the endpoint fails with: wave 2d's `errorTy`. -/
def errorEntities (endpoint : Endpoint refs) : List String :=
  endpoint.errors.filterMap fun response => response.body.entity?

end Endpoint

/-- Drop repeats, keeping the first occurrence. The accumulator is what makes
this structural rather than well-founded, so it reduces under `#guard`. -/
def dedupNames (seen : List String) : List String → List String
  | [] => []
  | first :: rest =>
    if seen.contains first then dedupNames seen rest
    else first :: dedupNames (seen ++ [first]) rest

namespace Api

variable {refs : List ReferenceEntry}

/-- Every endpoint as a row: api id, group id, endpoint id, and whether it
carries a payload. This is the join key wave 2d's handlers and wave 3d's
manifest read. -/
def endpointTable (api : Api refs) : List (String × String × String × Bool) :=
  api.groups.flatMap fun group =>
    group.endpoints.map fun endpoint =>
      (api.id, group.id, endpoint.id, endpoint.payload.isSome)

/-- Every endpoint's service requirements, keyed by endpoint id. -/
def requirements (api : Api refs) : List (String × List String) :=
  api.groups.flatMap fun group =>
    group.endpoints.map fun endpoint => (endpoint.id, endpoint.requires)

/-- Every service name the api needs, deduplicated, in first-use order. This is
what a deployment's `provides` is checked against in wave 2c. -/
def requirementNames (api : Api refs) : List String :=
  dedupNames [] (api.requirements.flatMap Prod.snd)

/-- Every endpoint of the api, with the group it came from. -/
def endpoints (api : Api refs) : List (Group refs × Endpoint refs) :=
  api.groups.flatMap fun group => group.endpoints.map fun endpoint => (group, endpoint)

end Api

/-! ## The view -/

/-- One representation as the view's payload; `null` when it does not persist. -/
def repJson (representation : Representation) : Json :=
  (Arch.Representation.toJson? representation).getD .null

/-- An optional kinded schema as the view's payload. -/
def schemaJson {refs : List ReferenceEntry} {k : Kind} (schema : Option (Sch refs k)) : Json :=
  match schema with
  | none => .null
  | some value => repJson value.rep

/-- One annotation bag as the view's payload. -/
def annotationsJson (annotations : Annotations) : Json :=
  match annotations with
  | none => .null
  | some entries =>
    .arr (entries.map fun entry => .obj [("key", .str entry.key), ("payload", entry.payload)])

/-- An optional path as the view's payload. -/
def pathJson (path : Option Path) : Json :=
  match path with
  | none => .null
  | some value => .str value.render

/-- One response body as the view's payload. The name is `view`, not `json`:
`ResponseBody.json` is a constructor of this very inductive. -/
def ResponseBody.view {refs : List ReferenceEntry} (body : ResponseBody refs) : Json :=
  .obj
    [ ("kind", .str body.kindName)
    , ("schema", match body.rep? with | none => .null | some rep => repJson rep)
    , ("events", .arr (body.eventNames.map Json.str)) ]

/-- One response as the view's payload. -/
def Response.json {refs : List ReferenceEntry} (response : Response refs) : Json :=
  .obj
    [ ("status", Arch.Json.ofNat response.status)
    , ("body", response.body.view)
    , ("headers", schemaJson response.headers)
    , ("annotations", annotationsJson response.annotations) ]

/-- One payload as the view's payload. The name is `view`, not `json`:
`Payload.json` is a constructor of this very inductive. -/
def Payload.view {refs : List ReferenceEntry} (payload : Payload refs) : Json :=
  .obj
    [ ("kind", .str payload.kindName)
    , ("contentType", .str payload.contentType)
    , ("schema", repJson payload.rep) ]

/-- One endpoint as the view's payload. -/
def Endpoint.json {refs : List ReferenceEntry} (endpoint : Endpoint refs) : Json :=
  .obj
    [ ("id", .str endpoint.id)
    , ("method", .str endpoint.method.spelling)
    , ("path", .str endpoint.path.render)
    , ("params", schemaJson endpoint.params)
    , ("query", schemaJson endpoint.query)
    , ("headers", schemaJson endpoint.headers)
    , ("payload", match endpoint.payload with | none => .null | some p => p.view)
    , ("success", .arr (endpoint.success.map Response.json))
    , ("errors", .arr (endpoint.errors.map Response.json))
    , ("security", .arr (endpoint.security.map Security.json))
    , ("requires", .arr (endpoint.requires.map Json.str))
    , ("annotations", annotationsJson endpoint.annotations) ]

/-- One group as the view's payload. -/
def Group.json {refs : List ReferenceEntry} (group : Group refs) : Json :=
  .obj
    [ ("id", .str group.id)
    , ("pathPrefix", pathJson group.pathPrefix)
    , ("endpoints", .arr (group.endpoints.map Endpoint.json))
    , ("topLevel", .bool group.topLevel)
    , ("annotations", annotationsJson group.annotations) ]

/-- One api as the view's payload. -/
def Api.json {refs : List ReferenceEntry} (api : Api refs) : Json :=
  .obj
    [ ("id", .str api.id)
    , ("pathPrefix", pathJson api.pathPrefix)
    , ("groups", .arr (api.groups.map Group.json))
    , ("annotations", annotationsJson api.annotations) ]

/-- The response view's representation. -/
def responseRep : Representation :=
  Schema.struct
    [ Schema.property "status" Schema.number
    , Schema.property "body" Schema.unknown
    , Schema.property "headers" Schema.unknown
    , Schema.property "annotations" Schema.unknown ]

/-- The endpoint view's representation. -/
def endpointRep : Representation :=
  Schema.struct
    [ Schema.property "id" Schema.string
    , Schema.property "method" Schema.string
    , Schema.property "path" Schema.string
    , Schema.property "params" Schema.unknown
    , Schema.property "query" Schema.unknown
    , Schema.property "headers" Schema.unknown
    , Schema.property "payload" Schema.unknown
    , Schema.property "success" (Schema.array (Schema.reference "Response"))
    , Schema.property "errors" (Schema.array (Schema.reference "Response"))
    , Schema.property "security" (Schema.array Schema.unknown)
    , Schema.property "requires" (Schema.array Schema.string)
    , Schema.property "annotations" Schema.unknown ]

/-- The group view's representation. -/
def groupRep : Representation :=
  Schema.struct
    [ Schema.property "id" Schema.string
    , Schema.property "pathPrefix" Schema.unknown
    , Schema.property "endpoints" (Schema.array (Schema.reference "Endpoint"))
    , Schema.property "topLevel" Schema.boolean
    , Schema.property "annotations" Schema.unknown ]

/-- The api view's representation. -/
def apiRep : Representation :=
  Schema.struct
    [ Schema.property "id" Schema.string
    , Schema.property "pathPrefix" Schema.unknown
    , Schema.property "groups" (Schema.array (Schema.reference "Group"))
    , Schema.property "annotations" Schema.unknown ]

/-- The api view, for registration at `["surface", "api"]` by `Views.lean`. -/
def apiDoc : Document :=
  { representation := apiRep
    references :=
      [ ⟨"Response", responseRep⟩, ⟨"Endpoint", endpointRep⟩, ⟨"Group", groupRep⟩ ] }

/-! ## Anti-vacuity: the `shop` api

The domain is `Effect4/Surface/Entity.lean`'s `shopDomain`, extended with the
tagged error entity `NotFound` the plan's §13.3 table asks every api to have.
Every row carries its semantics, because §15.2 makes a row without one
ill-formed.
-/

/-- One described property, as `Entity.lean`'s fixture spells it. -/
private def field (name text : String) (type : Representation)
    (optional : Bool := false) : PropertySignature :=
  PropertySignature.describe text (Schema.property name type optional)

/-- One described, identified entity representation. -/
private def entityRepOf (name text : String) (properties : List PropertySignature) :
    Representation :=
  Representation.describe text (Representation.identify name (Schema.struct properties))

/-- The tagged error entity every api needs: a `_tag` literal, the resource and
the id that were not found. -/
def notFoundEntity : Entity :=
  { name := "NotFound"
    domain := "shop"
    rep := entityRepOf "NotFound" "Nothing of that name exists."
      [ field "_tag" "The error tag rc.112 discriminates on."
          (Schema.literalString "NotFound")
      , field "resource" "Which kind of thing was looked for." Schema.string
      , field "id" "The identifier that resolved to nothing." Schema.string ]
    key := ["id"] }

/-- The fixture domain: `shopDomain` plus its tagged error. -/
def shopApiDomain : Domain :=
  { name := "shop"
    entities := shopDomain.entities ++ [notFoundEntity]
    active := true }

/-- The fixture domain is well-formed, by the kernel. -/
theorem shopApiDomain_wellFormed : Domain.WellFormed shopApiDomain := by decide

/-- The references table every fixture schema below is kinded against. -/
def shopRefs : List ReferenceEntry := shopApiDomain.refs

/-- The path parameters of the by-id endpoints. -/
def idParams : Sch shopRefs .text :=
  ⟨Schema.struct [field "id" "The customer id." Schema.string], by decide⟩

/-- The query of the list endpoint: an optional role filter. -/
def roleQuery : Sch shopRefs .text :=
  ⟨Schema.struct
      [ field "role" "Only customers with this role."
          (Schema.anyOf (Schema.literalString "admin") [Schema.literalString "member"]) true ],
    by decide⟩

/-- The `User` body. -/
def userBody : Sch shopRefs .json := ⟨Schema.reference "User", by decide⟩

/-- A list of `User` bodies. -/
def userListBody : Sch shopRefs .json :=
  ⟨Schema.array (Schema.reference "User"), by decide⟩

/-- The `NotFound` body. -/
def notFoundBody : Sch shopRefs .json := ⟨Schema.reference "NotFound", by decide⟩

/-- The response headers of the list endpoint. -/
def totalHeader : Sch shopRefs .text :=
  ⟨Schema.struct [field "x-total-count" "How many customers matched." Schema.string],
    by decide⟩

/-- `GET /api/users`. -/
def listUsers : Endpoint shopRefs :=
  { id := "listUsers"
    method := .get
    path := ⟨[]⟩
    query := some roleQuery
    success := [{ status := 200, body := .json userListBody, headers := some totalHeader
                  annotations := describedBag "listUsers.200" "Every matching customer." }]
    requires := ["Db"]
    annotations := describedBag "listUsers" "List the shop's customers." }

/-- `GET /api/users/:id`. -/
def getUser : Endpoint shopRefs :=
  { id := "getUser"
    method := .get
    path := ⟨[.param "id"]⟩
    params := some idParams
    success := [{ status := 200, body := .json userBody
                  annotations := describedBag "getUser.200" "The customer." }]
    errors := [{ status := 404, body := .json notFoundBody
                 annotations := describedBag "getUser.404" "No such customer." }]
    requires := ["Db"]
    annotations := describedBag "getUser" "Read one customer by id." }

/-- `POST /api/users`. -/
def createUser : Endpoint shopRefs :=
  { id := "createUser"
    method := .post
    path := ⟨[]⟩
    payload := some (.json userBody)
    success := [{ status := 201, body := .void
                  annotations := describedBag "createUser.201" "The customer was created." }]
    requires := ["Db"]
    annotations := describedBag "createUser" "Create a customer." }

/-- `PATCH /api/users/:id`. -/
def updateUser : Endpoint shopRefs :=
  { id := "updateUser"
    method := .patch
    path := ⟨[.param "id"]⟩
    params := some idParams
    payload := some (.json userBody)
    success := [{ status := 200, body := .json userBody
                  annotations := describedBag "updateUser.200" "The updated customer." }]
    errors := [{ status := 404, body := .json notFoundBody
                 annotations := describedBag "updateUser.404" "No such customer." }]
    requires := ["Db"]
    annotations := describedBag "updateUser" "Update one customer by id." }

/-- `DELETE /api/users/:id`. -/
def removeUser : Endpoint shopRefs :=
  { id := "removeUser"
    method := .delete
    path := ⟨[.param "id"]⟩
    params := some idParams
    success := [{ status := 204, body := .void
                  annotations := describedBag "removeUser.204" "The customer is gone." }]
    errors := [{ status := 404, body := .json notFoundBody
                 annotations := describedBag "removeUser.404" "No such customer." }]
    requires := ["Db", "Audit"]
    annotations := describedBag "removeUser" "Delete one customer by id." }

/-- The fixture group. -/
def usersGroup : Group shopRefs :=
  { id := "users"
    pathPrefix := some ⟨[.literal "users"]⟩
    endpoints := [listUsers, getUser, createUser, updateUser, removeUser]
    annotations := describedBag "users" "Everything about the shop's customers." }

/-- The fixture api. -/
def shopApi : Api shopRefs :=
  { id := "ShopApi"
    pathPrefix := some ⟨[.literal "api"]⟩
    groups := [usersGroup]
    annotations := describedBag "ShopApi" "The shop's HTTP API." }

/-- The fixture api is well-formed, by the kernel. -/
theorem shopApi_wellFormed : Api.WellFormed shopApi := by decide

/-- And so is every endpoint in it, read off `wellFormed_iff` rather than
`decide`d again. -/
theorem getUser_wellFormed : Endpoint.WellFormed getUser :=
  Api.wellFormed_endpoint shopApi shopApi_wellFormed usersGroup (List.Mem.head _)
    getUser (List.Mem.tail _ (List.Mem.head _))

/-- The clause a later capability opts into, read off the same theorem. -/
theorem getUser_paramsMatchPath : Endpoint.PathParamsHaveSchema getUser :=
  ((Endpoint.wellFormed_iff getUser).mp getUser_wellFormed).2.2.2.2.1

/-- A well-formed api serves distinct routes. -/
theorem shopApi_routes_unique : namesUnique shopApi.routeKeys = true :=
  Api.routes_unique shopApi shopApi_wellFormed

/-! ### The path fragment -/

#guard (Path.mk []).render == "/"
#guard (Path.mk [.literal "users"]).render == "/users"
#guard (Path.mk [.literal "users", .param "id"]).render == "/users/:id"
#guard Path.parse? "/" == some ⟨[]⟩
#guard Path.parse? "/users/:id" == some ⟨[.literal "users", .param "id"]⟩
#guard Path.parse? "users" == none
#guard Path.parse? "/users//id" == none
#guard Path.parse? "/*" == none
#guard Path.parse? "/users/:1st" == none
#guard Path.parse? "/users/:class" == none
#guard (Path.mk [.literal "users", .param "id"]).spelled
#guard (Path.mk [.literal "*"]).spelled == false
#guard (Path.mk [.param "1st"]).spelled == false
#guard Path.parse? (Path.mk [.literal "a", .param "b", .literal "c"]).render ==
  some ⟨[.literal "a", .param "b", .literal "c"]⟩
-- the ASCII edge, on both sides: a non-ASCII literal is not spelled, and its
-- template is refused rather than half-read. `Path.parse?_render` is the
-- theorem that everything `spelled` does admit round-trips.
#guard (Path.mk [.literal "café"]).spelled == false
#guard Path.parse? "/café" == none
#guard (Path.mk [.literal "users"]).paramNames == []
#guard (Path.mk [.literal "users", .param "id"]).paramNames == ["id"]

/-! ### The methods -/

#guard Method.census.map Method.spelling ==
  ["GET", "POST", "PUT", "PATCH", "DELETE", "HEAD", "OPTIONS"]
#guard Method.census.map Method.lower ==
  ["get", "post", "put", "patch", "delete", "head", "options"]
#guard Method.census.map Method.bodyless == [true, false, false, false, false, true, true]
#guard Method.ofSpelling? "GET" == some .get
#guard Method.ofSpelling? "TRACE" == none

/-! ### The fixture's own receipts -/

#guard Api.check shopApi == .ok ()
#guard Api.wellFormed shopApi
#guard shopApi.routes ==
  [ ("GET", "/api/users"), ("GET", "/api/users/:id"), ("POST", "/api/users")
  , ("PATCH", "/api/users/:id"), ("DELETE", "/api/users/:id") ]
#guard (getUser.fullPath shopApi usersGroup).render == "/api/users/:id"
#guard shopApi.endpointTable ==
  [ ("ShopApi", "users", "listUsers", false)
  , ("ShopApi", "users", "getUser", false)
  , ("ShopApi", "users", "createUser", true)
  , ("ShopApi", "users", "updateUser", true)
  , ("ShopApi", "users", "removeUser", false) ]
#guard shopApi.requirements ==
  [ ("listUsers", ["Db"]), ("getUser", ["Db"]), ("createUser", ["Db"])
  , ("updateUser", ["Db"]), ("removeUser", ["Db", "Audit"]) ]
#guard shopApi.requirementNames == ["Db", "Audit"]
#guard getUser.successEntities == ["User"]
#guard getUser.errorEntities == ["NotFound"]
#guard listUsers.successEntities == []
#guard identifierIn shopApi.annotations == some "ShopApi"
#guard descriptionIn shopApi.annotations == some "The shop's HTTP API."

-- the view accepts its own payload, and refuses one that is not its own
#guard accepts apiDoc shopApi.json = true
#guard accepts apiDoc usersGroup.json = false
#guard accepts apiDoc (.obj [("id", .str "ShopApi")]) = false

/-! ### One refused mutant per endpoint clause -/

private def streamBody : ResponseBody shopRefs := .stream userBody ["update"]
private def reservedStreamBody : ResponseBody shopRefs :=
  .stream userBody [reservedStreamFailureEvent]
private def okBag : Annotations := describedBag "probe" "a probe response"

#guard Endpoint.check { getUser with id := "class" } ==
  .error (.nameIllegal "endpoint" "class")
#guard Endpoint.check { getUser with annotations := none } ==
  .error (.identifierMissing "endpoint" "getUser")
#guard Endpoint.check { getUser with annotations := identifierKey.singleton "getUser" } ==
  .error (.descriptionMissing "endpoint" "getUser")
#guard Endpoint.check { getUser with path := ⟨[.param "id", .param "id"]⟩ } ==
  .error (.pathParamDuplicate "getUser" "id")
#guard Endpoint.check { getUser with path := ⟨[.param "slug"]⟩ } ==
  .error (.pathParamWithoutSchema "getUser" "slug")
#guard Endpoint.check { getUser with path := ⟨[]⟩ } ==
  .error (.schemaParamWithoutPath "getUser" "id")
#guard Endpoint.check { getUser with payload := some (.json userBody) } ==
  .error (.payloadOnBodylessMethod "getUser")
#guard Endpoint.check { getUser with success := [] } ==
  .error (.successEmpty "getUser")
#guard Endpoint.check
    { getUser with success := [{ status := 99, body := .void, annotations := okBag }] } ==
  .error (.statusOutOfRange "getUser" 99)
#guard Endpoint.check
    { getUser with success :=
        [ { status := 200, body := .json userBody, annotations := okBag }
        , { status := 200, body := .json userBody, annotations := okBag } ] } ==
  .error (.statusCollision "getUser" 200)
#guard Endpoint.check
    { getUser with errors :=
        [ { status := 404, body := .json notFoundBody, annotations := okBag }
        , { status := 404, body := .json notFoundBody, annotations := okBag } ] } ==
  .error (.statusCollision "getUser" 404)
#guard Endpoint.check
    { getUser with errors :=
        [{ status := 200, body := .json notFoundBody, annotations := okBag }] } ==
  .error (.statusCollision "getUser" 200)
#guard Endpoint.check
    { getUser with errors := [{ status := 404, body := streamBody, annotations := okBag }] } ==
  .error (.streamInError "getUser" 404)
#guard Endpoint.check
    { getUser with success :=
        [ { status := 200, body := streamBody, annotations := okBag }
        , { status := 201, body := streamBody, annotations := okBag } ] } ==
  .error (.multipleStreamSuccess "getUser")
#guard Endpoint.check
    { getUser with success :=
        [ { status := 200, body := .void, annotations := okBag }
        , { status := 200, body := streamBody, annotations := okBag } ] } ==
  .error (.voidAndStreamAtStatus "getUser" 200)
#guard Endpoint.check
    { getUser with success :=
        [ { status := 200, body := .json userBody, annotations := okBag }
        , { status := 200, body := streamBody, annotations := okBag } ] } ==
  .error (.streamWithBufferedStatus "getUser" 200)
private def headStreams : Endpoint shopRefs :=
  { getUser with
    method := .head
    path := ⟨[]⟩
    params := none
    success := [{ status := 200, body := streamBody, annotations := okBag }] }

#guard Endpoint.check headStreams == .error (.streamOnHead "getUser")
#guard Endpoint.check
    { getUser with success := [{ status := 200, body := reservedStreamBody,
                                 annotations := okBag }] } ==
  .error (.sseEventNameReserved "getUser" reservedStreamFailureEvent)
#guard Endpoint.check
    { getUser with success :=
        [ { status := 200, body := .json userBody, headers := some totalHeader,
            annotations := okBag }
        , { status := 200, body := .void, headers := some totalHeader,
            annotations := okBag } ] } ==
  .error (.multipleHeadersAtStatus "getUser" 200)
#guard Endpoint.check { getUser with requires := ["class"] } ==
  .error (.requirementNameIllegal "getUser" "class")

/-! ### One refused mutant per group and api clause -/

#guard Group.check { usersGroup with id := "class" } ==
  .error (.nameIllegal "group" "class")
#guard Group.check { usersGroup with annotations := none } ==
  .error (.identifierMissing "group" "users")
#guard Group.check { usersGroup with annotations := identifierKey.singleton "users" } ==
  .error (.descriptionMissing "group" "users")
#guard Group.check { usersGroup with endpoints := [getUser, getUser] } ==
  .error (.endpointIdDuplicate "users" "getUser")
#guard Group.check { usersGroup with endpoints := [{ getUser with requires := ["class"] }] } ==
  .error (.requirementNameIllegal "getUser" "class")

#guard Api.check { shopApi with id := "class" } == .error (.nameIllegal "api" "class")
#guard Api.check { shopApi with annotations := none } ==
  .error (.identifierMissing "api" "ShopApi")
#guard Api.check { shopApi with annotations := identifierKey.singleton "ShopApi" } ==
  .error (.descriptionMissing "api" "ShopApi")
#guard Api.check { shopApi with groups := [usersGroup, usersGroup] } ==
  .error (.groupIdDuplicate "ShopApi" "users")
private def peopleGroup : Group shopRefs :=
  { usersGroup with
    id := "people"
    endpoints := [getUser]
    annotations := describedBag "people" "The same route, twice." }

#guard Api.check { shopApi with groups := [usersGroup, peopleGroup] } ==
  .error (.routeCollision "ShopApi" "GET" "/api/users/:id")
#guard Api.check { shopApi with groups := [{ usersGroup with id := "class" }] } ==
  .error (.nameIllegal "group" "class")

end Effect4.Surface
