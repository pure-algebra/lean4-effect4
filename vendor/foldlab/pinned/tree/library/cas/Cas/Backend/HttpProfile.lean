import Cas.Core.Node
import Cas.Grammar.Sorts

/-!
# `cas-http/0` — the wire profile as data

The trust census's modelless-wire-law finding, answered at the level a
manifest answers it. `library/effects/PROFILE-CAS-HTTP-0.md` is the
normative wire contract and it is PROSE; `src/server/Protocol.ts` and
`src/internal/wire.ts` are hand mirrors of that prose with nothing
between them and it. Two artifacts, one law, no join — the same shape
`Cas/Grammar/Manifest.lean` was written to remove for the data grammar,
one plane over.

This module declares the profile's first-order content the way
`Cas/Grammar/Sorts.lean` declares the sort table: the three resource
spaces and their path grammar, the profile header, the six resources
with their methods and bodies, the status table, the canonical
key-list framing, the capability envelope's byte layout, the presence
alphabet, and §12's blob node shapes. Every declaration cites the
profile section it reads; where the profile and the store model already
agree — the address width, the blob kind tags, the scheme version byte
— the agreement is a theorem rather than a coincidence of two tables.

## What v0 declares, and what it deliberately does not

The manifest DECLARES. It says what paths exist, what bodies they
carry, which statuses are in the alphabet, and how the two control
documents are laid out in bytes. It does NOT model request/response
SEMANTICS: no exchange relation, no state machine, no admission, no
claim about what a server computes between reading a request and
choosing a status. `Cas/Lang/Handler.lean` is where meaning lives and
this module does not reach it. A row here is a shape, not a promise.

Two consequences worth saying out loud. Nothing below reads the
TypeScript, so nothing below can go red when a mirror drifts — the
strings are a hand column in exactly the sense
`Cas/Backend/Admission.lean`'s clause column is. And nothing below is
evidence about the profile prose: where the two disagree the prose
wins, because the prose is the authority and this is a reading of it.

owed(http-profile-emitter): the emitter that prints this manifest as
the generated wire document, the way `emitgrammar` prints the grammar
manifest.
owed(http-profile-gate): the byte gate that holds `Protocol.ts`'s path
table, status table and `wire.ts`'s envelope layout to the printed
document — the step that turns this declaration into a mirror that
cannot drift.
owed(http-profile-semantics): the exchange relation. Until it exists,
"the wire law is modeled" means the SYNTAX is modeled.
-/

namespace Cas.Backend.HttpProfile

/-! ## §1 — the profile's own names -/

/-- The profile revision this manifest declares. Endpoints are added to
`/0` only additively; any change to the meaning of an existing exchange
mints `cas-http/1` (§1). -/
def profile : String := "cas-http/0"

/-- §1 — the header naming the profile. Every conforming request
carries it; a server may refuse a request whose value is absent or
names a profile it does not serve. -/
def profileHeader : String := "cas-profile"

/-- §1 — the one media type, compared EXACTLY. Every request and
response body is this or the profile does not govern it. -/
def mediaType : String := "application/octet-stream"

/-- §1 — the accept header a conforming request also carries, with
`mediaType` as its value. -/
def acceptHeader : String := "accept"

/-- §1 — the request's own media type header. -/
def contentTypeHeader : String := "content-type"

/-- §9 — the opaque bearer credential's header, scoped to exactly one
authority and never accompanying a request anywhere else. -/
def authorizationHeader : String := "authorization"

/-- §9 — the one credential scheme at `/0`. There is no challenge
negotiation: a `401` is terminal for its operation. -/
def bearerScheme : String := "Bearer"

/-- §1 — the only retry hint honored, and only in its non-negative
integer-seconds form; any other value leaves the rate-limit event
without a delay rather than making the response a violation. -/
def retryAfterHeader : String := "retry-after"

/-- §1 — content encoding is identity-only at `/0`: any non-identity
`content-encoding` on a response is a typed protocol violation. -/
def identityEncoding : String := "identity"

/-- §1, §9 — the request headers the profile governs, as data. -/
def governedRequestHeaders : List String :=
  [profileHeader, acceptHeader, contentTypeHeader, authorizationHeader]

theorem governedRequestHeaders_nodup : governedRequestHeaders.Nodup := by
  decide

/-! ## §2 — addressing, scheme 0

An address is the full thirty-two-byte SHA-256 digest of the node's
canonical encoding — exactly those bytes, nothing prepended, never
truncated. Domain separation lives inside the digest input because the
canonical encoding already carries the version byte, kind tag and
length frames. Path hex is lowercase. -/

/-- §2 — the address width in bytes. -/
def addressBytes : Nat := 32

/-- §2 — the address width as the path spells it: lowercase hex. -/
def addressHexDigits : Nat := 64

/-- The path's hex width is the address width, spelled two digits to
the byte. The profile states both numbers; only one of them is free. -/
theorem addressHexDigits_eq_twice_bytes :
    addressHexDigits = 2 * addressBytes := by decide

/-- §2 against the store model: the profile's declared address width IS
the model's `Addr32`. The subtype carries the invariant, so this is the
carrier's own property read at the profile's number — the one place the
wire law and the store's carrier are pinned to each other. -/
theorem addressBytes_is_Addr32 (a : Cas.Addr32) :
    a.val.length = addressBytes := a.property

/-! ## §1, §14 — the three resource spaces -/

/-- §1 — the three resource spaces on one authority. §14 reserves all
three to the profile on any authority that serves it: a co-tenant may
not shadow them. -/
inductive Space where
  /-- The data plane (§3). -/
  | cas
  /-- The control plane (§5, §6). -/
  | control
  /-- The root registry (§7). -/
  | roots
  deriving DecidableEq, Repr

def Space.all : List Space := [.cas, .control, .roots]

theorem Space.all_complete (s : Space) : s ∈ all := by cases s <;> decide

/-- The path segment reserved to each space. -/
def Space.segment : Space → String
  | .cas => "cas"
  | .control => "control"
  | .roots => "roots"

/-- Whether the space's resources are named by a 64-hex address (§3,
§7) or by a fixed word (§5, §6). -/
def Space.addressed : Space → Bool
  | .cas => true
  | .control => false
  | .roots => true

/-- One position in a path template: a literal segment, or the
address position — `[0-9a-f]{64}`, lowercase, per §2. -/
inductive Segment where
  | lit (name : String)
  | addr
  deriving DecidableEq, Repr

/-- A path template: the segments after the authority, in order. -/
abbrev Path := List Segment

def Segment.render : Segment → String
  | .lit name => name
  | .addr => "<64hex>"

/-- The path template as the profile writes it. -/
def renderPath (p : Path) : String :=
  p.foldl (fun acc s => acc ++ "/" ++ s.render) ""

/-- The one-segment paths §14 reserves to the profile. -/
def reservedPaths : List Path := Space.all.map fun s => [Segment.lit s.segment]

/-- The space segments are pairwise distinct, so a path's head segment
decides at most one space. -/
theorem Space.segments_nodup : (Space.all.map Space.segment).Nodup := by
  decide

/-! ## §3, §5, §6, §7 — the resources -/

inductive Method where
  | get | put | post
  deriving DecidableEq, Repr

def Method.wire : Method → String
  | .get => "GET"
  | .put => "PUT"
  | .post => "POST"

/-- The closed set of body shapes the profile carries. The framing IS
the codec; the profile carries no JSON (§1). -/
inductive Body where
  /-- No body — or, on an acknowledgment, the CLOSED EMPTY body of §3:
  a declared non-zero length, or any body byte at all, is the
  unexpected-body violation. -/
  | empty
  /-- One canonical node, exactly its bytes (§3). -/
  | nodeBytes
  /-- The canonical key-list document (§4). -/
  | keyList
  /-- The eight-byte capability envelope (§5). -/
  | capability
  /-- Exactly N status bytes, positionally aligned to the request
  order (§6). -/
  | presence
  deriving DecidableEq, Repr

/-! ### §1, §3, §6, §7 — the status table

The alphabet comes before the path grammar because a resource row is
stated over it: an exchange is a path, a method, two body shapes, and
the statuses that close it.

Two rows are cited carefully, because reading the prose closely is what
this manifest is for. §1 enumerates its status→event table as
`401`/`403`/`429`/`3xx`/`503`/`507` and never mentions `400` or `405`;
§14 nonetheless attributes both to "§1's table" when it says unknown
paths and wrong methods stay `400`/`405`. The two rows below therefore
cite §14, which is the only section that declares them, and the
attribution is the profile's own gap rather than this reading's. The
manifest declares what the prose declares — a status being in this
alphabet says nothing about whether any host emits it. -/

/-- The status→event alphabet. One table for every endpoint (§1). The
3xx class is deliberately absent: every `3xx` is a REDIRECT EVENT the
shell never follows, so no row may claim one — `Status.codes_avoid_redirect`
below. -/
inductive Status where
  | ok | created | noContent
  | badRequest | unauthenticated | denied | notFound | methodNotAllowed
  | conflict | contentTooLarge | tooManyRequests
  | unavailable | insufficientStorage
  deriving DecidableEq, Repr

def Status.all : List Status :=
  [.ok, .created, .noContent, .badRequest, .unauthenticated, .denied,
   .notFound, .methodNotAllowed, .conflict, .contentTooLarge,
   .tooManyRequests, .unavailable, .insufficientStorage]

theorem Status.all_complete (s : Status) : s ∈ all := by cases s <;> decide

def Status.code : Status → Nat
  | .ok => 200
  | .created => 201
  | .noContent => 204
  | .badRequest => 400
  | .unauthenticated => 401
  | .denied => 403
  | .notFound => 404
  | .methodNotAllowed => 405
  | .conflict => 409
  | .contentTooLarge => 413
  | .tooManyRequests => 429
  | .unavailable => 503
  | .insufficientStorage => 507

/-- §1 — the redirect class, as declared data. Its members are EVENTS,
never table rows: the HTTP shell follows no redirect, and redirects are
semantic-core decisions. -/
def redirectClass : Nat × Nat := (300, 399)

/-- One status row: the code, the condition that produces it, and what
the client's exchange alphabet makes of it. -/
structure StatusRow where
  status : Status
  condition : String
  meaning : String
  cite : String
  deriving Repr

/-- THE status table. -/
def statusTable : List StatusRow := [
  { status := .ok, condition := "a data answer, or an accepted upload the server already held",
    meaning := "the body is the answer, framed by its declared length", cite := "§3, §5, §6" },
  { status := .created, condition := "an upload the server admitted now",
    meaning := "acknowledgment; the body is closed empty", cite := "§3" },
  { status := .noContent, condition := "an acknowledgment, or a published root read back",
    meaning := "acknowledgment; terminates at its header section", cite := "§3, §7" },
  { status := .badRequest, condition := "a malformed body, an absent or foreign profile header, an unclaimed path, a wrong media type",
    meaning := "a protocol violation; the exchange alphabet's truncation, never an invented event", cite := "§1, §14" },
  { status := .unauthenticated, condition := "no acceptable credential for this authority",
    meaning := "terminal for its operation; there is no challenge negotiation at /0", cite := "§9" },
  { status := .denied, condition := "an authenticated principal without authority for this operation class",
    meaning := "denied; root updates authorize independently of object upload", cite := "§9" },
  { status := .notFound, condition := "content absent from the data plane, or a root not published here",
    meaning := "content-not-found; root presence is registry fact only", cite := "§3, §7" },
  { status := .methodNotAllowed, condition := "a method the claimed resource does not serve",
    meaning := "a protocol violation, never a host 404", cite := "§14" },
  { status := .conflict, condition := "a server-side integrity mismatch, or a declared closure the server verified and found wanting",
    meaning := "the typed upload or publish failure", cite := "§3, §7" },
  { status := .contentTooLarge, condition := "a batch or node body past the server's published budget",
    meaning := "capacity; the client's own budget refusal fires before issue", cite := "§6" },
  { status := .tooManyRequests, condition := "rate limited",
    meaning := "rate-limit event, carrying a delay only when retry-after is a non-negative integer count of seconds", cite := "§1" },
  { status := .unavailable, condition := "the server cannot answer now",
    meaning := "capacity", cite := "§1" },
  { status := .insufficientStorage, condition := "the server cannot store more",
    meaning := "capacity", cite := "§1" }]

/-- The codes are distinct, so a code decides its row. -/
theorem Status.codes_nodup : (Status.all.map Status.code).Nodup := by decide

/-- The table covers the alphabet exactly, in order. -/
theorem statusTable_covers :
    statusTable.map StatusRow.status = Status.all := by decide

/-- No row claims a 3xx. §1 makes every `3xx` a redirect EVENT that the
shell never follows, so a redirect can never be a status the table
resolves — stated rather than left to the reader. -/
theorem Status.codes_avoid_redirect :
    Status.all.all fun s =>
      !(decide (redirectClass.1 ≤ s.code) && decide (s.code ≤ redirectClass.2)) := by
  decide

/-! ### The six resources -/

/-- One row of the path grammar: an operation, its method and path
template, the bodies it carries in each direction, the statuses that
accept it and the statuses the profile names as its refusals, and the
section that says so. -/
structure Resource where
  name : String
  method : Method
  space : Space
  path : Path
  request : Body
  response : Body
  success : List Status
  refusal : List Status
  cite : String
  deriving Repr

/-- THE path grammar: every exchange the profile declares. -/
def resources : List Resource := [
  { name := "loadNode", method := .get, space := .cas,
    path := [.lit "cas", .addr],
    request := .empty, response := .nodeBytes,
    success := [.ok], refusal := [.notFound],
    cite := "§3" },
  { name := "uploadNode", method := .put, space := .cas,
    path := [.lit "cas", .addr],
    request := .nodeBytes, response := .empty,
    success := [.ok, .created, .noContent],
    refusal := [.conflict, .contentTooLarge],
    cite := "§3" },
  { name := "readCapabilities", method := .get, space := .control,
    path := [.lit "control", .lit "capabilities"],
    request := .empty, response := .capability,
    success := [.ok], refusal := [],
    cite := "§5" },
  { name := "findMissing", method := .post, space := .control,
    path := [.lit "control", .lit "missing"],
    request := .keyList, response := .presence,
    success := [.ok], refusal := [.contentTooLarge],
    cite := "§6" },
  { name := "publishRoot", method := .put, space := .roots,
    path := [.lit "roots", .addr],
    request := .keyList, response := .empty,
    success := [.ok, .created, .noContent],
    refusal := [.conflict],
    cite := "§7" },
  { name := "readRoot", method := .get, space := .roots,
    path := [.lit "roots", .addr],
    request := .empty, response := .empty,
    success := [.noContent], refusal := [.notFound],
    cite := "§7" }]

theorem resources_names_nodup : (resources.map Resource.name).Nodup := by
  decide

/-- Method and path together decide at most one resource: the routing
the profile declares is a function, not a search. -/
theorem resources_routes_nodup :
    (resources.map fun r => (r.method, r.path)).Nodup := by decide

/-- The distinct path templates, deduplicated across the methods that
share one — `/cas/<64hex>` is served by two, `/roots/<64hex>` by two. -/
def resourcePaths : List Path := (resources.map Resource.path).eraseDups

/-- Path-prefix distinctness, the routing law: of any two declared
paths, either they are the same path or neither is a prefix of the
other. So a path either IS a declared resource or is not one, and
routing needs no longest-match rule — which is what lets §14 say the
status table answers every unclaimed exchange. -/
theorem resourcePaths_prefix_free :
    resourcePaths.all fun p => resourcePaths.all fun q =>
      decide (p = q) || !p.isPrefixOf q := by decide

/-- Every resource lives in its own space: the path's head segment is
the segment its space reserves. This is what makes §14's reservation
enforceable — a path that does not start in a reserved space is not the
profile's. -/
theorem resources_head_is_space :
    resources.all fun r => decide (r.path.head? = some (.lit r.space.segment)) := by
  decide

/-- A resource carries the address position exactly when its space is
address-addressed. -/
theorem resources_addressing :
    resources.all fun r => decide (Segment.addr ∈ r.path) == r.space.addressed := by
  decide

/-- A status is never both an acceptance and a refusal of the same
resource. -/
theorem resources_success_refusal_disjoint :
    resources.all fun r => r.success.all fun s => decide (s ∉ r.refusal) := by
  decide

/-! ## §14 — co-tenancy on one authority

A host MAY serve other prefixes on the same authority. Such a prefix is
a CO-TENANT: outside the profile's media-type and status law, and a
client MUST NOT read its answers through the exchange alphabet. The
profile's own status table answers every UNCLAIMED exchange on the
authority — every path a co-tenant prefix does not claim, including
unknown paths and wrong methods — and does not answer exchanges inside
a declared co-tenant prefix. -/

/-- One declared co-tenant: its prefix, what serves it, and which of
the profile's laws do not reach it. -/
structure CoTenant where
  prefixPath : Path
  tenant : String
  ungoverned : String
  deriving Repr

/-- §14's table, as `cas daemon` declares it. -/
def coTenants : List CoTenant := [
  { prefixPath := [.lit "mcp"],
    tenant := "MCP over HTTP (Streamable HTTP, POST-only)",
    ungoverned := "media type (JSON), status table (405 on the wrong method is the adapter's)" },
  { prefixPath := [.lit "metrics"],
    tenant := "Prometheus exposition",
    ungoverned := "media type (text), status table" },
  { prefixPath := [.lit "projections"],
    tenant := "the emitted byte-gated JSON artifacts, read-only",
    ungoverned := "media type (JSON), status table (404 is \"not emitted\", not an exchange event)" }]

theorem coTenants_prefixes_nodup :
    (coTenants.map CoTenant.prefixPath).Nodup := by decide

/-- §14's reservation, decided: no co-tenant prefix shadows a reserved
space and no reserved space shadows a co-tenant. Prefix-freedom in both
directions is what licenses the clause's closing inference — a client
that meets an unexpected media type or status on a path it believes is
a profile resource has found a server defect, not a co-tenant. -/
theorem coTenants_prefix_free :
    reservedPaths.all fun p => coTenants.all fun t =>
      !p.isPrefixOf t.prefixPath && !t.prefixPath.isPrefixOf p := by
  decide

/-- And no co-tenant prefix claims a declared resource. -/
theorem coTenants_claim_no_resource :
    coTenants.all fun t => resources.all fun r =>
      !t.prefixPath.isPrefixOf r.path := by decide

/-! ## §4 — the canonical key-list document

The shared framing for key collections: a 4-byte big-endian count N
followed by exactly N×32-byte addresses. Total length exactly
4 + 32·N, no trailing content, decode fail-closed; a successful
decode's input is exactly the canonical encoding of its result. Order
is significant and preserved. -/

/-- §4 — the width of the leading big-endian count. -/
def keyListCountBytes : Nat := 4

/-- §4 — the total wire length of a key-list document of N keys. -/
def keyListBytes (n : Nat) : Nat := keyListCountBytes + addressBytes * n

/-- A leaf root publishes a count-0 document, which is the header
alone (§7). -/
theorem keyListBytes_empty : keyListBytes 0 = keyListCountBytes := by decide

theorem keyListBytes_one : keyListBytes 1 = 36 := by decide

/-- The framing determines the count: two key counts with the same wire
length are the same count. This is the structural half of "no trailing
content" — a document's length already says how many keys it carries,
so a decoder that checks the length is not guessing. -/
theorem keyListBytes_inj {m n : Nat} (h : keyListBytes m = keyListBytes n) :
    m = n := by
  simp only [keyListBytes, keyListCountBytes, addressBytes] at h
  omega

/-! ## §5 — the capability envelope

`GET {authority}/control/capabilities` answers `200` with a body of
exactly the eight canonical bytes: big-endian u32 `maxBatchKeys`, then
big-endian u32 `maxBlobBytes`. The second field's WIRE meaning is the
maximum canonical NODE body accepted by `/0` — the name predates the
blob abstraction, and the field renames to `maxNodeBytes` at `/1`. Any
other length or a non-canonical body is a typed protocol violation. -/

/-- One fixed-width big-endian field of a declared envelope. -/
structure Field where
  name : String
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- §5 — the envelope's declared total size. -/
def capabilityEnvelopeBytes : Nat := 8

/-- §5 — the envelope's fields, in wire order. Big-endian throughout;
the names are the `/0` WIRE names, not the `/1` ones. -/
def capabilityFields : List Field := [
  { name := "maxBatchKeys", offset := 0, width := 4 },
  { name := "maxBlobBytes", offset := 4, width := 4 }]

/-- The offsets a contiguous layout from a given start forces. -/
def contiguousOffsets (start : Nat) : List Field → List Nat
  | [] => []
  | f :: fs => start :: contiguousOffsets (start + f.width) fs

theorem capabilityFields_names_nodup :
    (capabilityFields.map Field.name).Nodup := by decide

/-- The declared widths fill the declared size exactly: no padding, no
slack, which is what makes "any other length is a violation"
checkable. -/
theorem capabilityFields_fill :
    (capabilityFields.map Field.width).sum = capabilityEnvelopeBytes := by
  decide

/-- The declared offsets are the contiguous ones from zero: the fields
neither overlap nor leave a hole. -/
theorem capabilityFields_contiguous :
    contiguousOffsets 0 capabilityFields = capabilityFields.map Field.offset := by
  decide

/-- Every field is a big-endian u32 — the profile's only scalar width
here, and the same width §4's count carries. -/
theorem capabilityFields_u32 :
    capabilityFields.all fun f => decide (f.width = keyListCountBytes) := by
  decide

/-! ## §6 — the presence alphabet

`POST {authority}/control/missing` answers `200` with a body of exactly
N status bytes, positionally aligned to the request order. Any other
length or byte value is malformed and resolves as the typed batch
failure. Presence answers are planning data only: they steer upload
scheduling, admit nothing, and are never negatively cached. -/

inductive Presence where
  | missing | present | failed
  deriving DecidableEq, Repr

def Presence.all : List Presence := [.missing, .present, .failed]

theorem Presence.all_complete (p : Presence) : p ∈ all := by cases p <;> decide

/-- §6 — the status byte for each answer. -/
def Presence.byte : Presence → UInt8
  | .missing => 0
  | .present => 1
  | .failed => 2

/-- The partial inverse: the alphabet is CLOSED, so every other byte is
malformed rather than reserved. -/
def Presence.ofByte : UInt8 → Option Presence
  | 0 => some .missing
  | 1 => some .present
  | 2 => some .failed
  | _ => none

theorem Presence.ofByte_byte (p : Presence) : Presence.ofByte p.byte = some p := by
  cases p <;> rfl

theorem Presence.bytes_nodup : (Presence.all.map Presence.byte).Nodup := by
  decide

/-- The alphabet occupies the bottom of the byte plane and nothing
else. -/
theorem Presence.byte_lt_three (p : Presence) : p.byte < 3 := by
  cases p <;> decide

/-! ## §12 — blob representation

A blob is a NODE GRAPH under the ordinary data plane — no new endpoints
and no second identity. Four node shapes, version byte 0; all scalar
fields big-endian. The blob's identity is the manifest node's ordinary
content identifier. -/

/-- One of §12's four node shapes. -/
structure BlobShape where
  name : String
  tag : UInt8
  payload : String
  refs : String
  deriving Repr

/-- §12's table, verbatim. -/
def blobShapes : List BlobShape := [
  { name := "chunk data", tag := 8,
    payload := "the raw chunk bytes", refs := "none" },
  { name := "tree leaf", tag := 9,
    payload := "u32 index ++ u32 chunk length", refs := "one, expected tag 8" },
  { name := "tree parent", tag := 9,
    payload := "empty", refs := "two (left, right), expected tag 9" },
  { name := "manifest", tag := 10,
    payload := "u32 recipe id ++ u64 total bytes ++ u32 leaf count",
    refs := "one (tree root), expected tag 9" }]

/-- The profile's blob kinds ARE the grammar's sorts. `Cas/Grammar/Sorts.lean`
already cites this profile for tags 8, 9 and 10; this is the citation
discharged, so the two tables cannot drift apart silently. -/
theorem blobShapes_tags_are_sorts :
    Cas.Grammar.Ty.chunk.wireTag = 8
      ∧ Cas.Grammar.Ty.tree.wireTag = 9
      ∧ Cas.Grammar.Ty.manifest.wireTag = 10 := by decide

/-- And the version byte §12 declares is the grammar's scheme
version. -/
theorem blobShapes_version : Cas.Grammar.schemeVersion = 0 := rfl

/-- Leaf and parent SHARE tag 9, so the tag column is deliberately not
`Nodup` — exhibited rather than left implicit. References type-check at
tag granularity, which is why one sort carries both tree shapes; a
future revision that split them would have to change the grammar, not
just this table. -/
theorem blobShapes_tags_not_nodup :
    ¬ (blobShapes.map BlobShape.tag).Nodup := by decide

/-- §12 — the fixed chunk size of the shipping recipe. A PROFILE
constant, never a server capability: a capability-derived chunk size
would fragment content identity across authorities. -/
def chunkBytes : Nat := 65536

/-- §12 — the recipe registry. An unknown recipe identifier is
rejected, never guessed. -/
def recipes : List (Nat × String) := [
  (0, "inline-leaf — model substrate; no client implements it"),
  (1, "referenced-chunk — fixed-size chunking at 65536 bytes, empty input is one empty chunk, the tree splits at the largest power of two strictly below the leaf count")]

theorem recipes_ids_nodup : (recipes.map Prod.fst).Nodup := by decide

end Cas.Backend.HttpProfile
