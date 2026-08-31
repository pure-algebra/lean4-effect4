import Cas.Schema.Notation
import Cas.Schema.Projection
-- The scheme VERSION byte a node carries is the grammar's ratified
-- constant, not a second spelling of `0` — `Cas/Grammar/Sorts.lean` is
-- a leaf over `Cas.Core.Node`, so citing it here costs one edge and
-- keeps the byte owned in one place.
import Cas.Grammar.Sorts

/-!
# The system kind — a service topology as content

A composition of services is a DESCRIBED VALUE, exactly like an
exchange or an annotation: it rides the same admission law, addresses
its children rather than inlining them, and reaches TypeScript through
the ordinary emitter path. Nothing here is new theory and nothing here
is a new sort — `Cas/Schema/Exchange.lean` is the worked precedent and
this module is its shape a second time.

One system node is one WIRING STEP:

- `service` / `backing` — a leaf: a reference to written code that
  builds a layer, beside the service keys that layer answers with and
  the keys it still demands. `service` answers exactly one key;
  `backing` answers a whole context of them (a backend's seams).
- `provide` / `provideMerge` — an edge: the `inner` layer satisfies the
  `outer` layer's demands. `provide` keeps only the outer's keys;
  `provideMerge` keeps both sides'.
- `merge` — several layers set side by side, demanding nothing of each
  other.
- `fresh` — the same topology, built again rather than shared. It is
  the ONLY spelling of the sharing distinction, and it is spelled here
  because a description addresses its children by digest: what an
  author wrote twice under two `const`s the fold writes once, so a
  topology that wants two instances has to say so.

## Which keying regime this kind sits in

Effect keys three things three ways, and the difference is the whole
of the sharing question. A `Layer` is memoized by OBJECT REFERENCE:
`MemoMapImpl` (Effect v4 `Layer.ts`) holds a plain `Map` and looks a
layer up with `this.map.get(layer)`, so sharing is a property of where
the author put a `const`. A `Cache` is keyed STRUCTURALLY, by
`Equal`/`Hash`. A `PersistedCache` is keyed by a `PrimaryKey` string
derived from a schema-described request, with the result stored as a
serialized `Exit` (`Persistable.serializeExit` / `deserializeExit` over
`exitSchema`) in a store shared across fibers, restarts and workers.

The third regime is content-derived key plus serialized result plus a
shared store — this estate's own semantics, already inside Effect. A
`SystemNode` addresses its children by digest, so it is extensional in
the same way, and that is the seam it aligns with. The divergence it
does NOT resolve is against the FIRST regime: a description cannot see
where a `const` was written, so what Effect builds twice a fold builds
once unless `fresh` says otherwise.

Two facts about that first regime, read off the v4 source rather than
assumed, because both cut against the naive picture:

- `Layer.fresh self` builds `self` against `makeMemoMapUnsafe()` — a
  brand-new ROOT map. Freshness is therefore a property of the MemoMap,
  not of the layer value, which is exactly why a DESCRIPTION can carry
  it as an arm at all.
- `Layer.build` forks the current map (`CurrentMemoMap.forkOrCreate`)
  and `MemoMapImpl.get` reads through to `this.parent`, so v4 shares
  across nested provides where v3 did not. The gap between the two
  regimes is therefore narrower in v4 than the hazard first suggests —
  and still not closed, which is why this lane generates and never
  recovers.

Named, not built here: `Persistable` is the designated key discipline
for STORED REQUESTS, the layer-side counterpart of what this kind does
for stored wiring. Attaching it is a follow-on with its own consumer;
this module only records where it belongs.

## The address certifies the wiring

A system node's children are `StoreRef`s, so a topology is a Merkle
DAG whose root address is computed from its children's addresses and
nothing else. The address IS the certificate: anyone holding the bytes
can recompute it, and no separate signing plane is wanted or added.

One boundary to state rather than discover. The address is a function
of the WRITTEN TERM, list order included — `provides` and `requires`
are ordered content under the canonical rendering, as every array in
this store is. `EmitLayer`'s residual fold deduplicates and sorts by
key, so two spellings of one service SET emit the same TypeScript and
answer the same Context; they do not reside at the same address.

**CANON-1, ruled: canonicalize at the AUTHORING door, never here.** The
reason is the cache, not tidiness — a plan keyed by address misses on a
term meaning exactly what the hit meant — so the fix belongs where the
term is written, not where it is read. `tools/EmitLayers.lean` spells
every service list in `Cas.Backend.canonServices` order and `#guard`s
that it did, so the term this estate STORES is the canonical one and
equal service sets reside at equal addresses. The carrier stays
untouched: this kind still means the term it was given, and a
`normalize` on the load path would be renormalize-on-read, which is a
named defect (`Cas/Core/Canonicalize.lean:40-42`). The guard's scope is
the authored topology, not every `SystemNode` a caller can build; what
closing the door at the constructor would cost is written out at the
CANON-1 section of `tools/EmitLayers.lean`.

## How this kind grows

By an ARM, on the Exchange precedent — never by a sibling carrier and
never by a `Ty` row. The first candidate already named is a described
BUILD STEP: a recipe is a record of command, arguments, environment,
working directory and output paths (Effect v4's `StandardCommand` in
`unstable/process` has that exact shape), and whether it belongs here
as an arm or beside this kind as its own signature is a question the
shape of this module is meant to answer. Nothing is reserved for it.
- `opaque` — the escape. A leaf whose construction this grammar does
  not hold (a body that branches on a host value, reads the
  environment, or reaches for a platform API), carried as a reference
  plus a stated reason. It contributes IDENTITY, never structure.

## What an author writes, and what is derived

An author writes the topology and nothing else: service keys as
strings — exactly `Context.Key.key`, the same word the runtime
compares — ADDRESSED references to code that is already written, and
the wiring edges between them. Constructor BODIES are never authored
here; they are `CodeRef`s to written code, which is the R7 line
(`EFFECTS-BACKEND.md:112-119`: the backend generates layers, host
machinery, not programs). Everything else — the emitted expression,
the declared `Layer.Layer<…>` type, the import list, the residual
demands — is computed from the description by
`Cas/Backend/EmitLayer.lean`.

## Why the children are addresses

`inner`, `outer` and `parts` are `StoreRef systemKindTag`: a system
node references other system nodes BY STORE ADDRESS, never by
containment. This is `ExchangeSubject`'s move (`Exchange.lean:77-79`)
and it buys the same thing — the carrier is not recursive, so no
fixpoint is needed on the schema plane, and acyclicity is free because
an address can only name content that already exists.

## The kind tag is a WORKING tag, not plane identity

`systemKindTag` is `0x54`, chosen here so the recursive arms have a tag
to demand and a topology can be built at all. It is NOT registered as a
reserved tag and this module mints NO registry row: exactly as with the
exchange and sidecar-annotation kinds, minting plane identity is a
separate ruling and wants Lean and TypeScript counterparts together.
Until that ruling, `0x54` is the tag this kind's callers reside at, and
`Cas.value` accepts it because it is unreserved.

Like `Cas.Schema.Exchange`, this module keeps compiler metaprogramming
an opt-in import — the emitter and the mirrors import it; the runtime
facade does not.
-/

namespace Cas.Schema

open Cas.Schema.Notation

/-- The kind tag system nodes reside at. A WORKING tag, not a minted
plane identity: see the reserved-tag note above. -/
def systemKindTag : UInt8 := 0x54

/-- The tag file nodes reside at (`0x0B`), read off the grammar's own
sort table rather than spelled a second time here. -/
def fileKindTag : UInt8 := Cas.Grammar.Ty.file.wireTag

#guard fileKindTag == 0x0B

/-- A reference to WRITTEN CODE: the FILE it is exported from, as an
address, and the name it is exported as. A dotted `export` names a
static member (`AddressScheme.layerSha256`); the import list is derived
from its first segment.

`file` was `path : String` — a module specifier carried as text, which
is out-of-band by exactly the mechanism the annotation kind's old
`value : String` was. Written code already has a content seat
(`file` 0x0B over `manifest` 0x0A over `chunk` 0x08 puts a named file
with a media type); what had no seat was the NAMED EXPORT WITHIN A
MODULE, and that is this struct rather than a new plane. The topology's
edge to written code is now an address the store walks, counts in
`refCount`, and refuses at the wrong kind.

What the emitter must now do, and this is the honest cost: a module
SPECIFIER is no longer readable off the term. `EmitLayer` recovers it
from the file node's `name`, which means emission takes a resolution
table beside its bindings — the same children-first discipline the
residual fold already runs on. See `Cas/Backend/EmitLayer.lean`.

Promoting this struct moves every stored `SystemNode` address, because
the payload changed. That is the one cost in this ruling that IS an
address-moving event for content, and `BUILD-MODELING-AUDIT.md:124`
§D.2 is why it was paid now: today the stored topologies are the
authored DAG in `tools/EmitLayers.lean` and nothing else. It will never
be cheaper. -/
cas_struct CodeRef where
  «export» : String
  file : StoreRef fileKindTag

/-- A service as the topology names it: the runtime key the context is
compared on (exactly `Context.Key.key`), and the reference to the tag
that carries it — whose name is also the TypeScript TYPE the declared
layer type is written in. -/
cas_struct ServiceRef where
  key : String
  name : String
  path : String

/-- One wiring step. Children are addressed, never contained. -/
cas_union SystemNode where
  | backing (ctor : CodeRef) (provides : List ServiceRef)
      (requires : List ServiceRef)
  | fresh (inner : StoreRef systemKindTag)
  | merge (parts : List (StoreRef systemKindTag))
  | «opaque» (ctor : CodeRef) (note : String) (provides : List ServiceRef)
      (requires : List ServiceRef)
  | provide (inner : StoreRef systemKindTag) (outer : StoreRef systemKindTag)
  | provideMerge (inner : StoreRef systemKindTag)
      (outer : StoreRef systemKindTag)
  | service (ctor : CodeRef) (provides : ServiceRef)
      (requires : List ServiceRef)

-- The generator's discrimination claim, checked at elaboration. The
-- `opaque` arm is French-quoted because `opaque` is a Lean keyword; the
-- WIRE tag it carries is the plain word, which is what the ratified
-- arm list names.
#guard SystemNode.schemaCode.discriminated

/-! ## Put from Lean — the projection bridge, at this kind

The same pin discipline `Exchange.lean:88-133` established, at the same
bridge (`Projection.putNode`, kind tag `0x54`, revision 1): the payload
text, the reference array, and the node's own three observable fields.

One honest difference from that precedent, stated rather than left to
be discovered: the exchange pins compare against a string the effects
suite records for the same value, so their payload half is a
CROSS-RUNTIME pin. There is no TypeScript mirror of `SystemNode` — this
slice generates layers, it does not ingest them — so these pins are
single-register: they hold the Lean projection still, and nothing more.
The cross-runtime obligation belongs with the mirror, whenever a
consumer asks for one. -/

/-- The pin's child address. Its bytes reach the reference array and
never the payload, which is why the payload pins below are literals
rather than computations over this value. -/
def pinChild : Addr32 := ⟨List.replicate 32 0xab, by simp⟩

/-- The pin's file address — the node the constructor is exported from,
at the file kind. -/
def pinFile : Addr32 := ⟨List.replicate 32 0xcd, by simp⟩

/-- A leaf: one written constructor, one service key, one demand. -/
def pinService : SystemNode :=
  .service
    { «export» := "AddressScheme.layerSha256", file := ⟨pinFile⟩ }
    { key := "foldlab/cas/AddressScheme", name := "AddressScheme"
    , path := "../../src/cas/Store.ts" }
    [{ key := "effect/Crypto", name := "Crypto.Crypto", path := "effect" }]

/-- An edge: two addressed children, both at the system kind. -/
def pinEdge : SystemNode := .provideMerge ⟨pinChild⟩ ⟨pinChild⟩

-- A leaf is no longer reference-free: its constructor's FILE is an
-- address now, so the leaf carries exactly one typed edge at the file
-- kind and the module specifier has left the payload.
#guard putPayload 1 pinService == some
  "{\"revision\":1,\"value\":{\"_tag\":\"service\",\"ctor\":{\"export\":\"AddressScheme.layerSha256\",\"file\":{\"$ref\":0}},\"provides\":{\"key\":\"foldlab/cas/AddressScheme\",\"name\":\"AddressScheme\",\"path\":\"../../src/cas/Store.ts\"},\"requires\":[{\"key\":\"effect/Crypto\",\"name\":\"Crypto.Crypto\",\"path\":\"effect\"}]}}"

#guard putRefs 1 pinService == some [⟨fileKindTag, pinFile⟩]

-- An edge's addresses never reach the payload: each lowers to the
-- positional marker and rides the node's reference array instead.
#guard putPayload 1 pinEdge == some
  "{\"revision\":1,\"value\":{\"_tag\":\"provideMerge\",\"inner\":{\"$ref\":0},\"outer\":{\"$ref\":1}}}"

#guard putRefs 1 pinEdge == some
  [⟨systemKindTag, pinChild⟩, ⟨systemKindTag, pinChild⟩]

-- The node itself: the system kind tag, those two edges, and the
-- payload's UTF-8 bytes.
#guard (putNode Cas.Grammar.schemeVersion systemKindTag 1 pinEdge).map
    (fun n => (n.version, n.tag, n.refs))
  == some (Cas.Grammar.schemeVersion, systemKindTag,
      [⟨systemKindTag, pinChild⟩, ⟨systemKindTag, pinChild⟩])

end Cas.Schema
