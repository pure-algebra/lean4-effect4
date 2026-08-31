import Cas.Schema.Notation
import Cas.Schema.Projection
import Cas.Schema.Exchange
import Cas.Schema.System
-- The program and git planes own their tags in the grammar's sort
-- table, not here: `Cas/Grammar/Sorts.lean` is where `cont` (0x0F) and
-- `git` (0x47) are ratified, and the arms below read them off it so the
-- byte is spelled once in the estate.
import Cas.Grammar.Sorts

/-!
# The sidecar annotation kind (stipulation S2)

Annotation content is STORE CONTENT. The carrier `Ast` gains no
annotation field — that would ripple every codec, canonicality, and
round-trip proof in the plane for data the kernel never inspects — so
an annotation is its own described kind whose SUBJECT is a typed store
reference. The DAG carries as many of them as wanted: "twenty encoded
other schemas" is twenty annotation nodes, or twenty addresses carried
in their values.

One annotation node says one thing about one addressed value:

- `subject` — the value being annotated, addressed, never inlined.
  Stipulation S4 holds by construction here: the edge references the
  subject AS its own kind, not as a concrete instance of something
  else.
- `key` — the `foldlab/...` annotation key this node carries. String
  keys only: symbol-keyed annotations are dropped at persistence and
  code generation on the Effect side, so the persistent namespace is
  the slash namespace and nothing else.
- `value` — what the annotation says, as ALTERNATIVES: a `text` arm for
  a scalar, and a `ref` arm carrying a typed reference to whatever the
  annotation points at.

## Why the subject is a union (the convergent naming ruling)

`subject` was `StoreRef schemaKindTag` — a schema node and nothing
else. That pinned the kind to one plane, and three separate defects
were the same fact seen from three sides: a view's link to the value it
projects, a program's human-facing name, and a topology's link to the
written code that builds it were all unspellable or degraded to text.
`AnnotationSubject` is the widening `Exchange.lean:77-79` already
established the pattern for — one arm per addressable plane the estate
HAS TODAY, each arm a `StoreRef` at that plane's tag, because a
reference demands one tag and "what this annotation is about" is
genuinely alternatives.

Thirteen arms, in three groups. The META and AGENT planes, which the
convergent naming ruling admitted:

- `exchange` (`0x58`) — a recorded turn of the agent seam;
- `git` (`0x47`) — a git object as content;
- `program` (`0x0F`) — a `cont` node, the only spelling in which a
  program is content;
- `schema` (`0x53`) — the plane the kind was born pinned to;
- `system` (`0x54`) — a service topology.

The CONTENT planes, admitted 2026-08-30 as rider CA-1 of decision 40's
sort batch — the widening the search layout named, because until it
landed the union stopped at the meta planes and an annotation about
STORED CONTENT was not nameable at all:

- `value` (`0x01`) — an opaque value payload;
- `chunk` (`0x08`) — position-free chunk bytes, which is where an
  embedding's vector lives;
- `file` (`0x0B`) — a named file over a blob manifest;
- `context` (`0x0D`) — a folded context.

And the four sorts decision 40 ratified in the same event, which is
what makes the reflexive rung — a note about a note — spellable at all:

- `annotation` (`0x41`) — this very kind, at the row it was promoted
  to;
- `agent` (`0x49`) — the attribution anchor;
- `query` (`0x51`) — a spec as content;
- `result` (`0x52`) — a materialized answer.

`text` has NO arm, and that is a refusal rather than an omission: the
CRDT run was refused from the batch on vision grounds, so there is no
tag to demand and an arm would invent one.

Nothing is reserved for a plane that does not exist yet: growth is by
an arm, and an arm is arm-additive.

Note what the union does NOT span, and why that is not an oversight:
`tree` (`0x09`), `manifest` (`0x0A`), `entry` (`0x0C`) and `step`
(`0x0E`) are the INTERIOR of composites — a blob's shape, a journal's
link, a program's line. Nothing in the estate asks to say something
about one of those in isolation; the thing a person names is the
`file`, the `cont`, the `value`. An arm for each is one ruling away and
costs another versioning event, which is exactly the price this module
already documents.

## Why the value is a union too

`value : String` degraded a store-content link to text — the module's
own former docstring said "a content address in hex when the value is
itself store content", which is precisely the out-of-band config a
content-addressed estate exists to eliminate. A hex string does not
appear in `refCount`, `Graph.verify` does not walk it, and
`WrongKindReference` can never fire on it.

`AnnotationValue` fixes that with two arms, and the `ref` arm carries
an `AnnotationSubject` rather than a bare `StoreRef`:

- a `StoreRef` demands ONE tag, so a single generic `ref` arm cannot be
  spelled at all — the tag would have to be invented;
- one arm per plane, flattened into this union, would spell the plane
  list twice and let the two copies drift;
- nesting the subject union keeps admission CHECKABLE, which is the
  property the ruling asks for: every arm still names its expected tag,
  the reference lowers to a positional marker and rides the node's
  reference array, and the store's admission law refuses an edge whose
  target is of another kind. `WrongKindReference` fires on an annotation
  value now, which it never could before.

The two unions are the same list because they answer the same question
— "which addressable plane" — and one list is one place to grow.

## The versioning event

Arms are canonically ordered by the deriving handler (members sorted by
tag) and decision 4 rules ORDER IS IDENTITY, so this growth moves the
annotation SCHEMA CODE's address. `BUILD-MODELING-AUDIT.md:124` §D.2
prices exactly this: union growth is arm-additive and does not move
STORED NODE addresses; it does move the schema code's address, and that
is "a documented versioning event, not an address-moving event for
content." The receipts are `schemas/annotation.json` and the
`annotation` row of `schemas/addresses.json`, both regenerated by
`lake exe schemas` and byte-gated. No annotation node that was ever
stored changes address; every annotation node authored against the old
shape has to be re-authored, and there are none.

That price was paid a second time on 2026-08-30, for CA-1's eight arms,
and the reason it was payable is the same reason: there are still no
stored annotation nodes to re-author. What the batch deliberately did
NOT move is the TAG. Decision 40 promoted `0x41` — the working tag this
module's pins were already riding — to a ratified registry row rather
than assigning the sort a fresh byte, so every annotation node the
estate has ever written keeps its address. The tag is read off the sort
table now (`pinAnnotationKindTag` below), which is what makes the
promotion a fact of the build rather than a claim: the byte is spelled
once in the estate, in `Cas/Grammar/Sorts.lean`, exactly as `cont`'s
and `git`'s are.

At projection time the materializer folds sidecar annotations into the
representation-level annotation bags where Effect persists them. The
carrier stays small and fully proved; the annotation surface stays open
by design.

Like `Cas.Schema.Notation`, this module keeps compiler metaprogramming
an opt-in import — the schema emitter and the mirrors import it; the
runtime facade does not.
-/

namespace Cas.Schema

open Cas.Schema.Notation

/-- The tag `cont` nodes reside at, read off the grammar's sort table.
A published program is a `cont` node at an address (R7), which is what
makes `foldlab/name` on a program spellable. -/
def programKindTag : UInt8 := Cas.Grammar.Ty.cont.wireTag

/-- The tag git objects reside at, read off the grammar's sort table. -/
def gitKindTag : UInt8 := Cas.Grammar.Ty.git.wireTag

/-- The tag an opaque value payload resides at. -/
def valueKindTag : UInt8 := Cas.Grammar.Ty.value.wireTag

/-- The tag position-free chunk bytes reside at — where an embedding's
vector lives, which is why the embedding key points HERE and takes the
embedded content as its subject. -/
def chunkKindTag : UInt8 := Cas.Grammar.Ty.chunk.wireTag

/-- The tag a folded context resides at. -/
def contextKindTag : UInt8 := Cas.Grammar.Ty.context.wireTag

/-- The tag annotation nodes themselves reside at — the reflexive arm's
target, and this kind's own row since decision 40. -/
def annotationKindTag : UInt8 := Cas.Grammar.Ty.annotation.wireTag

/-- The tag agent steps reside at (decision 40): the attribution
anchor, off `entry`'s tag and onto its own. -/
def agentKindTag : UInt8 := Cas.Grammar.Ty.agent.wireTag

/-- The tag a query spec resides at (decision 40). -/
def queryKindTag : UInt8 := Cas.Grammar.Ty.query.wireTag

/-- The tag a materialized answer resides at (decision 40). -/
def resultKindTag : UInt8 := Cas.Grammar.Ty.result.wireTag

-- Every tag above is the grammar's, not a second spelling of a byte.
#guard programKindTag == 0x0F
#guard gitKindTag == 0x47
#guard valueKindTag == 0x01
#guard chunkKindTag == 0x08
#guard contextKindTag == 0x0D
#guard annotationKindTag == 0x41
#guard agentKindTag == 0x49
#guard queryKindTag == 0x51
#guard resultKindTag == 0x52

/-- What one annotation is about, by plane: every addressable plane the
estate has today, each arm a typed reference at that plane's tag.

The arms are written in the deriving handler's own canonical order
(ascending constructor name), so the source reads in the order the
emitted arm table does — but source order is not the code's identity
either way: the handler sorts. -/
cas_union AnnotationSubject where
  | agent (address : StoreRef agentKindTag)
  | annotation (address : StoreRef annotationKindTag)
  | chunk (address : StoreRef chunkKindTag)
  | context (address : StoreRef contextKindTag)
  | exchange (address : StoreRef exchangeKindTag)
  | file (address : StoreRef fileKindTag)
  | git (address : StoreRef gitKindTag)
  | program (address : StoreRef programKindTag)
  | query (address : StoreRef queryKindTag)
  | result (address : StoreRef resultKindTag)
  | schema (address : StoreRef schemaKindTag)
  | system (address : StoreRef systemKindTag)
  | value (address : StoreRef valueKindTag)

-- The generator's discrimination claim, checked at elaboration.
#guard AnnotationSubject.schemaCode.discriminated

/-- What one annotation SAYS: a scalar, or a typed reference to
addressed content. The reference arm reuses `AnnotationSubject` because
the question is the same one — which addressable plane — and one list
is one place to grow. -/
cas_union AnnotationValue where
  | ref (address : AnnotationSubject)
  | text (text : String)

-- The generator's discrimination claim, checked at elaboration.
#guard AnnotationValue.schemaCode.discriminated

/-- One sidecar annotation on one addressed value: the addressed
subject, the `foldlab/...` key it carries, and what it says. -/
cas_struct Annotation where
  key : String
  subject : AnnotationSubject
  value : AnnotationValue

/-! ## Put from Lean — the projection bridge, at this kind

The pin discipline `Exchange.lean:91-133` established, at the kind this
ruling widened: the payload text, the reference array, and the node's
own observable fields. The pins ride `0x41`, which the effects suite
was already putting at (`SchemaAnnotation.test.ts`) and which decision
40 ratified as this kind's registry row — so the byte below is read off
the sort table, not chosen here.

The worked example is the NAME SEAT: `foldlab/name` on a stored
topology through the `system` arm — the thing that was unspellable
before this ruling, spelled. The `foldlab/` key family beside it is
rider CA-2 of the same decision. -/

/-- The pin's subject address. Its bytes reach the reference array and
never the payload, which is why the payload pins below are literals. -/
def pinSubjectAddr : Addr32 := ⟨List.replicate 32 0xab, by simp⟩

/-- The kind tag the pins reside at, read off the grammar's sort table.
It WAS the caller's `0x41`, matching the effects suite's own choice;
decision 40 ratified that byte as the `annotation` row rather than
minting a fresh one, so no stored node moved and the spelling collapsed
into the sort table like every other ratified tag. -/
def pinAnnotationKindTag : UInt8 := annotationKindTag

/-- The revision the pins ride, and the one the CLI's naming seat puts
at. It is a pin like the tag beside it: the projection's revision is
part of the wire, so a consumer that spells it by hand spells it
twice. Emitted with the tag, and read off there. -/
def pinAnnotationRevision : Nat := 1

/-- The everyday word for this kind. It was emitted from here because
the annotation plane had no registry row to give a name; since decision
40 it HAS one, and this def is the spelling the two surfaces have to
agree on. `tools/EmitGrammar.lean` is where they are held to each
other — the registry's `Ty.sortName` lives one module above this one,
so the pin sits where both are in scope, exactly as the `step`/`cont`
witness pins do. Decision 25's rule is unchanged: a rendered kind name
enters the human register off the generated registry, never off a
hand-written table. -/
def pinAnnotationKindWord : String := "annotation"

/-- The name seat, worked: a human-facing name on a stored topology. -/
def pinName : Annotation :=
  { key := "foldlab/name"
  , subject := .system ⟨pinSubjectAddr⟩
  , value := .text "casSystem" }

/-- The view link, worked: an annotation whose value is a typed
reference rather than hex text. -/
def pinLink : Annotation :=
  { key := "foldlab/view"
  , subject := .program ⟨pinSubjectAddr⟩
  , value := .ref (.system ⟨pinSubjectAddr⟩) }

-- One typed edge at the system kind, and the name as text.
#guard putPayload pinAnnotationRevision pinName == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/name\",\"subject\":{\"_tag\":\"system\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"text\",\"text\":\"casSystem\"}}}"

#guard putRefs pinAnnotationRevision pinName == some [⟨systemKindTag, pinSubjectAddr⟩]

-- Two typed edges: the subject at the program kind, and the VALUE's
-- own reference at the system kind. The second edge is what the old
-- `value : String` could not carry — the store now walks it, and
-- `WrongKindReference` can fire on it.
#guard putPayload pinAnnotationRevision pinLink == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/view\",\"subject\":{\"_tag\":\"program\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"ref\",\"address\":{\"_tag\":\"system\",\"address\":{\"$ref\":1}}}}}"

#guard putRefs pinAnnotationRevision pinLink == some
  [⟨programKindTag, pinSubjectAddr⟩, ⟨systemKindTag, pinSubjectAddr⟩]

-- The node itself: the row's tag, the two edges, and the payload.
#guard (putNode Cas.Grammar.schemeVersion pinAnnotationKindTag pinAnnotationRevision pinLink).map
    (fun n => (n.version, n.tag, n.refs))
  == some (Cas.Grammar.schemeVersion, pinAnnotationKindTag,
      [⟨programKindTag, pinSubjectAddr⟩, ⟨systemKindTag, pinSubjectAddr⟩])

/-! ## The `foldlab/` key family (rider CA-2)

Annotation keys are structurally OPEN — the codec reads `key` as a
string and could not care which one — so ratifying a family is not a
narrowing of the carrier. It is the same act `foldlab/name` already
received: a worked pin, so the spelling exists once in the estate, at
byte level, and a consumer reads it rather than agreeing to it.

The five below are the search plane's, named by decision 40 and worked
here on the arms they actually ride, so each pin exhibits a widening
CA-1 paid for as well as a key:

- `foldlab/related` — the association edge, query to query. The
  `pinLink` shape at the search plane's own sorts.
- `foldlab/search-note` — a note about an answer, on the `result` arm.
- `foldlab/pref` — a preference attached to ONE past turn, on the
  `exchange` arm; a preference about "the model in general" has no
  subject and is therefore not sayable here, which is the point.
- `foldlab/embedding` — content to vector: the subject is the content
  and the value is a typed reference to the `chunk` the vector's bytes
  live in. This is why no `vec` sort was minted — nothing references a
  vector by typed edge, so the carrier is chunk bytes plus this key.
- `foldlab/tombstone` — a retraction, worked on the REFLEXIVE arm: a
  tombstone over an annotation. The store is grow-only, so a retraction
  is a further annotation and never a deletion, and the value carries
  the reason as text.

The spellings are `foldlab/`-namespaced because that is the persistent
namespace (symbol keys are dropped at persistence, so the slash
namespace is the whole of it), and lowercase-hyphenated because
`foldlab/name` and `foldlab/view` already are. `search-note` is the one
spelling with a compound; the alternative `note` was refused as too
broad for a key that means "a note made during a search". -/

/-- The association edge, worked: one query related to another. -/
def pinRelated : Annotation :=
  { key := "foldlab/related"
  , subject := .query ⟨pinSubjectAddr⟩
  , value := .ref (.query ⟨pinSubjectAddr⟩) }

/-- A note about a materialized answer, worked. -/
def pinSearchNote : Annotation :=
  { key := "foldlab/search-note"
  , subject := .result ⟨pinSubjectAddr⟩
  , value := .text "the second page is the one that answered it" }

/-- A preference attached to one recorded turn, worked. -/
def pinPref : Annotation :=
  { key := "foldlab/pref"
  , subject := .exchange ⟨pinSubjectAddr⟩
  , value := .text "prefer the shorter answer" }

/-- Content to vector, worked: the subject is the embedded content, the
value a typed reference to the chunk holding the vector's bytes. -/
def pinEmbedding : Annotation :=
  { key := "foldlab/embedding"
  , subject := .value ⟨pinSubjectAddr⟩
  , value := .ref (.chunk ⟨pinSubjectAddr⟩) }

/-- A retraction, worked on the reflexive arm: a tombstone over an
annotation, carrying its reason as text. -/
def pinTombstone : Annotation :=
  { key := "foldlab/tombstone"
  , subject := .annotation ⟨pinSubjectAddr⟩
  , value := .text "superseded by the grill's ruling" }

-- Two typed edges at the query kind: the search plane's own `pinLink`.
#guard putPayload pinAnnotationRevision pinRelated == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/related\",\"subject\":{\"_tag\":\"query\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"ref\",\"address\":{\"_tag\":\"query\",\"address\":{\"$ref\":1}}}}}"

#guard putRefs pinAnnotationRevision pinRelated == some
  [⟨queryKindTag, pinSubjectAddr⟩, ⟨queryKindTag, pinSubjectAddr⟩]

-- One typed edge at the result kind, and the note as text.
#guard putPayload pinAnnotationRevision pinSearchNote == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/search-note\",\"subject\":{\"_tag\":\"result\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"text\",\"text\":\"the second page is the one that answered it\"}}}"

#guard putRefs pinAnnotationRevision pinSearchNote == some
  [⟨resultKindTag, pinSubjectAddr⟩]

-- One typed edge at the exchange kind: the preference is about THAT
-- turn, and the edge is what says so.
#guard putPayload pinAnnotationRevision pinPref == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/pref\",\"subject\":{\"_tag\":\"exchange\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"text\",\"text\":\"prefer the shorter answer\"}}}"

#guard putRefs pinAnnotationRevision pinPref == some
  [⟨exchangeKindTag, pinSubjectAddr⟩]

-- The content plane on the subject edge and the chunk plane on the
-- value edge — both arms CA-1 admitted, in one node.
#guard putPayload pinAnnotationRevision pinEmbedding == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/embedding\",\"subject\":{\"_tag\":\"value\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"ref\",\"address\":{\"_tag\":\"chunk\",\"address\":{\"$ref\":1}}}}}"

#guard putRefs pinAnnotationRevision pinEmbedding == some
  [⟨valueKindTag, pinSubjectAddr⟩, ⟨chunkKindTag, pinSubjectAddr⟩]

-- The reflexive rung, at byte level: an annotation whose subject edge
-- expects this very kind. Unspellable before decision 40, because the
-- plane had no tag for an edge to demand.
#guard putPayload pinAnnotationRevision pinTombstone == some
  "{\"revision\":1,\"value\":{\"key\":\"foldlab/tombstone\",\"subject\":{\"_tag\":\"annotation\",\"address\":{\"$ref\":0}},\"value\":{\"_tag\":\"text\",\"text\":\"superseded by the grill's ruling\"}}}"

#guard putRefs pinAnnotationRevision pinTombstone == some
  [⟨annotationKindTag, pinSubjectAddr⟩]

/-- THE RATIFIED KEY FAMILY, as data: every `foldlab/` key the estate
pins, read off the worked pins rather than spelled a second time. The
name seat leads because it is the one the CLI writes; the rest are
decision 40's rider CA-2, in the order that decision names them. -/
def keyFamily : List String :=
  [pinName.key, pinRelated.key, pinSearchNote.key, pinPref.key,
   pinEmbedding.key, pinTombstone.key]

-- A key is how a consumer ADDRESSES an annotation's meaning, so two
-- pins sharing one would make the family ambiguous.
#guard decide (keyFamily.Nodup)

-- Every ratified key is `foldlab/`-namespaced and nothing else: the
-- persistent namespace is the slash namespace, because symbol-keyed
-- annotations are dropped at persistence.
#guard keyFamily.all fun k => k.startsWith "foldlab/"

-- `foldlab/view` is deliberately NOT in the family: it is the worked
-- example of a REF-valued annotation, not a ratified seat, and the
-- pin above is all it is.
#guard !keyFamily.contains pinLink.key

end Cas.Schema
