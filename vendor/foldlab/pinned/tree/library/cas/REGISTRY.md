# Kind-tag registry — scheme 0

Manifest version `1` — the version the JSON projection carries in its `manifestVersion` key.

GENERATED — projection of `Cas.Grammar.manifestV0` by `lake exe emitgrammar`; do not edit. Every layout below is read off a witness term per form — the encoders in `Cas/Grammar/Tree.lean` where the grammar has a constructor, the node itself where it has none — so this document cannot drift from what is written.

The wire kind tags of the grammar's sorts (`Cas/Grammar/Sorts.lean`, `Ty.wireTag`/`Ty.ofTag`). Ratified by the grammar grill (2026-08-28, rulings 2 and 3; recorded in `library/effects/IMPLEMENTATION-PLAN.md` §14), and extended once since, by decision 40 (2026-08-30): `annotation`, `agent`, `query` and `result` entered as ONE grilled batch under the principle that a thing deserves a sort iff the algebra needs typed, admission-checked references TO it. Tags 8, 9, and 10 are also the blob kinds of PROFILE-CAS-HTTP-0. A tag names one node form family; references type-check at tag granularity, so a row here is a contract on every wire.

The version above was bumped for a surface change, per the manifest-versioning ruling: a form's reference discipline is now stated under a `discipline` key rather than implied by the `refs` array alone. The previous version knew only fixed slot lists, so a reader of it would take a FREE discipline — any number of edges, constrained by a law rather than a list — for a form with no references at all. Consumers pinned to the previous version keep reading `refs` correctly for every fixed form; only the free ones need the new key.

## The node envelope

Every node is written as `version ++ tag ++ frame(payload) ++ nat32(refCount) ++ refs` and its content address is the digest of exactly those bytes. The version and tag bytes lead so that the separation theorems can quantify over them; the payload is framed rather than trailing, so the reference count is reachable without knowing a sort. Each reference record is one expected-tag byte followed by a 32-byte address.

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `version` | `u8` | 1 | the scheme-version byte — scheme 0 for every row here |
| `tag` | `u8` | 1 | the sort's wire kind tag: the row this manifest gives it |
| `payload` | `framed-u32` | variable | the sort's payload bytes, self-delimiting |
| `refCount` | `be-u32` | 4 | how many typed references follow |
| `refs` | `opaque` | variable | refCount reference records, in order |

## The sorts

| Tag (dec) | Tag (hex) | Sort | Status | Exemplar | Notes |
| --- | --- | --- | --- | --- | --- |
| 1 | `0x01` | `value` | RATIFIED core | `value-single` | Opaque value payload. A leaf: no references. |
| 8 | `0x08` | `chunk` | RATIFIED core | `blob-two-leaves` | Position-free chunk data (profile blob kind). The chunk carries no index: position lives in the `tree` leaf that names it, which is what lets one chunk be shared by two leaves. |
| 9 | `0x09` | `tree` | RATIFIED core | `blob-two-leaves` | Blob leaf and interior node share one sort and one tag — references type-check at tag granularity, so a `tree` edge accepts either. The forms are told apart by the payload: eight bytes for a leaf, none for an interior node. |
| 10 | `0x0A` | `manifest` | RATIFIED core | `blob-two-leaves` | Recipe-1 blob manifest (profile blob kind). Sixteen payload bytes in this order: recipe, total, leaf count — the total is the only 64-bit field in the grammar. |
| 11 | `0x0B` | `file` | RATIFIED core | `file-readme` | Named file over a blob manifest. Both payload fields are framed, so the payload is self-delimiting; each is bounded under 2^16 bytes so the framed pair stays inside one node payload bound. |
| 12 | `0x0C` | `entry` | RATIFIED core | `journal-two-entries` | Journal entry or genesis. The sort does not fix its reference list: the codec constrains a reference's expected tag, never the arity, so a reader dispatches on what it finds, not on this row. The agent language used to exercise exactly that latitude — it wrote a three-edge step (context, value, entry) over this same tag — and decision 40 moved that form onto its own `agent` row, because an edge expecting an AGENT specifically is unspellable while the form rides this tag and expected-tag checking is per-tag. Row `0x49` carries it now; what is left here is the journal. |
| 13 | `0x0D` | `context` | RATIFIED core | — | Context node: typed edges, no payload. The grammar has no `context` constructor — `Cas/Grammar/Tree.lean` writes no layout for this sort — so the row's witness is the NODE itself, the shape `CasExamples.AgentStep.contextNode` writes: empty payload, one typed edge per folded item, the edge tags read off whatever was loaded. A `Tree.context` constructor remains its own slice; the form does not wait on it. |
| 14 | `0x0E` | `step` | RATIFIED core | — | One code point of a defunctionalized program (F3). Ratified 2026-08-29 out of a reservation this registry carried since the defunctionalization landed: the tag was spelled as the bare def `Cas.Lang.stepWireTag` outside `Ty`, pinned in both directions by `#guard`, until `Ty.step` made the pin unnecessary — the name survives as an abbreviation of the sort's own tag. A step node carries NO references: its operands name earlier ANSWERS, which have no address until the table runs, so they live in the payload. The two forms are told apart by the leading discriminator byte, never by the tag. `Cas.Lang.decodeLine` recovers the code point from the node, and that round trip is what makes this layout a theorem. |
| 15 | `0x0F` | `cont` | RATIFIED core | — | A whole defunctionalized program as one node (F3) — the sort that makes a PROGRAM CONTENT. Ratified 2026-08-29 out of the same reservation as row 14, and spelled until then as `Cas.Lang.contWireTag`. The table node names its lines by address, so `Cas.Lang.encodeProg` lays a program out children-first: every step node, then the cont node referencing them all. `Cas.Lang.decodeProg_encodeProg` is the landing that earned the row: a table stored as content and recovered from that content is the same table, so it runs identically and denotes an observationally equal program. That is why a program is a sort and not a convention over the value plane. |
| 65 | `0x41` | `annotation` | RATIFIED core | — | The MEANING plane: one annotation node says one thing about one addressed value, and the DAG carries as many of them per subject as wanted. Ratified 2026-08-30 (decision 40) AT THE WORKING TAG it was already riding — `Cas/Schema/Annotation.lean` has put annotation nodes at `0x41` since the sidecar kind landed, so promoting that byte to a row re-authors no stored node and moves no address. The grammar has no `annotation` constructor, so the row's witness is the NODE, on the `context` precedent: the shape `Cas.Schema.putNode` writes through the annotation projection. What earned the row is the reflexive rung — an annotation ABOUT an annotation was unspellable while the plane had no tag to demand, because a reference demands one tag and expected-tag checking is per-tag. The subject union widened in the same versioning event to the content planes and to the batch's own four sorts, which is what makes notes-about-notes and notes-about-results spellable at all. |
| 71 | `0x47` | `git` | RATIFIED core | `git-pin-commit` | The estate's VERSIONING primitive (drafted 2026-08-29; awaiting ratification). A git object enters the store as content: the payload IS the loose-object preimage — `"<type> <length>\0" ++ content` — so `sha1(payload)` is the object's git id while the node's own address is the digest of its canonical pre-image. One node, two identities, neither declared in a field and both derivable by any host from the bytes alone. That dual identity is what makes the sort a versioning primitive rather than an import format: a commit admitted this way carries its git-side name with it, so pinning a dependency by revision and pinning it by content address name the same bytes, and the estate can hold a version without leaving the store. The exemplar is the `git-pin-commit` vector — the lean4-tree-sitter pin commit as one node, its payload's SHA-1 the commit id it names. References are empty in v0: git's internal SHA-1 edges (a commit's tree and parents, a tree's entries) stay inside the payload rather than becoming typed CAS edges, exactly as the schema sort's `$defs` graph does. Promoting them is the named follow-up, and is what would turn a pinned object into a walkable history. |
| 73 | `0x49` | `agent` | RATIFIED core | — | The ATTRIBUTION anchor. Ratified 2026-08-30 (decision 40) for the three-edge form the agent language already wrote — `CasExamples.AgentStep` admits exactly three nodes per step and the third was a journal `entry` over row `0x0C`. Riding that tag cost the thing the sort exists for: references type-check at tag granularity, so an edge expecting an AGENT specifically was unspellable, and "who did this" could not be asked of the store as a typed walk. The form is unchanged by the move — attestation, context, output, prev — and only the tag its `prev` edge demands changed, from the journal's to its own, which is what makes an agent chain a chain of agent steps rather than a branch of the journal. Two forms, on the `entry` precedent: a chain whose links point backwards has to bottom out, and `agent.genesis` is where. Greenfield made the migration free — the estate held no stored node at this form, so nothing was re-authored. |
| 81 | `0x51` | `query` | RATIFIED core | — | The SPEC plane — a query as content. Ratified 2026-08-30 (decision 40). A leaf, deliberately: a spec names the classifiers it runs by DERIVED NAME, the strings `names.json` carries, and a name is not an address, so there is nothing here for an edge to point at. What earned the row is the other direction — a `result` binds spec-to-query by a typed edge, annotations are written about queries, and related-edges run query to query; every one of those is a reference TO a spec, and a reference demands one tag. |
| 82 | `0x52` | `result` | RATIFIED core | — | The ANSWER plane — a materialized result set. Ratified 2026-08-30 (decision 40). The memoization law falls out of the shape rather than being enforced beside it: the node's preimage IS spec plus mark plus members, so the same spec at the same mark over the same members is the same address, and a duplicate put is the identity. This is also the INDEX kind the naming inventory anticipates — a materialized page of a query, which is what a reverse-ref index is a family of. A result is a REFERENCED thing (later steps hand result handles onward, annotations are written about answers), which is what earned it a tag rather than a composite. |
| 83 | `0x53` | `schema` | RATIFIED (opaque-payload revision 1) | `schema-vector-document` | Payload = the canonical JSON envelope of Effect's persistent `SchemaRepresentation` document; references remain empty. Revision 0's tagged projection is read-compatible. The cross-runtime byte pin is gated; the revision-1 byte theorem remains pending. Typed schema-to-schema edges (`$defs` as real CAS references) are the named follow-up. |

Rows 1 and 11–13 were previously marked "illustrative"; ruling 2 ratifies all seven data sorts into core. Consumer extension (profiles, the GrammarSpec registration pattern) is a named follow-up, not retrofitted here; a new tag enters only through the grill with a real consumer.

Rows 14 and 15 carried a reconciliation debt on purpose: they were used by `Cas/Lang/Defun.lean` but were NOT `Ty` constructors, and `Defun.lean` guarded both literals against this table AND guarded that `Ty.ofTag` still REFUSED both tags. That debt is DISCHARGED: the rows were ratified 2026-08-29 and are the `Ty.step` and `Ty.cont` sorts. The refusal guards went red exactly as designed and were removed with the reservation they pinned; the two names survive in `Defun.lean` as abbreviations of the sorts' own tags, so neither number is now written twice.

Rows 65, 73, 81 and 82 are decision 40's, ratified 2026-08-30 as ONE batch and not four rulings: `annotation` (the meaning column, promoted at the working tag it was already riding, so nothing stored moved), `agent` (the attribution anchor, taken off `entry`'s tag), `query` (specs as content) and `result` (materialized answers). The batch scopes the growth discipline rather than repealing it — one event, grilled once, and the stillness resumes with it. `text` was refused from the batch the same day: no logged vision sentence orders collaborative document editing, and the CRDT run's self-referencing parent pointer forces a tag only if a buffer is ever commissioned. None of the four has a `Tree` constructor, and none needs one — their writers sit at the node layer, exactly as `context`'s does.

No row is RESERVED today, and no row is formless. The registry keeps both notions anyway — a row id that is a bare tag, a status that says so, and the guards that tie the two together — because the next reservation should cost a red build rather than a silent drift, and the machinery is cheaper kept than re-derived.

## Payload layout and reference discipline

One section per node form, read off a witness term — a grammar term of `Cas/Grammar/Tree.lean`, or the node itself for a sort the grammar has no constructor for. Every row states a form.

### value.value

An opaque value payload.

- payload: variable
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `payload` | `opaque` | variable | the value's bytes; nothing in the grammar reads them |

### chunk.chunk

Position-free chunk data.

- payload: variable
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `bytes` | `opaque` | variable | the chunk's bytes |

### tree.leaf

A blob leaf: a positioned pointer at one chunk.

- payload: 8 bytes
- references: data

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `index` | `be-u32` | 4 | the leaf's absolute chunk index within the blob |
| `length` | `be-u32` | 4 | the declared byte length of the chunk |

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `data` | `chunk` | `0x08` | the chunk this leaf positions |

### tree.parent

A blob interior node: two ordered subtrees, no payload.

- payload: 0 bytes
- references: left, right

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `left` | `tree` | `0x09` | the earlier subtree |
| `right` | `tree` | `0x09` | the later subtree |

### manifest.manifest

The recipe-1 blob manifest.

- payload: 16 bytes
- references: root

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `recipe` | `be-u32` | 4 | the chunking recipe id (1 = fixed-size chunks) |
| `totalBytes` | `be-u64` | 8 | the blob's total byte length |
| `leafCount` | `be-u32` | 4 | how many leaves the tree carries |

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `root` | `tree` | `0x09` | the blob tree this manifest heads |

### file.file

A named file over a blob manifest.

- payload: variable, at least 8 bytes
- references: content

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `name` | `framed-u32` | variable | the file name, UTF-8, under 2^16 bytes |
| `mediaType` | `framed-u32` | variable | the media type, UTF-8, under 2^16 bytes |

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `content` | `manifest` | `0x0A` | the blob manifest holding the file's bytes |

### entry.genesis

The journal's first entry: no note, no edges.

- payload: 0 bytes
- references: none

### entry.entry

One journal entry over a file, linked to its predecessor.

- payload: variable
- references: item, prev

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `note` | `opaque` | variable | the entry's note bytes, uninterpreted |

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `item` | `file` | `0x0B` | the file this entry records |
| `prev` | `entry` | `0x0C` | the entry before it |

### context.context

A folded context: no payload, one typed edge per folded item.

- payload: 0 bytes
- references: free — any number of item edges

Free reference discipline: any number of `item` edges, no slot list. One edge per folded item, in fold order, any number of them. The sort fixes no slot list — a context is whatever was folded — so what holds instead is a law: every edge's expected tag must resolve through Ty.ofTag, a context edge may not carry an unratified tag. CasExamples.AgentStep.agentStep is the consumer that satisfies it, reading each edge tag off the node it loaded.

### step.put

A code point that admits a node whose references name operands.

- payload: variable, at least 11 bytes
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `form` | `u8` | 1 | 0x00 — this code point admits a node |
| `version` | `u8` | 1 | the scheme version of the node the line admits |
| `tag` | `u8` | 1 | the wire kind tag of the node the line admits |
| `payload` | `framed-u32` | variable | the admitted node's payload bytes, self-delimiting |
| `operandCount` | `be-u32` | 4 | how many typed operand records follow |
| `operands` | `opaque` | variable | operandCount records, each an expected-tag byte then an operand (0x00 and a 32-byte address, or 0x01 and a 32-bit answer index) |

### step.load

A code point that loads an operand.

- payload: variable, at least 2 bytes
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `form` | `u8` | 1 | 0x01 — this code point loads an operand |
| `operandKind` | `u8` | 1 | 0x00 a literal address, 0x01 an earlier answer |
| `operand` | `opaque` | variable | the operand's bytes: 32 address bytes under 0x00, a 32-bit big-endian index under 0x01 |

### cont.cont

A defunctionalized program: the line count, and one edge per code point in order.

- payload: 4 bytes
- references: free — any number of line edges

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `lineCount` | `be-u32` | 4 | how many code points the table holds |

Free reference discipline: any number of `line` edges, no slot list. One edge per code point, in program order, any number of them — a program's length is not a slot list. Every edge expects the step tag, which is stronger than the free law this discipline states; what the law itself forbids is a table edge at an unratified tag.

### annotation.annotation

One annotation: the projection envelope, the subject edge, and the value's edge when the value is a reference.

- payload: variable
- references: free — any number of link edges

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `projection` | `opaque` | variable | the annotation projection's canonical JSON envelope: the revision, then the key, the addressed subject and what the annotation says |

Free reference discipline: any number of `link` edges, no slot list. One edge per addressed reference the annotation carries: the SUBJECT first, then the value's own reference when the value is a typed one rather than text — one edge under the text arm, two under the ref arm. The sort fixes no slot list because the subject is a UNION over addressable planes and a reference demands one tag, so which tag edge 0 expects is the arm this annotation carries and not a fact of this row. The law every edge satisfies is that its expected tag is one AnnotationSubject names; unlike context and cont, that is NOT the same as resolving through Ty.ofTag, because two of the union's arms (exchange 0x58, system 0x54) address working tags with no registry row. Cas.Schema.pinLink is the worked example, and the witness above is its ratified-arm twin.

### git.git

A git object as content.

- payload: variable
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `object` | `opaque` | variable | the git loose-object preimage: the type word, a space, the decimal byte length, a NUL, then the object's content |

### agent.genesis

An agent chain's first step: no attestation, no edges.

- payload: 0 bytes
- references: none

### agent.agent

One agent step: the attestation, the context it folded, the answer it recorded, and the step before it.

- payload: variable
- references: context, output, prev

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `attestation` | `opaque` | variable | the executor's claim about the step it took, uninterpreted — a claim, never a proof |

| reference | expects | tag | meaning |
| --- | --- | --- | --- |
| `context` | `context` | `0x0D` | the folded context the step was taken over |
| `output` | `value` | `0x01` | the answer the step recorded |
| `prev` | `agent` | `0x49` | the step before it, or the chain's genesis |

### query.query

A query spec as content: the spec's bytes, and no edges.

- payload: variable
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `spec` | `opaque` | variable | the query spec's bytes — canonical JSON at the layer above, opaque here |

### result.result

A materialized answer: the mark it was computed at, the spec it answers, and one edge per member.

- payload: 4 bytes
- references: free — any number of member edges

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `mark` | `be-u32` | 4 | the word index the answer was computed at — the zero-based mark a non-monotone answer carries on its face |

Free reference discipline: any number of `member` edges, no slot list. The SPEC first — edge 0 expects the query tag, and is the spec this node answers — then one edge per member of the answer, in fold order, any number of them. The discipline is free rather than a slot list because an answer's length is not a manifest fact, and the manifest's two disciplines cannot state a fixed head and a free tail in one form: .fixed is checked as exact list equality against the witness and .free names no slots at all. So the leading slot is stated as this law instead of as a table, and what the law adds to the free one is that edge 0 is the spec. Every member edge's expected tag must resolve through Ty.ofTag, exactly as a context's must.

### schema.schema

A canonical schema as content.

- payload: variable
- references: none

| field | encoding | bytes | meaning |
| --- | --- | --- | --- |
| `bytes` | `opaque` | variable | the schema's canonical bytes, opaque at this layer |
