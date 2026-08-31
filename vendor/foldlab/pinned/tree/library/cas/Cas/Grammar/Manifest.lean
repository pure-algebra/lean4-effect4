import Cas.Grammar.Tree
import Cas.Codec.Hex
import Cas.Values.Json
import Cas.Values.Markdown

/-!
# The grammar manifest — the sort table as data

The interchange document of the data grammar, in the R11 shape the
lift lane established (`Cas/Lift/Manifest.lean`): one described
manifest, both surfaces generated. `lake exe emitgrammar` renders the
JSON the front ends consume and `REGISTRY.md`, the human registry, from
this one value; neither is hand-maintained and both are byte-gated.

The rows do not TRANSCRIBE a layout. Every form carries a WITNESS —
a term whose elaboration IS the shape the row states — and the guards
below read the tag, the payload width, and the reference discipline off
the node that witness produces (the `Cas.Backend.Admission` pattern). A
change to an encoder in `Cas/Grammar/Tree.lean` therefore moves this
manifest's bytes or turns the build red; it cannot silently part from
it.

A witness has two arms, because a sort can be real on the wire without
having a `Tree` constructor: `.tree` is a grammar term, elaborated by
`Tree.node`; `.node` is the node itself, for a sort whose only writers
sit at the node layer. `context`, `step`, and `cont` are those sorts —
ratified tags with real writers and no constructor — so each states its
forms as literal nodes rather than through a fake constructor. The
program sorts' writers are `Cas/Lang/Defun.lean`'s `encodeLine` and
`tableNode`, which this module may not import (layer 3 sits above layer
2); the literal nodes here are that layout spelled at layer 2, and
`decodeProg`'s round trip is what holds them to it.

A form's references are a DISCIPLINE, not always a list. `.fixed` names
the slots exactly — the discipline of every grammar constructor.
`.free` names none and states a law instead: every edge must resolve
through `Ty.ofTag`, so a free node may not carry an unratified tag.
`context` is the free one, because a context is whatever was folded,
and a slot list would be a lie in the shape of a table.

EVERY row now carries a form. Rows 14/15 were the last exception —
code points spelled outside `Ty` while their sorts were only reserved —
and they were ratified 2026-08-29. The `.reserved` row id and status
arms remain, unpopulated, for the next reservation: their guards below
are what makes the exception cost a red build rather than a silent
drift, and they are cheaper kept than re-derived.
-/

namespace Cas.Grammar

open Cas.Values.Markdown

/-! ## Prose

Free prose is typed inline content, not a string: the registry's
paragraphs carry code spans, and the estate's Markdown emitter escapes
everything that is not one. The JSON projection flattens the same
value to plain text. -/

/-- A prose fragment: typed inline content, rendered by the house
Markdown emitter and flattened for JSON. -/
abbrev Prose := List Inline

def Inline.plain : Inline → String
  | .text s => s
  | .bold s => s
  | .code s => s

def Prose.plain (p : Prose) : String := String.join (p.map Inline.plain)

/-! ## Field encodings

The four widths and the two variable forms the node codec actually
writes (`Cas/Codec/Nat32.lean`, `Cas/Codec/Bytes.lean`). Nothing else
appears in an encoder, so nothing else appears here. -/

/-- How one field is written into a payload or into the node envelope. -/
inductive FieldEnc where
  /-- One bare byte. -/
  | u8
  /-- Four bytes, big-endian (`Cas.nat32`). -/
  | beU32
  /-- Eight bytes, big-endian, written as two 32-bit halves
  (`Cas.nat64`). -/
  | beU64
  /-- A framed byte string (`Cas.frame`): a big-endian 32-bit byte
  length, then that many bytes. -/
  | framed
  /-- Uninterpreted bytes running to the end of the payload. -/
  | opaque
  deriving DecidableEq, Repr

def FieldEnc.wire : FieldEnc → String
  | .u8 => "u8"
  | .beU32 => "be-u32"
  | .beU64 => "be-u64"
  | .framed => "framed-u32"
  | .opaque => "opaque"

/-- The fixed width of an encoding, when it has one. -/
def FieldEnc.bytes : FieldEnc → Option Nat
  | .u8 => some 1
  | .beU32 => some 4
  | .beU64 => some 8
  | .framed => none
  | .opaque => none

/-- The smallest number of bytes an encoding can occupy: its width when
fixed, its length prefix when framed, nothing when opaque. -/
def FieldEnc.minBytes : FieldEnc → Nat
  | .u8 => 1
  | .beU32 => 4
  | .beU64 => 8
  | .framed => 4
  | .opaque => 0

def FieldEnc.meaning : FieldEnc → String
  | .u8 => "one byte"
  | .beU32 => "a 32-bit natural, big-endian, four bytes"
  | .beU64 => "a 64-bit natural, big-endian, eight bytes (two 32-bit halves)"
  | .framed => "a 32-bit big-endian byte length, then that many bytes"
  | .opaque => "uninterpreted bytes, running to the end of the payload"

/-- Every encoding, in width order. -/
def FieldEnc.all : List FieldEnc := [.u8, .beU32, .beU64, .framed, .opaque]

theorem FieldEnc.all_complete (e : FieldEnc) : e ∈ FieldEnc.all := by
  cases e <;> decide

-- The wire spellings collide with nothing.
#guard decide ((FieldEnc.all.map FieldEnc.wire).Nodup)

-- The stated widths ARE the encoders' widths, not a transcription.
#guard (Cas.nat32 0).length == FieldEnc.beU32.minBytes
#guard (Cas.nat64 0).length == FieldEnc.beU64.minBytes
#guard (Cas.frame [1, 2, 3]).length == FieldEnc.framed.minBytes + 3

/-! ## The row shape -/

/-- The registry name of a sort — the one spelling every surface uses
for it. -/
def Ty.sortName : Ty → String
  | .value => "value"
  | .chunk => "chunk"
  | .tree => "tree"
  | .manifest => "manifest"
  | .file => "file"
  | .entry => "entry"
  | .context => "context"
  | .step => "step"
  | .cont => "cont"
  | .schema => "schema"
  | .git => "git"
  | .annotation => "annotation"
  | .agent => "agent"
  | .query => "query"
  | .result => "result"

/-- One payload field: its name, how it is written, what it means. -/
structure Field where
  name : String
  enc : FieldEnc
  meaning : String

/-- One reference slot: its name, the sort the reference is expected to
have (references type-check at tag granularity), what it means. -/
structure Slot where
  name : String
  expects : Ty
  meaning : String

/-- How a form's references are constrained. Two disciplines, because
the grammar has two kinds of node.

`.fixed` names the slots exactly: the form writes those references, in
that order, and nothing else — the discipline of every constructor in
`Cas/Grammar/Tree.lean`.

`.free` names no slots: the form writes any number of edges, and what
holds of them is a LAW rather than a list — every edge must resolve
through `Ty.ofTag`, so a free-discipline node may not carry an
unratified tag. That is the constraint a folded `context` actually
satisfies, and stating it as a slot list would be a lie in the shape of
a table. -/
inductive RefDiscipline where
  /-- Exactly these slots, in this order. -/
  | fixed (slots : List Slot)
  /-- Any number of edges of one named kind, each carrying a ratified
  sort's tag. -/
  | free (name : String) (meaning : String)

/-- The slots a discipline names — none, under a free one. -/
def RefDiscipline.slots : RefDiscipline → List Slot
  | .fixed ss => ss
  | .free _ _ => []

/-- The discipline's wire spelling, the `discipline` key's `kind`. -/
def RefDiscipline.kind : RefDiscipline → String
  | .fixed _ => "fixed"
  | .free _ _ => "free"

/-- What a form's shape is read off. `.tree` is a grammar term, whose
elaboration under `Tree.node` IS the form's node; `.node` is that node
written directly, for a ratified sort the grammar has no constructor
for. Both arms answer the same question — what bytes does this form
write — so every guard below reads `Form.node` and never the arm. -/
inductive Witness where
  /-- A grammar term: `Cas/Grammar/Tree.lean` elaborates the shape. -/
  | tree (w : Σ t : Ty, Tree t)
  /-- The node itself: the sort is written at the node layer, by
  consumers, with no constructor standing between. -/
  | node (n : Node)

/-- LAW SM-28: a form's layout is read off its witness term, never
transcribed.

One node form of a sort. A sort with two forms (a blob `tree` is a
leaf or an interior node; an `entry` is the genesis or a linked entry)
has two rows here and ONE wire tag: the forms are told apart by their
payload, never by the tag.

`witness` is a term whose elaboration IS this form's shape. The fields
and the reference discipline below are checked against it; they are not
a second spelling of the encoder. -/
structure Form where
  name : String
  witness : Witness
  fields : List Field
  refs : RefDiscipline
  meaning : String

/-- The node a form's witness elaborates to. The address function is
irrelevant to everything the guards read (tag, payload, expected tags),
so a constant one is enough. -/
private def noAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

private def noH : Bytes → Addr32 := fun _ => noAddr

def Form.node (f : Form) : Node :=
  match f.witness with
  | .tree w => w.2.node noH
  | .node n => n

/-- The form's payload width, when every field is fixed-width. -/
def Form.payloadBytes (f : Form) : Option Nat :=
  f.fields.foldr
    (fun d acc => match d.enc.bytes, acc with
      | some n, some m => some (n + m)
      | _, _ => none)
    (some 0)

/-- The smallest payload the form can write. -/
def Form.payloadMinBytes (f : Form) : Nat :=
  (f.fields.map (·.enc.minBytes)).sum

/-- A registry row's identity: a grammar sort, or a reserved tag that
is not (yet) a `Ty` constructor. -/
inductive RowId where
  | sort (t : Ty)
  | reserved (tag : UInt8)
  deriving DecidableEq, Repr

def RowId.wireTag : RowId → UInt8
  | .sort t => t.wireTag
  | .reserved tag => tag

/-- A row's standing in the registry. -/
inductive Status where
  /-- Ratified core (grammar grill ruling 2, 2026-08-28). -/
  | core
  /-- Ratified at opaque-payload revision 1 (the schema sort). -/
  | revision1
  /-- A registry row that is not a `Ty` constructor. -/
  | reserved
  deriving DecidableEq, Repr

def Status.wire : Status → String
  | .core => "RATIFIED core"
  | .revision1 => "RATIFIED (opaque-payload revision 1)"
  | .reserved => "RESERVED"

def Status.isReserved : Status → Bool
  | .reserved => true
  | _ => false

def Status.all : List Status := [.core, .revision1, .reserved]

theorem Status.all_complete (s : Status) : s ∈ Status.all := by
  cases s <;> decide

#guard decide ((Status.all.map Status.wire).Nodup)

/-- One registry row: a tag, the sort it names, its standing, the node
forms that write it, a conformance vector that exhibits it, and the
row's prose. -/
structure Row where
  id : RowId
  name : String
  status : Status
  forms : List Form
  exemplar : Option String
  notes : Prose

/-- The node envelope every sort's payload sits inside: the canonical
pre-image `Cas.encodeNode` writes. Stated once, because it is the same
for every row. -/
structure Envelope where
  fields : List Field
  refRecordBytes : Nat
  meaning : Prose

/-- The manifest: the whole data grammar's wire surface, as data. -/
structure Manifest where
  manifestVersion : Nat
  grammar : String
  scheme : Nat
  title : String
  preamble : List Prose
  envelope : Envelope
  rows : List Row
  closing : List Prose

/-! ## v0 -/

private def wValue : Tree .value := .value (Payload.ofBytes [1, 2, 3])
private def wChunk : Tree .chunk := .chunk (Payload.ofBytes [1, 2, 3])
private def wLeaf : Tree .tree := .leaf 0 3 wChunk
private def wParent : Tree .tree := .parent wLeaf wLeaf
private def wManifest : Tree .manifest := .manifest 1 3 1 wLeaf
private def wFile : Tree .file :=
  .file (Name.utf8 "a.txt") (Name.utf8 "text/plain") wManifest
private def wGenesis : Tree .entry := .genesis
private def wEntry : Tree .entry := .entry (Payload.ofBytes [1]) wFile wGenesis
private def wSchema : Tree .schema := .schema (Payload.ofBytes [123, 125])
/-- A git loose-object preimage: `"blob 1\0" ++ "x"`. -/
private def wGit : Tree .git :=
  .git (Payload.ofBytes [98, 108, 111, 98, 32, 49, 0, 120])

/-- The `context` shape as a node, because the grammar has no
constructor for it: empty payload, one typed edge per folded item, the
edge tag read off whatever was loaded. This is the shape
`CasExamples.AgentStep.contextNode` writes — layer 2 cannot import the
examples, so the witness is that node spelled here, and any drift
between the two is a drift the consumer's own build shows. One
value-tag edge stands for the list. -/
private def wContext : Node :=
  ⟨schemeVersion, Ty.context.wireTag, [], [⟨Ty.value.wireTag, noAddr⟩]⟩

/-! ### The program witnesses

`Cas/Lang/Defun.lean` writes the `step` and `cont` sorts and this
module may not import it — layer 3 sits above layer 2 — so the three
witnesses below spell that layout at layer 2, through the same byte
primitives the encoder uses. `tools/EmitGrammar.lean` sits above both
and is where the two are pinned against each other; the round trip
(`decodeProg_encodeProg`) is what makes the layout a theorem rather
than a convention. -/

/-- A `put` code point as a node — `Cas.Lang.encodeLine` of a
`PLine.put`. The body leads with the `0x00` put discriminator, then the
version and tag of the node the line admits, its framed payload, the
operand-reference count, and one record per operand. This witness
admits a three-byte `value` node whose single reference names the
zeroth earlier answer: `0x00 ‖ 0 ‖ 1 ‖ frame [7,7,7] ‖ nat32 1 ‖ (1 ‖
0x01 ‖ nat32 0)`. The node's own references are EMPTY, and that is the
sort's whole point: a line's operands name answers, which have no
address until the table runs. -/
private def wStepPut : Node :=
  ⟨schemeVersion, Ty.step.wireTag,
    0 :: schemeVersion :: Ty.value.wireTag ::
      (Cas.frame [7, 7, 7] ++
        (Cas.nat32 1 ++ (Ty.value.wireTag :: 1 :: Cas.nat32 0))),
    []⟩

/-- A `load` code point as a node — `Cas.Lang.encodeLine` of a
`PLine.load`. The body leads with the `0x01` load discriminator, then
one operand: a kind byte (`0x00` a literal 32-byte address, `0x01` an
earlier answer) and its bytes. This witness loads the zeroth earlier
answer: `0x01 ‖ 0x01 ‖ nat32 0`. -/
private def wStepLoad : Node :=
  ⟨schemeVersion, Ty.step.wireTag, 1 :: 1 :: Cas.nat32 0, []⟩

/-- A table as a node — `Cas.Lang.tableNode`. The payload is the line
count and nothing else; the lines themselves are the edges, one per
code point in program order, each expecting the `step` tag. One edge
stands for the table. -/
private def wCont : Node :=
  ⟨schemeVersion, Ty.cont.wireTag, Cas.nat32 1,
    [⟨Ty.step.wireTag, noAddr⟩]⟩

/-! ### The sort-event witnesses (decision 40)

Four sorts ratified 2026-08-30 as one batch, and not one of them has a
`Tree` constructor: the grammar builds blobs and journals, while these
four are written by the schema plane (`Cas/Schema/Annotation.lean`) and
by the agent language (`examples/CasExamples/AgentStep.lean`). Each
witness is therefore the NODE, on the `context` precedent — a ratified
row whose shape is read off what its writer writes, not off a
constructor the grammar does not have.

The `annotation` witness spells at layer 2 what
`Cas.Schema.putNode … pinAnnotationKindTag …` writes, exactly as the
program witnesses above spell `Defun`'s encoders; `tools/EmitGrammar.lean`
sits above both planes and is where the hand-spelling is held to the
projection. -/

/-- An annotation node — `Cas.Schema.putNode` of an annotation whose
value is a typed reference. The payload is the projection envelope
(revision, then the annotation), and the two edges are the SUBJECT and
the value's own reference, in that order. Both arms here are ratified
planes, which is what lets the free-discipline guard read this witness;
the arms at working tags are the reason the row's law is stated the way
it is. -/
private def wAnnotation : Node :=
  ⟨schemeVersion, Ty.annotation.wireTag,
    utf8 "{\"revision\":1,\"value\":{\"key\":\"foldlab/view\",\
\"subject\":{\"_tag\":\"program\",\"address\":{\"$ref\":0}},\
\"value\":{\"_tag\":\"ref\",\"address\":{\"_tag\":\"git\",\
\"address\":{\"$ref\":1}}}}}",
    [⟨Ty.cont.wireTag, noAddr⟩, ⟨Ty.git.wireTag, noAddr⟩]⟩

/-- An agent chain's first step: no attestation, no edges. The `prev`
edge of the form below expects this sort, so a chain has to bottom out
somewhere, and this is where — `entry.genesis`'s move, at the sort that
took the three-edge form off `entry`'s tag. -/
private def wAgentGenesis : Node :=
  ⟨schemeVersion, Ty.agent.wireTag, [], []⟩

/-- One agent step as a node — the shape
`CasExamples.AgentStep.agentNode` writes: the executor's attestation as
the payload, and three typed edges, the folded context, the answer it
produced, and the step before it. -/
private def wAgent : Node :=
  ⟨schemeVersion, Ty.agent.wireTag, utf8 "model=scripted;t=0",
    [⟨Ty.context.wireTag, noAddr⟩, ⟨Ty.value.wireTag, noAddr⟩,
     ⟨Ty.agent.wireTag, noAddr⟩]⟩

/-- A query spec as a node: the spec's bytes and no edges. A spec names
the classifiers it runs by DERIVED NAME — the strings `names.json`
carries — and a name is not an address, so this sort is a leaf. -/
private def wQuery : Node :=
  ⟨schemeVersion, Ty.query.wireTag,
    utf8 "{\"aggregator\":\"count\",\"generator\":\"tree.leaf\",\"rung\":\"R1\"}",
    []⟩

/-- A materialized answer as a node: the mark it was computed at, the
spec it answers, and one edge per member. The witness carries one
member so the free law has an edge to read. -/
private def wResult : Node :=
  ⟨schemeVersion, Ty.result.wireTag, Cas.nat32 7,
    [⟨Ty.query.wireTag, noAddr⟩, ⟨Ty.value.wireTag, noAddr⟩]⟩

def envelopeV0 : Envelope where
  fields := [
    { name := "version", enc := .u8,
      meaning := "the scheme-version byte — scheme 0 for every row here" },
    { name := "tag", enc := .u8,
      meaning := "the sort's wire kind tag: the row this manifest gives it" },
    { name := "payload", enc := .framed,
      meaning := "the sort's payload bytes, self-delimiting" },
    { name := "refCount", enc := .beU32,
      meaning := "how many typed references follow" },
    { name := "refs", enc := .opaque,
      meaning := "refCount reference records, in order" }
  ]
  refRecordBytes := 33
  meaning := [
    .text "Every node is written as ", .code "version ++ tag ++ frame(payload) ++ nat32(refCount) ++ refs",
    .text " and its content address is the digest of exactly those bytes. \
The version and tag bytes lead so that the separation theorems can \
quantify over them; the payload is framed rather than trailing, so the \
reference count is reachable without knowing a sort. Each reference \
record is one expected-tag byte followed by a 32-byte address."]

/-- LAW SM-26: the human kind-tag registry is this value's Markdown
projection, and every sort carries a row.

The authority for both projections — `REGISTRY.md` for readers and the
front ends' `manifest.json` — so the registry is generated from one
description rather than kept in step by hand. -/
def manifestV0 : Manifest where
  manifestVersion := 1
  grammar := "cas-grammar"
  scheme := 0
  title := "Kind-tag registry — scheme 0"
  preamble := [
    [.text "GENERATED — projection of ", .code "Cas.Grammar.manifestV0",
     .text " by ", .code "lake exe emitgrammar", .text "; do not edit. \
Every layout below is read off a witness term per form — the encoders \
in ", .code "Cas/Grammar/Tree.lean", .text " where the grammar has a \
constructor, the node itself where it has none — so this document \
cannot drift from what is written."],
    [.text "The wire kind tags of the grammar's sorts (",
     .code "Cas/Grammar/Sorts.lean", .text ", ", .code "Ty.wireTag",
     .text "/", .code "Ty.ofTag", .text "). Ratified by the grammar \
grill (2026-08-28, rulings 2 and 3; recorded in ",
     .code "library/effects/IMPLEMENTATION-PLAN.md", .text " §14), and \
extended once since, by decision 40 (2026-08-30): ", .code "annotation",
     .text ", ", .code "agent", .text ", ", .code "query", .text " and ",
     .code "result", .text " entered as ONE grilled batch under the \
principle that a thing deserves a sort iff the algebra needs typed, \
admission-checked references TO it. Tags 8, 9, and 10 are also the blob \
kinds of PROFILE-CAS-HTTP-0. A tag names one node form family; \
references type-check at tag granularity, so a row here is a contract \
on every wire."],
    [.text "The version above was bumped for a surface change, per the \
manifest-versioning ruling: a form's reference discipline is now stated \
under a ", .code "discipline", .text " key rather than implied by the ",
     .code "refs", .text " array alone. The previous version knew only \
fixed slot lists, so a reader of it would take a FREE discipline — any \
number of edges, constrained by a law rather than a list — for a form \
with no references at all. Consumers pinned to the previous version \
keep reading ", .code "refs", .text " correctly for every fixed form; \
only the free ones need the new key."]
  ]
  envelope := envelopeV0
  rows := [
    { id := .sort .value, name := "value", status := .core
      exemplar := some "value-single"
      forms := [
        { name := "value", witness := .tree ⟨.value, wValue⟩
          fields := [
            { name := "payload", enc := .opaque,
              meaning := "the value's bytes; nothing in the grammar reads them" }]
          refs := .fixed []
          meaning := "An opaque value payload." }]
      notes := [.text "Opaque value payload. A leaf: no references." ] },
    { id := .sort .chunk, name := "chunk", status := .core
      exemplar := some "blob-two-leaves"
      forms := [
        { name := "chunk", witness := .tree ⟨.chunk, wChunk⟩
          fields := [
            { name := "bytes", enc := .opaque,
              meaning := "the chunk's bytes" }]
          refs := .fixed []
          meaning := "Position-free chunk data." }]
      notes := [.text "Position-free chunk data (profile blob kind). \
The chunk carries no index: position lives in the ", .code "tree",
        .text " leaf that names it, which is what lets one chunk be \
shared by two leaves."] },
    { id := .sort .tree, name := "tree", status := .core
      exemplar := some "blob-two-leaves"
      forms := [
        { name := "leaf", witness := .tree ⟨.tree, wLeaf⟩
          fields := [
            { name := "index", enc := .beU32,
              meaning := "the leaf's absolute chunk index within the blob" },
            { name := "length", enc := .beU32,
              meaning := "the declared byte length of the chunk" }]
          refs := .fixed [
            { name := "data", expects := .chunk,
              meaning := "the chunk this leaf positions" }]
          meaning := "A blob leaf: a positioned pointer at one chunk." },
        { name := "parent", witness := .tree ⟨.tree, wParent⟩
          fields := []
          refs := .fixed [
            { name := "left", expects := .tree, meaning := "the earlier subtree" },
            { name := "right", expects := .tree, meaning := "the later subtree" }]
          meaning := "A blob interior node: two ordered subtrees, no payload." }]
      notes := [.text "Blob leaf and interior node share one sort and \
one tag — references type-check at tag granularity, so a ", .code "tree",
        .text " edge accepts either. The forms are told apart by the \
payload: eight bytes for a leaf, none for an interior node."] },
    { id := .sort .manifest, name := "manifest", status := .core
      exemplar := some "blob-two-leaves"
      forms := [
        { name := "manifest", witness := .tree ⟨.manifest, wManifest⟩
          fields := [
            { name := "recipe", enc := .beU32,
              meaning := "the chunking recipe id (1 = fixed-size chunks)" },
            { name := "totalBytes", enc := .beU64,
              meaning := "the blob's total byte length" },
            { name := "leafCount", enc := .beU32,
              meaning := "how many leaves the tree carries" }]
          refs := .fixed [
            { name := "root", expects := .tree,
              meaning := "the blob tree this manifest heads" }]
          meaning := "The recipe-1 blob manifest." }]
      notes := [.text "Recipe-1 blob manifest (profile blob kind). \
Sixteen payload bytes in this order: recipe, total, leaf count — the \
total is the only 64-bit field in the grammar."] },
    { id := .sort .file, name := "file", status := .core
      exemplar := some "file-readme"
      forms := [
        { name := "file", witness := .tree ⟨.file, wFile⟩
          fields := [
            { name := "name", enc := .framed,
              meaning := "the file name, UTF-8, under 2^16 bytes" },
            { name := "mediaType", enc := .framed,
              meaning := "the media type, UTF-8, under 2^16 bytes" }]
          refs := .fixed [
            { name := "content", expects := .manifest,
              meaning := "the blob manifest holding the file's bytes" }]
          meaning := "A named file over a blob manifest." }]
      notes := [.text "Named file over a blob manifest. Both payload \
fields are framed, so the payload is self-delimiting; each is bounded \
under 2^16 bytes so the framed pair stays inside one node payload \
bound."] },
    { id := .sort .entry, name := "entry", status := .core
      exemplar := some "journal-two-entries"
      forms := [
        { name := "genesis", witness := .tree ⟨.entry, wGenesis⟩
          fields := []
          refs := .fixed []
          meaning := "The journal's first entry: no note, no edges." },
        { name := "entry", witness := .tree ⟨.entry, wEntry⟩
          fields := [
            { name := "note", enc := .opaque,
              meaning := "the entry's note bytes, uninterpreted" }]
          refs := .fixed [
            { name := "item", expects := .file,
              meaning := "the file this entry records" },
            { name := "prev", expects := .entry,
              meaning := "the entry before it" }]
          meaning := "One journal entry over a file, linked to its predecessor." }]
      notes := [.text "Journal entry or genesis. The sort does not fix \
its reference list: the codec constrains a reference's expected tag, \
never the arity, so a reader dispatches on what it finds, not on this \
row. The agent language used to exercise exactly that latitude — it \
wrote a three-edge step (context, value, entry) over this same tag — \
and decision 40 moved that form onto its own ", .code "agent",
        .text " row, because an edge expecting an AGENT specifically is \
unspellable while the form rides this tag and expected-tag checking is \
per-tag. Row ", .code "0x49", .text " carries it now; what is left \
here is the journal."] },
    { id := .sort .context, name := "context", status := .core
      exemplar := none
      forms := [
        { name := "context", witness := .node wContext
          fields := []
          refs := .free "item"
            "One edge per folded item, in fold order, any number of \
them. The sort fixes no slot list — a context is whatever was folded — \
so what holds instead is a law: every edge's expected tag must resolve \
through Ty.ofTag, a context edge may not carry an unratified tag. \
CasExamples.AgentStep.agentStep is the consumer that satisfies it, \
reading each edge tag off the node it loaded."
          meaning := "A folded context: no payload, one typed edge per folded item." }]
      notes := [.text "Context node: typed edges, no payload. The \
grammar has no ", .code "context", .text " constructor — ",
        .code "Cas/Grammar/Tree.lean", .text " writes no layout for \
this sort — so the row's witness is the NODE itself, the shape ",
        .code "CasExamples.AgentStep.contextNode", .text " writes: \
empty payload, one typed edge per folded item, the edge tags read off \
whatever was loaded. A ", .code "Tree.context", .text " constructor \
remains its own slice; the form does not wait on it."] },
    { id := .sort .step, name := "step", status := .core
      exemplar := none
      forms := [
        { name := "put", witness := .node wStepPut
          fields := [
            { name := "form", enc := .u8,
              meaning := "0x00 — this code point admits a node" },
            { name := "version", enc := .u8,
              meaning := "the scheme version of the node the line admits" },
            { name := "tag", enc := .u8,
              meaning := "the wire kind tag of the node the line admits" },
            { name := "payload", enc := .framed,
              meaning := "the admitted node's payload bytes, self-delimiting" },
            { name := "operandCount", enc := .beU32,
              meaning := "how many typed operand records follow" },
            { name := "operands", enc := .opaque,
              meaning := "operandCount records, each an expected-tag byte then an operand (0x00 and a 32-byte address, or 0x01 and a 32-bit answer index)" }]
          refs := .fixed []
          meaning := "A code point that admits a node whose references name operands." },
        { name := "load", witness := .node wStepLoad
          fields := [
            { name := "form", enc := .u8,
              meaning := "0x01 — this code point loads an operand" },
            { name := "operandKind", enc := .u8,
              meaning := "0x00 a literal address, 0x01 an earlier answer" },
            { name := "operand", enc := .opaque,
              meaning := "the operand's bytes: 32 address bytes under 0x00, a 32-bit big-endian index under 0x01" }]
          refs := .fixed []
          meaning := "A code point that loads an operand." }]
      notes := [.text "One code point of a defunctionalized program \
(F3). Ratified 2026-08-29 out of a reservation this registry carried \
since the defunctionalization landed: the tag was spelled as the bare \
def ", .code "Cas.Lang.stepWireTag", .text " outside ", .code "Ty",
        .text ", pinned in both directions by ", .code "#guard",
        .text ", until ", .code "Ty.step", .text " made the pin \
unnecessary — the name survives as an abbreviation of the sort's own \
tag. A step node carries NO references: its operands name earlier \
ANSWERS, which have no address until the table runs, so they live in \
the payload. The two forms are told apart by the leading discriminator \
byte, never by the tag. ", .code "Cas.Lang.decodeLine",
        .text " recovers the code point from the node, and that round \
trip is what makes this layout a theorem."] },
    { id := .sort .cont, name := "cont", status := .core
      exemplar := none
      forms := [
        { name := "cont", witness := .node wCont
          fields := [
            { name := "lineCount", enc := .beU32,
              meaning := "how many code points the table holds" }]
          refs := .free "line"
            "One edge per code point, in program order, any number of \
them — a program's length is not a slot list. Every edge expects the \
step tag, which is stronger than the free law this discipline states; \
what the law itself forbids is a table edge at an unratified tag."
          meaning := "A defunctionalized program: the line count, and one edge per code point in order." }]
      notes := [.text "A whole defunctionalized program as one node \
(F3) — the sort that makes a PROGRAM CONTENT. Ratified 2026-08-29 out \
of the same reservation as row 14, and spelled until then as ",
        .code "Cas.Lang.contWireTag", .text ". The table node names its \
lines by address, so ", .code "Cas.Lang.encodeProg",
        .text " lays a program out children-first: every step node, \
then the cont node referencing them all. ",
        .code "Cas.Lang.decodeProg_encodeProg",
        .text " is the landing that earned the row: a table stored as \
content and recovered from that content is the same table, so it runs \
identically and denotes an observationally equal program. That is why \
a program is a sort and not a convention over the value plane."] },
    { id := .sort .annotation, name := "annotation", status := .core
      exemplar := none
      forms := [
        { name := "annotation", witness := .node wAnnotation
          fields := [
            { name := "projection", enc := .opaque,
              meaning := "the annotation projection's canonical JSON envelope: the revision, then the key, the addressed subject and what the annotation says" }]
          refs := .free "link"
            "One edge per addressed reference the annotation carries: \
the SUBJECT first, then the value's own reference when the value is a \
typed one rather than text — one edge under the text arm, two under \
the ref arm. The sort fixes no slot list because the subject is a \
UNION over addressable planes and a reference demands one tag, so \
which tag edge 0 expects is the arm this annotation carries and not a \
fact of this row. The law every edge satisfies is that its expected \
tag is one AnnotationSubject names; unlike context and cont, that is \
NOT the same as resolving through Ty.ofTag, because two of the union's \
arms (exchange 0x58, system 0x54) address working tags with no \
registry row. Cas.Schema.pinLink is the worked example, and the \
witness above is its ratified-arm twin."
          meaning := "One annotation: the projection envelope, the subject edge, and the value's edge when the value is a reference." }]
      notes := [.text "The MEANING plane: one annotation node says one \
thing about one addressed value, and the DAG carries as many of them \
per subject as wanted. Ratified 2026-08-30 (decision 40) AT THE \
WORKING TAG it was already riding — ", .code "Cas/Schema/Annotation.lean",
        .text " has put annotation nodes at ", .code "0x41",
        .text " since the sidecar kind landed, so promoting that byte \
to a row re-authors no stored node and moves no address. The grammar \
has no ", .code "annotation", .text " constructor, so the row's \
witness is the NODE, on the ", .code "context",
        .text " precedent: the shape ", .code "Cas.Schema.putNode",
        .text " writes through the annotation projection. What earned \
the row is the reflexive rung — an annotation ABOUT an annotation was \
unspellable while the plane had no tag to demand, because a reference \
demands one tag and expected-tag checking is per-tag. The subject \
union widened in the same versioning event to the content planes and \
to the batch's own four sorts, which is what makes notes-about-notes \
and notes-about-results spellable at all."] },
    { id := .sort .git, name := "git", status := .core
      exemplar := some "git-pin-commit"
      forms := [
        { name := "git", witness := .tree ⟨.git, wGit⟩
          fields := [
            { name := "object", enc := .opaque,
              meaning := "the git loose-object preimage: the type word, a space, the decimal byte length, a NUL, then the object's content" }]
          refs := .fixed []
          meaning := "A git object as content." }]
      notes := [.text "The estate's VERSIONING primitive (drafted \
2026-08-29; awaiting ratification). A git object enters the store as \
content: the payload IS the loose-object preimage — ",
        .code "\"<type> <length>\\0\" ++ content",
        .text " — so ", .code "sha1(payload)",
        .text " is the object's git id while the node's own address is \
the digest of its canonical pre-image. One node, two identities, \
neither declared in a field and both derivable by any host from the \
bytes alone. That dual identity is what makes the sort a versioning \
primitive rather than an import format: a commit admitted this way \
carries its git-side name with it, so pinning a dependency by revision \
and pinning it by content address name the same bytes, and the estate \
can hold a version without leaving the store. The exemplar is the ",
        .code "git-pin-commit", .text " vector — the lean4-tree-sitter \
pin commit as one node, its payload's SHA-1 the commit id it names. \
References are empty in v0: git's internal SHA-1 edges (a commit's tree \
and parents, a tree's entries) stay inside the payload rather than \
becoming typed CAS edges, exactly as the schema sort's ", .code "$defs",
        .text " graph does. Promoting them is the named follow-up, and \
is what would turn a pinned object into a walkable history."] },
    { id := .sort .agent, name := "agent", status := .core
      exemplar := none
      forms := [
        { name := "genesis", witness := .node wAgentGenesis
          fields := []
          refs := .fixed []
          meaning := "An agent chain's first step: no attestation, no edges." },
        { name := "agent", witness := .node wAgent
          fields := [
            { name := "attestation", enc := .opaque,
              meaning := "the executor's claim about the step it took, uninterpreted — a claim, never a proof" }]
          refs := .fixed [
            { name := "context", expects := .context,
              meaning := "the folded context the step was taken over" },
            { name := "output", expects := .value,
              meaning := "the answer the step recorded" },
            { name := "prev", expects := .agent,
              meaning := "the step before it, or the chain's genesis" }]
          meaning := "One agent step: the attestation, the context it folded, the answer it recorded, and the step before it." }]
      notes := [.text "The ATTRIBUTION anchor. Ratified 2026-08-30 \
(decision 40) for the three-edge form the agent language already \
wrote — ", .code "CasExamples.AgentStep",
        .text " admits exactly three nodes per step and the third was a \
journal ", .code "entry", .text " over row ", .code "0x0C",
        .text ". Riding that tag cost the thing the sort exists for: \
references type-check at tag granularity, so an edge expecting an \
AGENT specifically was unspellable, and \"who did this\" could not be \
asked of the store as a typed walk. The form is unchanged by the move \
— attestation, context, output, prev — and only the tag its ", .code "prev",
        .text " edge demands changed, from the journal's to its own, \
which is what makes an agent chain a chain of agent steps rather than a \
branch of the journal. Two forms, on the ", .code "entry",
        .text " precedent: a chain whose links point backwards has to \
bottom out, and ", .code "agent.genesis", .text " is where. Greenfield \
made the migration free — the estate held no stored node at this form, \
so nothing was re-authored."] },
    { id := .sort .query, name := "query", status := .core
      exemplar := none
      forms := [
        { name := "query", witness := .node wQuery
          fields := [
            { name := "spec", enc := .opaque,
              meaning := "the query spec's bytes — canonical JSON at the layer above, opaque here" }]
          refs := .fixed []
          meaning := "A query spec as content: the spec's bytes, and no edges." }]
      notes := [.text "The SPEC plane — a query as content. Ratified \
2026-08-30 (decision 40). A leaf, deliberately: a spec names the \
classifiers it runs by DERIVED NAME, the strings ", .code "names.json",
        .text " carries, and a name is not an address, so there is \
nothing here for an edge to point at. What earned the row is the other \
direction — a ", .code "result", .text " binds spec-to-query by a \
typed edge, annotations are written about queries, and related-edges \
run query to query; every one of those is a reference TO a spec, and a \
reference demands one tag."] },
    { id := .sort .result, name := "result", status := .core
      exemplar := none
      forms := [
        { name := "result", witness := .node wResult
          fields := [
            { name := "mark", enc := .beU32,
              meaning := "the word index the answer was computed at — the zero-based mark a non-monotone answer carries on its face" }]
          refs := .free "member"
            "The SPEC first — edge 0 expects the query tag, and is the \
spec this node answers — then one edge per member of the answer, in \
fold order, any number of them. The discipline is free rather than a \
slot list because an answer's length is not a manifest fact, and the \
manifest's two disciplines cannot state a fixed head and a free tail \
in one form: .fixed is checked as exact list equality against the \
witness and .free names no slots at all. So the leading slot is stated \
as this law instead of as a table, and what the law adds to the free \
one is that edge 0 is the spec. Every member edge's expected tag must \
resolve through Ty.ofTag, exactly as a context's must."
          meaning := "A materialized answer: the mark it was computed at, the spec it answers, and one edge per member." }]
      notes := [.text "The ANSWER plane — a materialized result set. \
Ratified 2026-08-30 (decision 40). The memoization law falls out of \
the shape rather than being enforced beside it: the node's preimage IS \
spec plus mark plus members, so the same spec at the same mark over \
the same members is the same address, and a duplicate put is the \
identity. This is also the INDEX kind the naming inventory anticipates \
— a materialized page of a query, which is what a reverse-ref index \
is a family of. A result is a REFERENCED thing (later steps hand \
result handles onward, annotations are written about answers), which \
is what earned it a tag rather than a composite."] },
    { id := .sort .schema, name := "schema", status := .revision1
      exemplar := some "schema-vector-document"
      forms := [
        { name := "schema", witness := .tree ⟨.schema, wSchema⟩
          fields := [
            { name := "bytes", enc := .opaque,
              meaning := "the schema's canonical bytes, opaque at this layer" }]
          refs := .fixed []
          meaning := "A canonical schema as content." }]
      notes := [.text "Payload = the canonical JSON envelope of \
Effect's persistent ", .code "SchemaRepresentation",
        .text " document; references remain empty. Revision 0's tagged \
projection is read-compatible. The cross-runtime byte pin is gated; the \
revision-1 byte theorem remains pending. Typed schema-to-schema edges (",
        .code "$defs", .text " as real CAS references) are the named \
follow-up."] }
  ]
  closing := [
    [.text "Rows 1 and 11–13 were previously marked \"illustrative\"; \
ruling 2 ratifies all seven data sorts into core. Consumer extension \
(profiles, the GrammarSpec registration pattern) is a named follow-up, \
not retrofitted here; a new tag enters only through the grill with a \
real consumer."],
    [.text "Rows 14 and 15 carried a reconciliation debt on purpose: \
they were used by ", .code "Cas/Lang/Defun.lean", .text " but were NOT ",
     .code "Ty", .text " constructors, and ", .code "Defun.lean",
     .text " guarded both literals against this table AND guarded that ",
     .code "Ty.ofTag", .text " still REFUSED both tags. That debt is \
DISCHARGED: the rows were ratified 2026-08-29 and are the ",
     .code "Ty.step", .text " and ", .code "Ty.cont",
     .text " sorts. The refusal guards went red exactly as designed and \
were removed with the reservation they pinned; the two names survive in ",
     .code "Defun.lean", .text " as abbreviations of the sorts' own \
tags, so neither number is now written twice."],
    [.text "Rows 65, 73, 81 and 82 are decision 40's, ratified \
2026-08-30 as ONE batch and not four rulings: ", .code "annotation",
     .text " (the meaning column, promoted at the working tag it was \
already riding, so nothing stored moved), ", .code "agent",
     .text " (the attribution anchor, taken off ", .code "entry",
     .text "'s tag), ", .code "query", .text " (specs as content) and ",
     .code "result", .text " (materialized answers). The batch scopes \
the growth discipline rather than repealing it — one event, grilled \
once, and the stillness resumes with it. ", .code "text",
     .text " was refused from the batch the same day: no logged vision \
sentence orders collaborative document editing, and the CRDT run's \
self-referencing parent pointer forces a tag only if a buffer is ever \
commissioned. None of the four has a ", .code "Tree",
     .text " constructor, and none needs one — their writers sit at the \
node layer, exactly as ", .code "context", .text "'s does."],
    [.text "No row is RESERVED today, and no row is formless. The \
registry keeps both notions anyway — a row id that is a bare tag, a \
status that says so, and the guards that tie the two together — \
because the next reservation should cost a red build rather than a \
silent drift, and the machinery is cheaper kept than re-derived."]
  ]

/-! ## The completeness guards

The house registry discipline, plus the witness checks that make the
stated layouts derived rather than transcribed. -/

/-- Every (tag, form) pair the manifest declares. -/
private def formsOf (m : Manifest) : List (UInt8 × Form) :=
  m.rows.flatMap fun r => r.forms.map fun f => (r.id.wireTag, f)

/-- The row ids, in registry order. -/
def Manifest.ids (m : Manifest) : List RowId := m.rows.map Row.id

/-- The table is complete: every sort of the grammar has a row. -/
theorem manifestV0_rows_complete (t : Ty) :
    RowId.sort t ∈ manifestV0.ids := by
  cases t <;> decide

-- A sort row's name is the sort's own spelling.
#guard manifestV0.rows.all fun r =>
  match r.id with
  | .sort t => r.name == t.sortName
  | .reserved _ => true

-- One row per tag, one row per name.
#guard decide ((manifestV0.ids.map RowId.wireTag).Nodup)
#guard decide ((manifestV0.rows.map Row.name).Nodup)

-- Rows agree with `ofTag`: a sort row round-trips its tag, and a
-- reserved row is exactly a tag `ofTag` still refuses. The reserved
-- half is unpopulated since 14/15 were ratified; it is what a future
-- reservation is held to, and what turns its ratification red.
#guard manifestV0.rows.all fun r =>
  match r.id with
  | .sort t => decide (Ty.ofTag r.id.wireTag = some t)
  | .reserved tag => (Ty.ofTag tag).isNone

-- Reserved rows are exactly the rows with reserved status.
#guard manifestV0.rows.all fun r =>
  (match r.id with | .reserved _ => true | .sort _ => false) == r.status.isReserved

-- A row carries no form exactly when it is RESERVED. No row is
-- reserved today (14/15 were the last, ratified 2026-08-29), so this
-- reads: every row states a form, whether the grammar has a
-- constructor for it or not. The guard is kept for the next
-- reservation, which it holds to the same bargain.
#guard manifestV0.rows.all fun r => r.forms.isEmpty == r.status.isReserved

-- Elaboration stamps the row's tag. This is what ties a form to its
-- row: the witness's own sort is not read anywhere, so a `.node`
-- witness is held to exactly the standard a `.tree` one is.
#guard (formsOf manifestV0).all fun (tag, f) => f.node.tag == tag

-- Every witness writes the scheme version the grammar declares.
#guard (formsOf manifestV0).all fun (_, f) => f.node.version == schemeVersion

-- The declared reference discipline IS the witness's. Under `.fixed`,
-- exact list equality: those slots, in that order. Under `.free`, THE
-- LAW — every edge resolves through `Ty.ofTag`, so a free node may not
-- carry an unratified tag. Nothing checked this before.
#guard (formsOf manifestV0).all fun (_, f) =>
  match f.refs with
  | .fixed slots =>
      f.node.refs.map Ref.expectedTag == slots.map fun s => s.expects.wireTag
  | .free _ _ =>
      f.node.refs.all fun r => (Ty.ofTag r.expectedTag).isSome

-- A free discipline EXHIBITS its law rather than passing it vacuously:
-- its witness carries at least one edge for the check above to read.
#guard (formsOf manifestV0).all fun (_, f) =>
  match f.refs with
  | .fixed _ => true
  | .free _ _ => !f.node.refs.isEmpty

-- A fixed-width layout states the witness's exact payload size.
#guard (formsOf manifestV0).all fun (_, f) =>
  match f.payloadBytes with
  | some n => f.node.payload.length == n
  | none => true

-- A variable layout states a real lower bound.
#guard (formsOf manifestV0).all fun (_, f) =>
  decide (f.payloadMinBytes ≤ f.node.payload.length)

-- The envelope is the codec's, not a retelling: two lead bytes, a
-- framed payload, a 32-bit count, then fixed-width reference records.
#guard (Cas.encodeNode ⟨0, 1, [7, 7, 7], []⟩).length
  == 1 + 1 + (4 + 3) + 4
#guard (Cas.encodeRef ⟨0, noAddr⟩).length == envelopeV0.refRecordBytes
#guard (Cas.encodeNode ⟨0, 1, [], [⟨9, noAddr⟩, ⟨9, noAddr⟩]⟩).length
  == 1 + 1 + 4 + 4 + 2 * envelopeV0.refRecordBytes

/-! ## The machine projection -/

/-- Two uppercase hex digits with the `0x` prefix — how a tag is
spelled in the estate's prose (payload hex stays lowercase; a tag is a
registry row, not payload bytes). -/
def hexTag (t : UInt8) : String :=
  "0x" ++ String.ofList ((Cas.hexS [t]).toList.map Char.toUpper)

def Field.toValue (d : Field) : Cas.Json.Value :=
  .obj ([
    ("name", .str d.name),
    ("encoding", .str d.enc.wire),
    ("minBytes", .nat d.enc.minBytes),
    ("meaning", .str d.meaning)] ++
    (match d.enc.bytes with
      | some n => [("bytes", Cas.Json.Value.nat n)]
      | none => []))

def Slot.toValue (s : Slot) : Cas.Json.Value :=
  .obj [
    ("name", .str s.name),
    ("expects", .str s.expects.sortName),
    ("expectsTag", .nat s.expects.wireTag.toNat),
    ("expectsTagHex", .str (hexTag s.expects.wireTag)),
    ("meaning", .str s.meaning)]

/-- The discipline as a JSON value: its kind always, and under `.free`
the name and the law the edges satisfy. `refs` beside it stays the slot
array a fixed discipline names, and is empty under a free one — a
reader that only knew `refs` would read a free form as edgeless, which
is why the key exists. -/
def RefDiscipline.toValue : RefDiscipline → Cas.Json.Value
  | .fixed _ => .obj [("kind", .str "fixed")]
  | .free name meaning =>
      .obj [
        ("kind", .str "free"),
        ("name", .str name),
        ("meaning", .str meaning)]

def Form.toValue (f : Form) : Cas.Json.Value :=
  .obj ([
    ("name", .str f.name),
    ("meaning", .str f.meaning),
    ("payloadMinBytes", .nat f.payloadMinBytes),
    ("fields", .arr (f.fields.map Field.toValue)),
    ("discipline", f.refs.toValue),
    ("refs", .arr (f.refs.slots.map Slot.toValue))] ++
    (match f.payloadBytes with
      | some n => [("payloadBytes", Cas.Json.Value.nat n)]
      | none => []))

def Row.toValue (r : Row) : Cas.Json.Value :=
  .obj [
    ("name", .str r.name),
    ("tag", .nat r.id.wireTag.toNat),
    ("tagHex", .str (hexTag r.id.wireTag)),
    ("status", .str r.status.wire),
    ("reserved", .bool r.status.isReserved),
    ("exemplar", match r.exemplar with
      | some v => .str v
      | none => .null),
    ("forms", .arr (r.forms.map Form.toValue)),
    ("notes", .str r.notes.plain)]

def Envelope.toValue (e : Envelope) : Cas.Json.Value :=
  .obj [
    ("fields", .arr (e.fields.map Field.toValue)),
    ("refRecordBytes", .nat e.refRecordBytes),
    ("meaning", .str e.meaning.plain)]

/-- The manifest as a JSON value (keys sort at render, per the house
printer). -/
def Manifest.toValue (m : Manifest) : Cas.Json.Value :=
  .obj [
    ("manifestVersion", .nat m.manifestVersion),
    ("grammar", .str m.grammar),
    ("scheme", .nat m.scheme),
    ("title", .str m.title),
    ("preamble", .arr (m.preamble.map fun p => .str p.plain)),
    ("envelope", m.envelope.toValue),
    ("sorts", .arr (m.rows.map Row.toValue)),
    ("closing", .arr (m.closing.map fun p => .str p.plain))]

/-! ## The human projection

`REGISTRY.md` itself: the registry is this manifest's Markdown
rendering, generated beside the JSON and byte-gated like it. There is
no second human spelling of the sort table anywhere in the estate. -/

private def bytesCell : Option Nat → Cell
  | some n => ⟨[.text (toString n)]⟩
  | none => ⟨[.text "variable"]⟩

private def fieldTable (fields : List Field) : Block :=
  .table {
    headers := #v["field", "encoding", "bytes", "meaning"]
    rows := fields.map fun d =>
      #v[⟨[.code d.name]⟩, ⟨[.code d.enc.wire]⟩, bytesCell d.enc.bytes,
         ⟨[.text d.meaning]⟩] }

private def slotTable (slots : List Slot) : Block :=
  .table {
    headers := #v["reference", "expects", "tag", "meaning"]
    rows := slots.map fun s =>
      #v[⟨[.code s.name]⟩, ⟨[.code s.expects.sortName]⟩,
         ⟨[.code (hexTag s.expects.wireTag)]⟩, ⟨[.text s.meaning]⟩] }

/-- How a form's reference discipline reads in one line, and what it
puts under the bullets: a fixed discipline renders its slot table, a
free one states its law in prose because there is no list to table. -/
private def disciplineLine : RefDiscipline → String
  | .fixed [] => "none"
  | .fixed slots => String.intercalate ", " (slots.map fun s => s.name)
  | .free name _ => s!"free — any number of {name} edges"

private def disciplineBlocks : RefDiscipline → List Block
  | .fixed [] => []
  | .fixed slots => [slotTable slots]
  | .free name meaning =>
      [.p [.text "Free reference discipline: any number of ",
           .code name, .text " edges, no slot list. ", .text meaning]]

private def formBlocks (row : Row) (f : Form) : List Block :=
  [.h3 s!"{row.name}.{f.name}",
   .p [.text f.meaning],
   .ul [
     [.text "payload: ",
      .text (match f.payloadBytes, f.payloadMinBytes with
        | some n, _ => s!"{n} bytes"
        | none, 0 => "variable"
        | none, m => s!"variable, at least {m} bytes")],
     [.text "references: ", .text (disciplineLine f.refs)]]] ++
  (if f.fields.isEmpty then [] else [fieldTable f.fields]) ++
  disciplineBlocks f.refs

/-- The registry document — `REGISTRY.md`. -/
def Manifest.toMarkdown (m : Manifest) : String :=
  let formless := m.rows.filter (·.forms.isEmpty)
  render <|
    [.h1 m.title,
     .p [.text "Manifest version ", .code (toString m.manifestVersion),
         .text " — the version the JSON projection carries in its ",
         .code "manifestVersion", .text " key."]] ++
    m.preamble.map Block.p ++
    [.h2 "The node envelope",
     .p m.envelope.meaning,
     fieldTable m.envelope.fields,
     .h2 "The sorts",
     .table {
       headers := #v["Tag (dec)", "Tag (hex)", "Sort", "Status", "Exemplar", "Notes"]
       rows := m.rows.map fun r =>
         #v[⟨[.text (toString r.id.wireTag.toNat)]⟩,
            ⟨[.code (hexTag r.id.wireTag)]⟩,
            ⟨[.code r.name]⟩,
            ⟨[.text r.status.wire]⟩,
            ⟨[match r.exemplar with
               | some v => .code v
               | none => .text "—"]⟩,
            ⟨r.notes⟩] }] ++
    m.closing.map Block.p ++
    [.h2 "Payload layout and reference discipline",
     .p [.text "One section per node form, read off a witness term — a \
grammar term of ", .code "Cas/Grammar/Tree.lean", .text ", or the node \
itself for a sort the grammar has no constructor for. ",
         .text (if formless.isEmpty then
             "Every row states a form."
           else
             "Rows with no form: " ++
             String.intercalate ", " (formless.map Row.name) ++
             " — see their notes above.")]] ++
    (m.rows.flatMap fun r => r.forms.flatMap (formBlocks r))

/-- The rendered projections — the bytes of the generated artifacts. -/
def document : String := Cas.Json.document manifestV0.toValue
def registry : String := manifestV0.toMarkdown

end Cas.Grammar
