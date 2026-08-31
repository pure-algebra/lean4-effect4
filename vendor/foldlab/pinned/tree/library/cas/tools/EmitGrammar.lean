import Cas.Grammar.Manifest
import Cas.Lang.Defun
import Cas.Core.Refs
import Cas.Schema.Annotation
import Cas.Schema.Codec.References
import Cas.Backend.Ts
import Gate

/-!
# The grammar-manifest emitter — `lake exe emitgrammar`

Emits four projections of the grammar manifest (the R11 interchange
document of the data grammar) from `Cas.Grammar.manifestV0`: the JSON
the front ends consume, through the house manifest printer;
`REGISTRY.md`, the human kind-tag registry, which is this manifest's
Markdown rendering and nothing else; `kindTags.ts`, the TypeScript
door's refusal set, which is the same table's tag column; and
`names.json`, the derived-name inventory, which is every name the
grammar gives a column, a block, a field, or an edge, mechanically
joined. `--check` is the byte-identity gate over all four.

The registry is regenerated IN PLACE rather than beside the JSON: the
grammar's human surface already has a home at the library root, and a
second Markdown spelling of the sort table is exactly what closing
ruling-queue item 26 was about. The TypeScript projection rides beside
the JSON, so a re-pointed target moves the pair together.

TWO MORE FIXTURES, for the workbench. `kindTags.ts` and `names.json` are
emitted a second time into `experiments/workbench/src/generated/`,
because the front end is a separate package that may not import the
effects package's copies — the two name different `effect` versions, and
that split is unruled (`experiments/workbench/README.md`, C6 pending). A
front end spelling a wire tag or a derived name by hand is exactly what
that README refuses, so the copies are emitted from this same manifest
in this same run. Their targets are FIXED rather than derived from the
positional override: they are mirrors in another package, not siblings
in one generated directory.

This root is also where the grammar manifest and the `Lang` layer meet,
so the cross-layer pins live here — the manifest cannot import `Defun`
(layer 3 sits above layer 2), but the tool that renders it can, and
`check:cas` builds it. The pins used to hold the RESERVED rows against
`Defun`'s literals; since those rows were ratified (2026-08-29) they
hold the `step` and `cont` witnesses against `Defun`'s own encoders,
which is the same bargain one rung stronger.
-/

namespace EmitGrammarMain

open Cas.Grammar
open Cas.Backend.Ts

/-- The reserved rows — the tags the registry holds outside `Ty`.
EMPTY since 2026-08-29: rows 14/15 were the last two, and they are now
the `step` and `cont` sorts. The definition and its guard stay for the
next reservation, which they hold to the same bargain. -/
private def reservedTags : List UInt8 :=
  (manifestV0.rows.filter (·.status.isReserved)).map (·.id.wireTag)

#guard reservedTags == []

/-! ## The program sorts, pinned across the layering

`Cas/Grammar/Manifest.lean` may not import `Cas/Lang/Defun.lean` —
layer 3 sits above layer 2 — so the manifest's `step` and `cont`
witnesses spell the encoder's layout by hand. This root is where the
two meet, so this is where the hand-spelling is held to the encoder:
the witness node of each form must be the node `Defun` actually writes.
That closes the loop the layering forbids stating in either module,
exactly as the reserved-tag guard above used to.

`noAddr` matches `Manifest.lean`'s private witness address; a table's
line addresses are `H`-determined and the guard reads only tag,
version, payload, and expected tags. -/

private def noAddr : Cas.Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- The put line the `step.put` witness states. -/
private def wLinePut : Cas.Lang.PLine :=
  .put Cas.Grammar.schemeVersion Ty.value.wireTag [7, 7, 7]
    [(Ty.value.wireTag, .ans 0)]

/-- The load line the `step.load` witness states. -/
private def wLineLoad : Cas.Lang.PLine := .load (.ans 0)

/-- The form of a row, by row name and form name. -/
private def formNamed (row form : String) : Option Form :=
  (manifestV0.rows.find? (·.name == row)).bind
    (·.forms.find? (·.name == form))

private def witnessOf (row form : String) : Option Cas.Node :=
  (formNamed row form).map Form.node

-- The `step` forms ARE `Cas.Lang.encodeLine`'s nodes.
#guard witnessOf "step" "put" == some (Cas.Lang.encodeLine wLinePut)
#guard witnessOf "step" "load" == some (Cas.Lang.encodeLine wLineLoad)

-- The `cont` form IS `Cas.Lang.tableNode`'s node, up to the address
-- the manifest's constant `H` writes into the one edge it exhibits.
#guard witnessOf "cont" "cont"
  == some (Cas.Lang.tableNode (fun _ => noAddr) [wLinePut])

/-! ## The annotation sort, pinned across the same layering

`Cas/Grammar/Manifest.lean` may not import `Cas/Schema/Annotation.lean`
either — the annotation kind is written through the schema plane's
projection, which sits above the grammar — so the `annotation` witness
spells that projection's output by hand, exactly as the program
witnesses spell `Defun`'s. This root imports both planes, so this is
where the hand-spelling is held to the projection: the witness node must
be the node `Cas.Schema.putNode` actually writes at this kind, envelope
payload and edge order included.

The pinned annotation is `pinLink`'s shape with RATIFIED arms — the
subject on the program plane, the value's reference on the git plane —
because the manifest's free-discipline guard reads every witness edge
through `Ty.ofTag`, and the union's `system` and `exchange` arms sit at
working tags with no registry row. That divergence is stated in the
row's own law rather than hidden: a real annotation may carry an edge at
a working tag, and the row says so.

The `agent` row has no pin here and cannot: its writer is
`CasExamples.AgentStep`, and `CasExamples` is a LEAF the strata gate
holds to being imported by nothing. Its witnesses are held the way
`context`'s is — by the consumer's own build, and by the row's notes
naming it. -/

/-- The annotation the `annotation.annotation` witness states: a typed
reference value, on the two ratified planes. -/
private def wAnnotationPin : Cas.Schema.Annotation :=
  { key := "foldlab/view"
  , subject := .program ⟨noAddr⟩
  , value := .ref (.git ⟨noAddr⟩) }

-- The `annotation` form IS `Cas.Schema.putNode`'s node at this kind.
#guard witnessOf "annotation" "annotation"
  == Cas.Schema.putNode Cas.Grammar.schemeVersion
      Cas.Schema.pinAnnotationKindTag Cas.Schema.pinAnnotationRevision
      wAnnotationPin

-- The kind's everyday word IS the registry's name for its row. The
-- annotation plane emitted that word because it had no row to give one;
-- since decision 40 it has, and the two spellings meet here rather than
-- drifting.
#guard Cas.Schema.pinAnnotationKindWord == Ty.annotation.sortName

-- And the tag the plane's pins ride IS the row's. Both directions of
-- the promotion, held: the sort table gives the byte, and the schema
-- plane reads it rather than choosing one.
#guard Cas.Schema.pinAnnotationKindTag == Ty.annotation.wireTag

/-! ## The TypeScript door

`Cas.value` mints caller-defined projections, and a projection at a tag
the registry already gives a row would hand that row's plane a second
public interpretation. The refusal set is therefore not a hand list in
TypeScript: it is this column. A row ratified in Lean widens the door on
the next regeneration, and the byte gate says so when it has not been
run. -/

/-- Every tag the registry gives a row — ratified sorts and reserved
code points alike. This IS the door's refusal set. -/
private def doorTags : List UInt8 := manifestV0.ids.map RowId.wireTag

-- Every row reaches the door; nothing is dropped between the table and
-- the emitted column.
#guard doorTags.length == manifestV0.rows.length

-- The six tags the substrate audit found undefended (B-A): `value`,
-- `file`, `entry`, `context`, `step`, `cont`. A door that stops
-- refusing any of them is the aliasing hole reopening.
#guard [1, 11, 12, 13, 14, 15].all (doorTags.contains ·)

private def tagOf (r : Row) : Expr := .int (Int.ofNat r.id.wireTag.toNat)

private def rowExpr (r : Row) : Expr :=
  .objectML [("name", .str r.name), ("tag", tagOf r),
    ("reserved", .bool r.status.isReserved)]

/-- The row type the generated table is read at. A raw block: these are
TypeScript declarations, not expressions, and the fragment the printer
carries is deliberately expression-only. -/
private def typeBlock : String :=
  "/** One registry row's tag surface: the sort's registry name, its\n" ++
  " * wire kind tag, and whether the row is RESERVED — a code point the\n" ++
  " * registry holds outside `Ty` — rather than a ratified sort. No row\n" ++
  " * is reserved today; both kinds are refused identically at the door,\n" ++
  " * so the flag is a fact about the registry, never a door policy. */\n" ++
  "export interface KindTagRow {\n" ++
  "  readonly name: string\n" ++
  "  readonly tag: number\n" ++
  "  readonly reserved: boolean\n" ++
  "}"

private def decls : List Decl := [
  .raw typeBlock,
  .const {
    name := "KindTagRows",
    type := some "ReadonlyArray<KindTagRow>",
    doc := ["Every registry row, in registry order — the table",
      "`REGISTRY.md` renders for humans, as data."],
    value := .arr (manifestV0.rows.map rowExpr) },
  .const {
    name := "KindTagsByName",
    doc := ["The registry's wire tags by sort name: how a consumer names",
      "one row without repeating its number."],
    value := .objectML (manifestV0.rows.map fun r => (r.name, tagOf r)) },
  .const {
    name := "GrammarKindTags",
    type := some "ReadonlyArray<number>",
    doc := ["THE door's refusal set: every tag the registry gives a row,",
      "in registry order. `Cas.value` refuses each of these, so a",
      "caller-defined projection can never give a registry row a second",
      "public interpretation."],
    value := .arr (manifestV0.rows.map tagOf) }
]

/-- The lane's emitted header, shared by all three machine
projections. `schemaVersion` opens at the `manifestVersion` the
manifest and the name inventory already declare, and that field stays
in both for one release beside the header that now carries it.

`REGISTRY.md` is not headed: it is the table's rendering FOR PEOPLE,
and the JSON beside it is where a machine reads the provenance. -/
def emitted : Gate.Emitted where
  schemaVersion := manifestV0.manifestVersion
  emitter := "emitgrammar"
  module := "library/cas/tools/EmitGrammar.lean"

/-- The door's table, at whichever header its copy is read under. The
`decls` are the SAME value for every copy — one manifest, lowered once —
so two renderings of this table can differ only in the prose that says
where each one lives and why, never in a row. -/
private def moduleWith (header : List String) : Module where
  header := header ++ emitted.headerLines
  imports := []
  decls := decls

private def module : Module := moduleWith [
    "GENERATED — do not edit. THE KIND-TAG REGISTRY, as data: every wire",
    "tag `Cas.Grammar.manifestV0` gives a row, emitted from",
    "`library/cas/Cas/Grammar/Manifest.lean` by `lake exe emitgrammar`;",
    "regeneration is byte-identity-gated (`--check`, wired into",
    "`check:cas`). `REGISTRY.md` is the same table's human rendering and",
    "`manifest.json` its machine one.",
    "",
    "`src/internal/kindTags.ts` is the door's projection of this file.",
    "`Cas.value` refuses every tag listed here, which is what stops a",
    "caller-defined projection from aliasing a kind plane the library",
    "already reads. A RESERVED row is a code point the registry holds",
    "outside `Ty`; none is today (14 and 15 were ratified as the `step`",
    "and `cont` sorts on 2026-08-29). Reserved or ratified, a row is",
    "refused identically, because a tag with a second public",
    "interpretation is the same hole either way — so this door's",
    "membership did not move when those two rows did."
  ]

def rendered : String := Render.module house0 module

/-- The workbench's copy of the same table. The front end is a separate
package that may not import the effects package's rendering — the two
name different `effect` versions, and that split is unruled
(`experiments/workbench/README.md`, C6 pending) — so it reads the
manifest's own projection rather than a transcription of it.

The header quotes the obligation that makes it a fixture rather than a
hand copy, because the file is where somebody tempted to edit it will be
standing. -/
private def workbenchModule : Module := moduleWith [
  "GENERATED — do not edit. THE KIND-TAG REGISTRY, as data: every wire",
  "tag `Cas.Grammar.manifestV0` gives a row, emitted from",
  "`library/cas/Cas/Grammar/Manifest.lean` by `lake exe emitgrammar`;",
  "regeneration is byte-identity-gated (`--check`, wired into",
  "`check:cas`). `REGISTRY.md` is the same table's human rendering and",
  "`grammar/names.json` beside this file the inventory of every name the",
  "grammar derives.",
  "",
  "THE WORKBENCH'S COPY, and the law it exists under —",
  "`experiments/workbench/README.md`: «any surface the store language",
  "already describes must be generated, never typed by hand». The kind",
  "tags are such a surface: a front end that spells a wire tag by hand",
  "is a second, unregistered opinion about what a stored node means. The",
  "rows below are the SAME Lean values",
  "`library/effects/src/cas/generated/grammar/kindTags.ts` carries,",
  "printed by the same printer in the same run; only this header",
  "differs, and it differs because the two files are read by different",
  "people.",
  "",
  "A RESERVED row is a code point the registry holds outside `Ty`; none",
  "is today (14 and 15 were ratified as the `step` and `cont` sorts on",
  "2026-08-29). Reserved or ratified, a row is refused identically at",
  "the library's door, because a tag with a second public interpretation",
  "is the same hole either way."
]

def workbenchTagsRendered : String := Render.module house0 workbenchModule

/-! ## The reference discipline's reserved keys

A sort table says which edges a form carries; it does not say how a
reference SPELLS itself inside a payload, and that spelling is two
reserved keys with two Lean homes. `src/internal/refMarkers.ts` used
to open with both of them typed out — the last two hand-copied
constants on the value plane's wire, and the pair a payload's whole
identity turns on, since the walks refuse rather than escape a
collision with either.

They are not merely re-typed here. `refKey` is the model's own
constant, and the sentinel key is READ OFF the codec that writes it:
`Cas.Schema.encRef` builds a one-key object, and that key is the
answer. Nothing in this section spells a `$`. -/

/-- The marker key: what the k-th reference looks like in a stored
payload, from the model's own `Cas.refKey`. -/
private def markerKey : String := Cas.refKey

/-- The sentinel key, read off the codec rather than spelled: the one
object key `Cas.Schema.encRef` writes. `none` is unreachable — the
codec's arm is a single-field object — and the guard below is what
makes a change to it a build failure rather than an empty constant. -/
private def sentinelKey? : Option String :=
  match Cas.Schema.encRef 0 noAddr with
  | .obj [(k, _)] => some k
  | _ => none

#guard sentinelKey?.isSome

private def sentinelKey : String := sentinelKey?.getD ""

-- The two keys are distinct and non-empty: they are what the walks
-- discriminate ON, so one being the other — or being nothing — would
-- collapse the encode side into the decode side's refusal.
#guard markerKey != sentinelKey
#guard !markerKey.isEmpty && !sentinelKey.isEmpty

private def markerModule : Module where
  header := [
    "GENERATED — do not edit. THE RESERVED PAYLOAD KEYS of the",
    "typed-reference law (CAS-005): the key a stored payload spells a",
    "reference with, and the key an encode-side value carries one as",
    "before the walk assigns indexes — emitted from",
    "`library/cas/Cas/Core/Refs.lean` and",
    "`library/cas/Cas/Schema/Codec/References.lean` by",
    "`lake exe emitgrammar`; regeneration is byte-identity-gated",
    "(`--check`, wired into `check:cas`).",
    "",
    "`src/internal/refMarkers.ts` is this file's consumer: the two",
    "walks it carries are written against these keys, and both REFUSE",
    "— never escape — user data that collides with one, because an",
    "escape would invent a second spelling for the same value and",
    "split its content identity. That is why the keys are emitted",
    "rather than agreed: a payload's identity turns on them, and the",
    "two sides of the wire cannot be allowed to disagree about which",
    "two strings they are."
  ] ++ emitted.headerLines
  imports := []
  decls := [
    .const {
      name := "RefMarkerKey",
      doc := ["The marker key. A typed reference appears in a stored",
        "payload as exactly `{<this key>: k}`, where k is the index of",
        "the k-th marker in canonical byte order — indexes forced,",
        "sharing by repeated entries."],
      value := .str markerKey },
    .const {
      name := "RefSentinelKey",
      doc := ["The sentinel key. An encode-side value carries a",
        "reference under this key, as `{id, tag}`, until `markerize`",
        "lowers it to a positional marker and an entry in the node's",
        "reference array. Read off `Cas.Schema.encRef`, the codec that",
        "writes the sentinel, rather than spelled a second time."],
      value := .str sentinelKey }
  ]

def markersRendered : String := Render.module house0 markerModule

/-! ## The derived-name inventory

A front end over this store names things: a COLUMN per sort, a BLOCK
per node form, a FIELD per payload slot, an EDGE per reference. Those
names are not a vocabulary anyone gets to pick — they are the
manifest's own identifiers joined by one separator, and `names.json`
carries that join out so no consumer has to spell a name by hand and
no two consumers can spell one differently.

Nothing below transforms prose, changes casing, or pluralizes: every
string is manifest identifiers concatenated with `sep` and the
identifiers themselves, which is exactly why the inventory cannot name
something the grammar does not have. The guards state that as the
property that makes it true — no identifier carries the separator, so
a derived name splits back into the identifiers it was built from, and
every name sits under the one above it.

A free-discipline form has no slot list, so its edges cannot be
enumerated: there are any number of them and the count is not a
manifest fact. The inventory states the PATTERN instead, under the
discipline's own edge name (`item` for a folded context, `line` for a
table), with the index left as the hole the conventions key names. -/

/-- The separator the naming law joins identifiers with, stated once:
every derived name below is this join and nothing else. -/
private def sep : String := "."

/-- The hole a free edge's name carries where its index goes. The
number of edges a free form writes is a fact about a stored node, not
about the grammar, so the inventory names the pattern and leaves this
position open. -/
private def indexHole : String := "<index>"

/-- A derived name: manifest identifiers, joined. THE law — nothing
else in this section builds a string. -/
private def qualified (parts : List String) : String :=
  String.intercalate sep parts

/-- The naming law as data, so a consumer reads it rather than
inferring it from examples. The three shapes here need a coordinate the
manifest does not carry: an instance needs the stored node's address, a
free edge its index, and a node at a tag with no registry row has no
derived name at all — it is spelled by its tag, which is what makes an
unregistered plane visibly unregistered. Each is built by the same join
as the names it describes. -/
private def conventions : Cas.Json.Value :=
  .obj [
    ("separator", .str sep),
    ("instance", .str (qualified ["<sort>", "<form>"] ++ "@<address-hex>")),
    ("freeEdge", .str (qualified ["<sort>", "<form>", "<edge>", indexHole])),
    ("unregistered", .str "tag:0x<tag-hex>")]

/-- A form's block name: its sort, then the form. -/
private def blockName (r : Row) (f : Form) : String := qualified [r.name, f.name]

private def fieldName (r : Row) (f : Form) (d : Field) : String :=
  qualified [blockName r f, d.name]

private def slotName (r : Row) (f : Form) (s : Slot) : String :=
  qualified [blockName r f, s.name]

/-- A free edge's pattern name: the block, the discipline's edge name,
and the index hole. -/
private def freeEdgeName (r : Row) (f : Form) (edge : String) : String :=
  qualified [blockName r f, edge, indexHole]

private def columnValue (r : Row) : Cas.Json.Value :=
  .obj [
    ("name", .str r.name),
    ("tag", .nat r.id.wireTag.toNat),
    ("tagHex", .str (hexTag r.id.wireTag))]

private def blockValue (r : Row) (f : Form) : Cas.Json.Value :=
  .obj [
    ("name", .str (blockName r f)),
    ("column", .str r.name),
    ("meaning", .str f.meaning)]

private def fieldValue (r : Row) (f : Form) (d : Field) : Cas.Json.Value :=
  .obj [
    ("name", .str (fieldName r f d)),
    ("block", .str (blockName r f)),
    ("encoding", .str d.enc.wire),
    ("meaning", .str d.meaning)]

private def slotValue (r : Row) (f : Form) (s : Slot) : Cas.Json.Value :=
  .obj [
    ("name", .str (slotName r f s)),
    ("block", .str (blockName r f)),
    ("expects", .str s.expects.sortName),
    ("expectsTag", .nat s.expects.wireTag.toNat),
    ("meaning", .str s.meaning)]

/-- The pattern entry a free discipline contributes. `free` is what
tells a reader this row stands for any number of edges rather than for
one; the discipline names no sort, so there is no `expects` to state,
and its law is the meaning. -/
private def freeEdgeValue (r : Row) (f : Form) (edge law : String) :
    Cas.Json.Value :=
  .obj [
    ("name", .str (freeEdgeName r f edge)),
    ("block", .str (blockName r f)),
    ("free", .bool true),
    ("meaning", .str law)]

/-- The edge entries one form contributes: its slots under a fixed
discipline, one pattern under a free one. -/
private def edgeValues (r : Row) (f : Form) : List Cas.Json.Value :=
  match f.refs with
  | .fixed slots => slots.map (slotValue r f)
  | .free edge law => [freeEdgeValue r f edge law]

private def edgeNamesOf (r : Row) (f : Form) : List String :=
  match f.refs with
  | .fixed slots => slots.map (slotName r f)
  | .free edge _ => [freeEdgeName r f edge]

private def columnNames : List String := manifestV0.rows.map Row.name

private def blockNames : List String :=
  manifestV0.rows.flatMap fun r => r.forms.map (blockName r)

private def fieldNames : List String :=
  manifestV0.rows.flatMap fun r =>
    r.forms.flatMap fun f => f.fields.map (fieldName r f)

private def edgeNames : List String :=
  manifestV0.rows.flatMap fun r => r.forms.flatMap (edgeNamesOf r)

-- The inventory covers the manifest exactly: a column per registry
-- row, a block per form. Nothing is dropped between the table and the
-- names projected off it.
#guard columnNames.length == manifestV0.rows.length
#guard blockNames.length == (manifestV0.rows.map fun r => r.forms.length).sum

-- A name is how a consumer ADDRESSES a column, a block, a field, or an
-- edge, so two of anything sharing one is that address going ambiguous.
#guard decide (columnNames.Nodup)
#guard decide (blockNames.Nodup)
#guard decide (fieldNames.Nodup)
#guard decide (edgeNames.Nodup)

-- No identifier carries the separator. THIS is what makes the join
-- reversible — a derived name splits back into exactly the manifest
-- identifiers it was built from — and it is a property of the
-- manifest, not of this tool, so it is checked here rather than
-- assumed.
#guard manifestV0.rows.all fun r =>
  !r.name.contains '.' && r.forms.all fun f =>
    !f.name.contains '.' &&
    (f.fields.all fun d => !d.name.contains '.') &&
    (match f.refs with
     | .fixed slots => slots.all fun s => !s.name.contains '.'
     | .free edge _ => !edge.contains '.')

-- Every name sits under the one above it: a block under its column, a
-- field and an edge under their block. True by construction today; the
-- guard is what keeps it true if the join grows a case.
#guard blockNames.all fun n => columnNames.any fun c => n.startsWith (c ++ sep)
#guard fieldNames.all fun n => blockNames.any fun b => n.startsWith (b ++ sep)
#guard edgeNames.all fun n => blockNames.any fun b => n.startsWith (b ++ sep)

/-- The inventory as a JSON value: the manifest version it projects,
the scheme those tags live in, the naming law, and the law carried out
over every row in registry order. The house printer sorts the keys, so
the spelling here is the reading order, never the bytes. -/
private def namesValue : Cas.Json.Value :=
  emitted.obj [
    ("manifestVersion", .nat manifestV0.manifestVersion),
    ("scheme", .nat manifestV0.scheme),
    ("conventions", conventions),
    ("columns", .arr (manifestV0.rows.map columnValue)),
    ("blocks", .arr (manifestV0.rows.flatMap fun r =>
      r.forms.map (blockValue r))),
    ("fields", .arr (manifestV0.rows.flatMap fun r =>
      r.forms.flatMap fun f => f.fields.map (fieldValue r f))),
    ("edges", .arr (manifestV0.rows.flatMap fun r =>
      r.forms.flatMap (edgeValues r)))]

def namesDocument : String := Cas.Json.document namesValue

/-! ## The fixtures -/

/-- Where the manifest lives in the effects package — the lane's own
knowledge of its artifact. A positional argument overrides it; the
registry rendering is at the library root either way. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/grammar/manifest.json"

-- The manifest's projection is an OBJECT, which is where the header
-- goes; this is what makes `Emitted.onto`'s pass-through arm
-- unreachable here.
#guard match manifestV0.toValue with | .obj _ => true | _ => false

/-- The manifest, headed. The projection is `Cas.Grammar`'s, so the
header is prepended to the value rather than spelled into a field
list. -/
def manifestDocument : String :=
  Cas.Json.document (emitted.onto manifestV0.toValue)

/-- The registry document, at the library root. -/
def registryTarget : System.FilePath := "REGISTRY.md"

/-- The TypeScript door registry, beside the JSON: one generated
directory, so re-pointing the target moves both machine projections. -/
def tagsTargetFor (json : System.FilePath) : System.FilePath :=
  match json.parent with
  | some dir => dir.join "kindTags.ts"
  | none => "kindTags.ts"

/-- The derived-name inventory, beside the JSON and the door: one
generated directory, so a re-pointed target moves all three machine
projections together. -/
def namesTargetFor (json : System.FilePath) : System.FilePath :=
  match json.parent with
  | some dir => dir.join "names.json"
  | none => "names.json"

/-- The reference discipline's reserved keys, beside the door: one
generated directory, so a re-pointed target moves every machine
projection together. -/
def markersTargetFor (json : System.FilePath) : System.FilePath :=
  match json.parent with
  | some dir => dir.join "refMarkers.ts"
  | none => "refMarkers.ts"

/-! ### The workbench's two

FIXED targets, not derived from the effects target the way the three
above are: those are siblings in ONE generated directory, and these are
mirrors in a DIFFERENT package, so a re-pointed effects artifact must
not drag the front end's copies after it. `registryTarget` is the
precedent for a fixture the positional override does not move.

Two of the five, not all five. The front end reads the door's refusal
set and the derived-name inventory — the two projections a surface over
this store needs to name a node and to refuse an unregistered plane.
`manifest.json` and `refMarkers.ts` are not emitted here: the first is
the whole interchange document and nothing in the workbench reads it
yet, and the second is the payload-key law of a codec the front end does
not run. Both are one line each the day something needs them. -/

/-- The workbench's copy of the door's table. -/
def workbenchTagsTarget : System.FilePath :=
  "../../experiments/workbench/src/generated/kindTags.ts"

/-- The workbench's copy of the derived-name inventory. No header prose
distinguishes it — a JSON document's `emitted` header is four fields and
no place to put a sentence — so this file and the effects package's
`grammar/names.json` are BYTE-IDENTICAL, which is the strongest form the
mirror claim takes anywhere in this emitter. -/
def workbenchNamesTarget : System.FilePath :=
  "../../experiments/workbench/src/generated/grammar/names.json"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  let json := target.getD defaultTarget
  let sorts := s!"{manifestV0.rows.length} sorts"
  let namesLabel :=
    s!"{columnNames.length} columns, {blockNames.length} blocks, " ++
      s!"{fieldNames.length} fields, {edgeNames.length} edges — " ++
      "every name the grammar derives"
  return [
    ⟨json, manifestDocument, sorts⟩,
    ⟨registryTarget, Cas.Grammar.registry, s!"{sorts}, the kind-tag registry"⟩,
    ⟨tagsTargetFor json, rendered,
      s!"{doorTags.length} kind tags, the TypeScript door's refusal set"⟩,
    ⟨markersTargetFor json, markersRendered,
      "2 reserved payload keys, the typed-reference law's spelling"⟩,
    ⟨namesTargetFor json, namesDocument, namesLabel⟩,
    ⟨workbenchTagsTarget, workbenchTagsRendered,
      s!"{doorTags.length} kind tags, the workbench's copy"⟩,
    ⟨workbenchNamesTarget, namesDocument, s!"{namesLabel}, the workbench's copy"⟩]

end EmitGrammarMain

def main := Gate.mainAt "lake exe emitgrammar" EmitGrammarMain.fixtures
