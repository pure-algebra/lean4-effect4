import Cas
import Cas.Vectors.Schema
import Cas.Schema.Annotation
import Cas.Schema.Exchange
import Cas.Schema.Notation
import Cas.Backend.Ts
import Cas.Backend.EmitAst
import Gate

/-!
# The schema emitter — `lake exe schemas`

Emits the registered canonical-schema payloads as committed byte
fixtures under `schemas/`, one file per code (the file's bytes ARE the
schema-node payload — the cross-runtime pin surface), plus the
`index.json` tracking manifest. `--check` is the byte-identity gate.

The registry rows are the described wire codes already in service
(the conformance-vector document and index), one notation-authored
sample covering every deriving-reachable constructor, one
hand-composed literal pin covering the `Literal` spellings the
deriving handler does not reach, the sidecar annotation kind
(`Cas.Schema.Annotation`, stipulation S2), the union pin — both
modes, a nested union, and members a sort would reorder, so
order-is-identity is held by the bytes — the DERIVED tagged union,
the generator's own pin for `deriving Described` over constructor
alternatives, the enum pin — both member value rows, orders a sort
would reorder, and the alias TypeScript admits — and the tuple pin,
which carries every shape the grown `Arrays` node reaches beside the
plain array whose bytes must not move, and the exchange kind
(`Cas.Schema.Exchange`) — the stored form of an R15 recording, whose
subject is a tagged union of addressed planes. The TypeScript side asserts
`CanonicalSchema.payloadOf` over the same codes answers these bytes —
the canonical-schema pin the implementation plan holds open.
-/

open Cas.Schema Cas.Schema.Notation

namespace SchemasMain

/- Every constructor the deriving handler can reach, in one
notation-authored kind: null (Unit), bool, int, string, array,
optional field, and a tagged store reference. -/
cas_struct PinSample where
  count : SafeInt
  flag : Bool
  items : List String
  label : String
  note : Option String
  root : StoreRef 9
  unit : Unit

/-- The `Literal` spellings, hand-composed (sorted fields — `WF` by
construction): the deriving handler reaches literals only through
bespoke instances, so the pin carries them explicitly. -/
def literalPin : Ast := .struct [
  ("a", false, .lit .null),
  ("b", false, .lit (.bool true)),
  ("c", true, .lit (.int ⟨-7, by decide⟩)),
  ("d", false, .lit (.str "pinned"))
]

/-- The union spellings, hand-composed (increment C1): both modes and a
nested union, with member lists a sort WOULD REORDER — so
order-is-identity is visible in the committed bytes, not only in a
docstring.

- `choice` — `anyOf` over three keywords, in a written order no
  canonical arrangement would produce;
- `exact` — `oneOf` over two string literals spelled `zebra` before
  `alpha`: any sort of the members changes these bytes, and the fixture
  goes red;
- `nested` — an `anyOf` whose second member is itself a `oneOf`, so the
  no-flattening rule is pinned too (this code is NOT
  `union [null, arr str, bool]`), on an optional field so the union
  rides both key positions. -/
def unionPin : Ast := .struct [
  ("choice", false, .union [.str, .bool, .int] .anyOf),
  ("exact", false, .union [.lit (.str "zebra"), .lit (.str "alpha")] .oneOf),
  ("nested", true, .union [.null, .union [.arr .str, .bool] .oneOf] .anyOf)
]

/-- The enum spellings, hand-composed (increment C4): both member value
rows, member orders a sort WOULD REORDER, and the alias TypeScript
admits — so order-is-identity and value-freedom are held by the
committed bytes and not only by a docstring.

- `direction` — a string enum spelled `Up` before `Down`. Any sort of
  the members changes these bytes and the fixture goes red;
- `level` — a numeric enum carrying a negative member and an ALIAS
  (`Warn` and `Warning` at one value), which `WF` admits because the
  NAME is the member's identity and the value is not;
- `mixed` — one row of each kind, on an optional field, so the enum
  rides both key positions. -/
def enumPin : Ast := .struct [
  ("direction", false, .enum [("Up", .str "Up"), ("Down", .str "Down")]),
  ("level", false, .enum [
    ("Debug", .int ⟨-1, by decide⟩),
    ("Warn", .int ⟨1, by decide⟩),
    ("Warning", .int ⟨1, by decide⟩)]),
  ("mixed", true, .enum [
    ("Name", .str "name"),
    ("Zero", .int ⟨0, by decide⟩)])
]

/-- The tuple spellings, hand-composed (increment C2, the Arrays
completion): every shape the grown `Arrays` node reaches, beside the
plain array whose bytes this increment must NOT move.

- `plain` — `Ast.arr`, unchanged: `{elements:[], rest:[t]}`. It is in
  the fixture so that the one collision this increment could have made
  is held by the bytes — a tuple cannot spell this, because `Ast.tuple`
  takes a first element;
- `pair` — a two-element tuple, positions in a written order a sort
  would reorder;
- `withOptional` — a trailing optional element, so the optionality bit
  rides the wire;
- `withRest` — `Schema.TupleWithRest`: one element and a rest type;
- `nested` — a tuple inside an array inside a tuple, on an optional
  field, so the code rides both key positions. -/
def tuplePin : Ast := .struct [
  ("nested", true,
    .tuple (false, .arr (.tuple (false, .str) [] none)) [(false, .null)] none),
  ("pair", false, .tuple (false, .str) [(false, .int)] none),
  ("plain", false, .arr .str),
  ("withOptional", false, .tuple (false, .int) [(true, .str)] none),
  ("withRest", false, .tuple (false, .str) [] (some .int))
]

/-- The DERIVED tagged union (increment C1, stage 2), authored through
`cas_union`: the `Described` instance is what the deriving handler
generates, so these bytes are the GENERATOR's output and not a
hand-composed code — the fixture is the generator's own pin.

Three constructors at three arities (binary, nullary, and one carrying
an optional field), and the source order — `move`, `stop`, `say` — is
deliberately NOT the code's order. The handler sorts members by tag, so
the payload spells `move`, `say`, `stop`: the one spelling a generator
is allowed to pick, held by the bytes.

`TaggedPin.schemaDiscriminated`, emitted alongside the instance, is the
proof that this code is a discriminated union — which is what makes
`El` of it the member sum and its round trip a theorem. -/
cas_union TaggedPin where
  | move (dx : SafeInt) (dy : SafeInt)
  | stop
  | say (body : String) (note : Option String)

-- The generator's discrimination claim, checked at elaboration; the
-- theorem it is checking is `TaggedPin.schemaDiscriminated`, emitted
-- beside the instance.
#guard TaggedPin.schemaCode.discriminated

/-- The registry: every pinned code in one place. -/
def registry : List (String × Ast) := [
  ("vector-document", Described.code (α := Cas.Vectors.Wire.VectorDocument)),
  ("vector-index", Described.code (α := Cas.Vectors.Wire.VectorIndex)),
  ("pin-sample", PinSample.schemaCode),
  ("literal-pin", literalPin),
  ("annotation", Annotation.schemaCode),
  ("union-pin", unionPin),
  ("tagged-pin", TaggedPin.schemaCode),
  ("enum-pin", enumPin),
  ("tuple-pin", tuplePin),
  ("exchange", Exchange.schemaCode)
]

/-! ## Emission -/

def outDir : System.FilePath := "schemas"

def pathOf (name : String) : System.FilePath := outDir / (name ++ ".json")

def indexPath : System.FilePath := outDir / "index.json"

def addressesPath : System.FilePath := outDir / "addresses.json"

/-- The tool's emitted header for its two MANIFESTS. `schemaVersion`
opens at the `revision` the index already declares —
`Cas.Schema.schemaRevision` — and that field stays for one release
beside the header that now carries it. The address file declared no
version and rides the same one: the two are one manifest pair over one
registry, and versioning them apart would say they can move apart.

The payload files themselves are deliberately NOT headed. Their bytes
ARE the schema node's payload — the pre-image `addresses.json` states
the digest of — so a header there would not describe the artifact, it
would change its identity. -/
def emitted : Gate.Emitted where
  schemaVersion := schemaRevision
  emitter := "schemas"
  module := "library/cas/tools/Schemas.lean"

/-- The schema node a code stores as (kind tag 0x53, envelope payload,
no references) — the same node `CanonicalSchema.nodeOf` builds on the
TypeScript side. -/
def schemaNodeOf (ast : Ast) : Cas.Node :=
  ⟨Cas.Grammar.schemeVersion, Cas.Schema.schemaKindTag,
    ast.payloadBytes.toList, []⟩

/-- The code's content address under the production digest — the
identity the store answers when this schema is admitted. -/
def addressOf (ast : Ast) : String :=
  Cas.hexS (Cas.sha256Addr (Cas.encodeNode (schemaNodeOf ast))).val

/-- THE STORE ADDRESS FILE: every registered schema's content address,
persisted and byte-gated — identity held at the address, not only the
payload. The TypeScript pin suite admits each mirrored code through
the real store and must be answered these exact addresses. -/
def addressesDocument : String :=
  let rows := registry.map fun (name, ast) =>
    Cas.Json.Value.obj [
      ("name", .str name),
      ("address", .str (addressOf ast))]
  Cas.Json.render (emitted.obj [
    ("digest", .str "sha256-scheme0"),
    ("kindTag", .nat Cas.Schema.schemaKindTag.toNat),
    ("schemas", .arr rows)
  ]) ++ "\n"

/-- The tracking manifest: one row per registered code. -/
def indexDocument : String :=
  let rows := registry.map fun (name, ast) =>
    Cas.Json.Value.obj [
      ("name", .str name),
      ("file", .str (name ++ ".json")),
      ("byteLength", .nat ast.payload.toUTF8.size)
    ]
  Cas.Json.render (emitted.obj [
    ("revision", .nat schemaRevision),
    ("schemas", .arr rows)
  ]) ++ "\n"

/-! ## The annotation plane, projected to the CLI (the naming seat)

`cas name` writes annotation nodes, and to do it the CLI must spell
three facts this plane owns: the working tag annotation nodes ride
(`pinAnnotationKindTag`), the name seat's key (`pinName.key`), and the
subject union's arm-to-tag table. Hand copies of those spellings in
TypeScript are drift channels — the CLI lane carried all three by hand
until this projection. The arms are READ OFF
`AnnotationSubject.schemaCode`, the deriving handler's own output, so a
widened union grows the emitted table on the next regeneration and the
byte gate says so until that regeneration has run. -/

/-- The subject arms, read off the code itself: each member of the
`oneOf` is a struct whose `_tag` literal names the arm and whose
`address` field is a reference at the plane's tag. A member of any
other shape is dropped by the match — and the totality guard below is
what makes a drop a build failure rather than a silent narrowing. -/
def subjectArms : List (String × UInt8) :=
  match AnnotationSubject.schemaCode with
  | .union members _ => members.filterMap fun member =>
      match member with
      | .struct [("_tag", _, .lit (.str arm)), ("address", _, .ref tag)] =>
          some (arm, tag)
      | _ => none
  | _ => []

-- Totality over the union: every member is an arm; none was dropped by
-- the shape match above.
#guard (match AnnotationSubject.schemaCode with
  | .union members _ => members.length
  | _ => 0) == subjectArms.length

-- The table is the THIRTEEN planes, at the library's own tag spellings
-- — read off the code and equal to the named constants, so the emitted
-- projection, the union, and the tag definitions cannot drift apart.
-- Five meta/agent planes, the four content planes rider CA-1 admitted,
-- and decision 40's own four sorts. In the deriving handler's canonical
-- member order, which is ascending constructor name.
#guard subjectArms == [
  ("agent", agentKindTag), ("annotation", annotationKindTag),
  ("chunk", chunkKindTag), ("context", contextKindTag),
  ("exchange", exchangeKindTag), ("file", fileKindTag),
  ("git", gitKindTag), ("program", programKindTag),
  ("query", queryKindTag), ("result", resultKindTag),
  ("schema", schemaKindTag), ("system", systemKindTag),
  ("value", valueKindTag)]

-- No `text` arm. The CRDT run was refused from decision 40's batch on
-- vision grounds, so there is no tag for an arm to demand, and an arm
-- would be the sort minted sideways.
#guard !(subjectArms.map Prod.fst).contains "text"

open Cas.Backend.Ts in
private def armExpr (arm : String × UInt8) : Expr :=
  .objectML [("arm", .str arm.1), ("tag", .int (Int.ofNat arm.2.toNat))]

private def armTypeBlock : String :=
  "/** One nameable plane: the subject union's arm name, and the wire\n" ++
  " * kind tag a reference through that arm expects at its target. */\n" ++
  "export interface AnnotationSubjectArm {\n" ++
  "  readonly arm: string\n" ++
  "  readonly tag: number\n" ++
  "}"

open Cas.Backend.Ts in
private def annotationPlaneModule : Module where
  header := [
    "GENERATED — do not edit. THE ANNOTATION PLANE, as data: the tag",
    "annotation nodes ride and the everyday word for it, the revision",
    "they ride, the ratified `foldlab/` key family, and the subject",
    "union's arm-to-tag table, emitted from",
    "`library/cas/Cas/Schema/Annotation.lean` by `lake exe schemas`;",
    "regeneration is byte-identity-gated (`--check`, wired into",
    "`check:cas`). The arm table is read off",
    "`AnnotationSubject.schemaCode` — the deriving handler's output —",
    "so it widens when the union does and never before. Decision 40",
    "widened it by eight arms and ratified the tag, in one event.",
    "",
    "`src/cas/Annotations.ts` is this file's first consumer: it builds",
    "the subject union's arms, exports THE projection annotation nodes",
    "are stored through (`Annotations.Node`, at the tag below), and",
    "reads the system plane's working tag from here rather than",
    "spelling it. `bin/cli/naming.ts` is the second: `cas name` writes",
    "through that projection under `AnnotationNameKey`, and refuses",
    "subjects on planes this table does not carry. `bin/cli/render.ts`",
    "is the third: every everyday kind word the annotation plane owns",
    "is seeded from here, so no rendered surface spells one by hand."
  ] ++ emitted.headerLines
  imports := []
  decls := [
    .raw armTypeBlock,
    .const {
      name := "AnnotationKindTag",
      doc := ["The tag annotation nodes ride (`pinAnnotationKindTag`).",
        "It was a WORKING tag — a byte the callers owned, with no",
        "registry row — until decision 40 ratified THAT VERY BYTE as the",
        "`annotation` row rather than minting a fresh one, so no stored",
        "annotation moved address. It is read off the grammar's sort",
        "table in Lean now, which is what makes the promotion a fact of",
        "the build. The plane is library-owned, so its projection is",
        "`Cas.Annotations.Node` and not a caller's `Cas.value`: the",
        "reserved-tag door refuses every registry row, and this row's",
        "one interpretation is the library's own."],
      value := .int (Int.ofNat pinAnnotationKindTag.toNat) },
    .const {
      name := "AnnotationKindWord",
      doc := ["The everyday word for that kind. It is emitted rather",
        "than written in TypeScript because a rendered kind name enters",
        "the human register off the generated registry and never off a",
        "hand-written table (decision 25). Since decision 40 the kind",
        "HAS a registry row, and `tools/EmitGrammar.lean` pins this word",
        "to that row's own name, so the overlay and the registry cannot",
        "say different words."],
      value := .str pinAnnotationKindWord },
    .const {
      name := "AnnotationRevision",
      doc := ["The revision annotation nodes ride, the Lean pin's own",
        "(`pinAnnotationRevision`) — the projection's revision is part",
        "of the wire, so its consumer reads it here."],
      value := .int (Int.ofNat pinAnnotationRevision) },
    .const {
      name := "AnnotationNameKey",
      doc := ["The name seat's annotation key, exactly as the Lean worked",
        "example pins it (`pinName`)."],
      value := .str pinName.key },
    .const {
      name := "AnnotationKeys",
      type := some "ReadonlyArray<string>",
      doc := ["THE RATIFIED `foldlab/` KEY FAMILY (decision 40, rider",
        "CA-2), read off the Lean worked pins rather than agreed:",
        "the name seat, then related, search-note, pref, embedding and",
        "tombstone. Keys are structurally OPEN strings — the codec reads",
        "`key` as text and could not care which one — so ratifying a",
        "family narrows nothing; it makes the spelling exist once, at",
        "byte level, the way `foldlab/name` already did. A key not on",
        "this list is legal and unratified, which is a different thing",
        "from refused."],
      value := .arr (keyFamily.map Cas.Backend.Ts.Expr.str) },
    .const {
      name := "SystemKindTag",
      doc := ["The service-topology plane's WORKING tag",
        "(`Cas.Schema.systemKindTag`), which the `system` arm below",
        "demands at its target. It is emitted HERE because this is the",
        "only generated surface in the effects package that names it:",
        "the kind registry has no row for a working tag, and the system",
        "lane generates layers rather than a node mirror. The day a",
        "system mirror lands, this constant moves beside it. Named",
        "rather than searched out of the arm table, so its consumer",
        "reads a constant the way it reads `KindTagsByName.cont`."],
      value := .int (Int.ofNat systemKindTag.toNat) },
    .const {
      name := "AnnotationSubjectArms",
      type := some "ReadonlyArray<AnnotationSubjectArm>",
      doc := ["The nameable planes, in the subject union's own member",
        "order: arm name and expected kind tag, read off the union's",
        "canonical code."],
      value := .arr (subjectArms.map armExpr) }
  ]

/-- The emitted projection, rendered in the effects package's style. -/
def annotationPlaneRendered : String :=
  Cas.Backend.Ts.Render.module Cas.Backend.Ts.house0 annotationPlaneModule

/-- Where the projection lands: the effects package's generated tree,
beside the grammar registry it complements. -/
def annotationPlaneTarget : System.FilePath :=
  "../effects/src/cas/generated/annotationPlane.ts"

/-! ## The described store kinds, mirrored

Two of the registered codes above — `exchange` and `annotation` — are
not only pinned payloads: they are KINDS the effects package stores
values through, so each had a hand-written Effect Schema twin
(`src/cas/Exchanges.ts`, and the schema half of
`src/cas/Annotations.ts`) whose own docstrings called it "the hand
mirror of Lean `Cas.Schema.Exchange` — pinned to the same bytes". The
pin was real and it held; what it could not do is author. Every arm,
every field order, every union mode and every kind tag was retyped by
hand and then checked, which makes the byte pin a tripwire on a copy
rather than the copy's absence.

`emitwire` and `emitword` already lower `Described` codes into the
effects package with structural sharing. These two ride the same path;
the one thing they need that no earlier mirror did is a LIVE
reference. -/

section StoreKinds
open Cas.Backend Cas.Backend.Ts

mutual

/-- The live-reference substitution.

`Cas.Backend.constructorExpr` renders a `.ref` as
`CanonicalSchema.ref(tag)` — Effect's own `toCode` spelling of the
reference DECLARATION (`Value.ts`'s `referenceRepresentation`), which
is the right lowering for a mirror that exists to be COMPARED and the
wrong one for a mirror that exists to be STORED THROUGH: that
declaration's decoded side is the `{"$link":…}` sentinel, so a struct
built from it neither accepts a `Root` at encode nor answers one at
decode.

These two kinds are stored through their mirrors — `Cas.value({schema:
Exchanges.Exchange})` puts and gets real nodes — so the reference must
be the runtime's `refWithTag`, whose representation is EXACTLY the
declaration `constructorExpr` names. Hence one substitution on the
rendered expression and nothing else: the sharing environment, the
field order, the union modes and the literal spellings all stay the
lowering's own. -/
private def liveRefs : Expr → Expr
  | .call (.ident "CanonicalSchema.ref") [.int tag] =>
    .call (.ident "refWithTag") [.call (.ident "Byte.make") [.int tag]]
  | .call fn args => .call (liveRefs fn) (liveRefsList args)
  | .object fields => .object (liveRefsFields fields)
  | .objectML fields => .objectML (liveRefsFields fields)
  | .arr items => .arr (liveRefsList items)
  | .arrow ty body => .arrow ty (liveRefs body)
  | e => e

private def liveRefsList : List Expr → List Expr
  | [] => []
  | e :: rest => liveRefs e :: liveRefsList rest

private def liveRefsFields : List (String × Expr) → List (String × Expr)
  | [] => []
  | (name, value) :: rest => (name, liveRefs value) :: liveRefsFields rest

end

-- The substitution fires, and it fires on the exact text the lowering
-- writes: a spelling change on either side goes red here rather than
-- silently emitting a mirror that cannot store.
#guard Render.expr house0 0 (liveRefs (constructorExpr [] (.ref schemaKindTag)))
  == "refWithTag(Byte.make(83))"

-- Nothing else about the lowering moves.
#guard Render.expr house0 0
    (liveRefs (constructorExpr [] (.union [.str, .bool] .oneOf)))
  == "Schema.Union([Schema.String, Schema.Boolean], { mode: \"oneOf\" })"

/-- The mirror registry: emission order is sharing order — a subject
union is named before the kinds that carry it, so those kinds factor
through the name exactly as the hand mirrors referred to the const. -/
def mirrorRegistry : List (String × List String × Ast) := [
  ("exchangeSubjectSchema",
    ["What one exchange is about, by plane: a schema node, or the",
     "exchange that came before it. A reference demands ONE kind tag",
     "and \"what this exchange was about\" is genuinely alternatives, so",
     "the arms are addressed references, and following the `exchange`",
     "arm to exhaustion IS the conversation. A derived union's mode is",
     "part of its identity, so the mode is always spelled; member order",
     "is the deriving handler's canonical order, and reordering it",
     "would be a different code."],
    ExchangeSubject.schemaCode),
  ("exchangeSchema",
    ["One recorded turn of the agent seam (R15): the word put to the",
     "model, the answer that came back, and the content the exchange",
     "was about. The answer's bytes are kept AS SPOKEN — under the",
     "acquisition loop a model's output is evidence and carries no",
     "trust, so normalizing it here would destroy the thing a later",
     "gate has to judge. No `role` field is spelled: role is a property",
     "of an UTTERANCE and an exchange is the PAIR, so position already",
     "says which side spoke."],
    Exchange.schemaCode),
  ("annotationSubjectSchema",
    ["What one annotation is about, by plane: every addressable plane",
     "the estate has today, each arm a typed reference at that plane's",
     "tag. The subject was a bare schema reference, which made a view's",
     "link to the value it projects, a program's human-facing name and",
     "a topology's link to written code all unspellable at once. It",
     "then stopped at the meta and agent planes, which left an",
     "annotation about STORED CONTENT — and a note about a note —",
     "equally unspellable; decision 40's rider CA-1 widened it to the",
     "content planes and to the four sorts that batch ratified. No",
     "`text` arm: the CRDT run was refused from the batch, so there is",
     "no tag for an arm to demand. Nothing is reserved for a plane that",
     "does not exist yet: growth is by an arm, and an arm is",
     "arm-additive."],
    AnnotationSubject.schemaCode),
  ("annotationValueSchema",
    ["What one annotation SAYS: a scalar, or a typed reference to",
     "addressed content. The value was a plain string, and the kind's",
     "own docstring admitted the cost — \"a content address in hex when",
     "the value is itself store content\" — which is precisely the",
     "out-of-band config a content-addressed estate exists to remove: a",
     "hex string never reaches the reference count, the graph walk",
     "never follows it, and a wrong-kind refusal can never fire on it.",
     "The `ref` arm carries the subject union rather than a bare",
     "reference because a reference must name its expected tag, so a",
     "single generic arm cannot be spelled and a second flattened copy",
     "of the plane list would drift from the first."],
    AnnotationValue.schemaCode),
  ("annotationSchema",
    ["The sidecar annotation kind: one annotation node says one thing",
     "about one addressed value, and the DAG carries as many per",
     "subject as wanted. Annotation content is STORE CONTENT — nothing",
     "is added to the schema carrier. Every reference decodes to a",
     "`Root` and encodes to a reference sentinel, so the declaration",
     "this lowers to — what the byte pin compares against the Lean",
     "fixture — is also the live reference codec the value plane",
     "rides."],
    Annotation.schemaCode)
]

private def mirrorDecls : List Decl := Id.run do
  let mut env : List (String × Ast) := []
  let mut out : List Decl := []
  for (name, doc, code) in mirrorRegistry do
    out := out ++ [.const { doc, name, value := liveRefs (constructorExpr env code) }]
    env := env ++ [(name, code)]
  return out

private def storeKindModule : Module where
  header := [
    "GENERATED — do not edit. THE DESCRIBED STORE KINDS, as Effect",
    "Schema: the exchange kind and the sidecar annotation kind, lowered",
    "from the Lean codes in `library/cas/Cas/Schema/Exchange.lean` and",
    "`library/cas/Cas/Schema/Annotation.lean` (`Described.code` of the",
    "authored kinds) by `lake exe schemas`; regeneration is",
    "byte-identity-gated (`--check`, wired into `check:cas`).",
    "",
    "These are LIVE codecs, not comparison mirrors: a reference lowers",
    "to `refWithTag`, so a value built here encodes a `Root` to a",
    "reference sentinel and decodes one back, and the store's admission",
    "law checks the arm's kind tag at the address. Their canonical",
    "payloads are the committed `schemas/exchange.json` and",
    "`schemas/annotation.json`, and the pin suites hold these",
    "declarations to those bytes and to the addresses beside them.",
    "",
    "`src/cas/Exchanges.ts` and `src/cas/Annotations.ts` are this",
    "file's consumers. What they add is what a schema is not: the",
    "constructors that build one subject arm or one value arm, and —",
    "on the annotation side — the estate's persistent annotation",
    "namespace on live Effect carriers, which is a different plane",
    "with the same name."
  ] ++ emitted.headerLines
  imports := [
    .named ["Schema"] "effect",
    .named ["Byte"] "../Node.ts",
    .named ["refWithTag"] "../Value.ts"
  ]
  decls :=
    (.const {
      name := "ExchangeKindTag",
      doc := ["The kind tag exchange nodes reside at",
        "(`Cas.Schema.exchangeKindTag`). A WORKING tag, deliberately",
        "absent from the reserved set: minting plane identity is the",
        "reserved-tag ruling's question, and until it is answered an",
        "exchange resides at a tag its callers own — which is what lets",
        "`Cas.value` accept it. The `exchange` arm of the subject union",
        "demands this tag, so a chain is only walkable when its nodes",
        "reside here; that constraint is the whole content of the",
        "ruling."],
      value := .int (Int.ofNat exchangeKindTag.toNat) }) :: mirrorDecls

/-- The store-kind mirrors, rendered in the effects package's style. -/
def storeKindRendered : String :=
  Cas.Backend.Ts.Render.module Cas.Backend.Ts.house0 storeKindModule

-- No declaration-only reference survives into the emitted module: one
-- that did would compile and then refuse every `Root` it was handed.
#guard (storeKindRendered.splitOn "CanonicalSchema.ref").length == 1

-- Fifteen live references — two arms of the exchange subject and
-- thirteen of the annotation subject, which decision 40's rider CA-1
-- widened from five. The other two kinds reach theirs through the
-- shared name, which is what the sharing environment is for.
#guard (storeKindRendered.splitOn "refWithTag(").length
  == 1 + 2 + subjectArms.length

/-- Where the mirrors land: the effects package's generated tree,
beside the annotation plane's own projection. -/
def storeKindTarget : System.FilePath :=
  "../effects/src/cas/generated/StoreKindSchema.ts"

end StoreKinds

/-- The registry rendered as the driver's fixtures: one payload file
per pinned code — the file's bytes ARE the schema-node payload — then
the tracking manifest, the store-address file, the annotation-plane
projection the CLI's naming seat consumes, and the described store
kinds' Effect Schema mirrors. -/
def fixtures : IO (List Gate.Fixture) :=
  return registry.map (fun (name, ast) =>
      ({ path := pathOf name, content := ast.payload,
         label := "canonical payload" } : Gate.Fixture)) ++
    [⟨indexPath, indexDocument, s!"{registry.length} schemas"⟩,
     ⟨addressesPath, addressesDocument, s!"{registry.length} addresses"⟩,
     ⟨annotationPlaneTarget, annotationPlaneRendered,
       s!"{subjectArms.length} nameable planes, the annotation-plane projection"⟩,
     ⟨storeKindTarget, storeKindRendered,
       s!"{mirrorRegistry.length} mirrors, the described store kinds"⟩]

end SchemasMain

def main := Gate.main "lake exe schemas" SchemasMain.fixtures
