import Cas.Schema.Ingest

/-!
# The admission map — the ACC-1 carrier-adequacy table, as a value

Every variant of Effect's schema algebra, dispositioned against the
canonical carrier `Cas.Schema.Ast`: what the estate admits today, what
it defers and behind which named increment or ruling, and what it
rejects outright. This is the CLAIMS artifact of the schema plane —
the A-1/ACC-2 discipline written as data instead of prose, emitted as
`conformance/admission-map.json` by `lake exe admissionmap` and gated
byte-for-byte like every other manifest in the estate.

## Two unions, one table

The source algebra has two enumerations and they are not the same
size, so the map carries BOTH and says which is which per row:

- the **AST union** — 21 variants, the union the committed inventory
  (`experiments/entity-store-extract/inventory.json`) enumerates by
  extraction, and the only enumeration any gate can check against;
- the **Representation union** — 22 variants, the persistent algebra
  the ingestion door actually reads
  (`SchemaRepresentation.Representation`), which is the AST union plus
  `Reference`, the revival shape that exists only in the persisted
  document.

Every row is a Representation variant; `inAst` says whether it is also
an AST variant. Exactly one row (`Reference`) is not, and the ACC-1
totality gate is stated over the 21 that are: every inventory variant
has exactly one row, checked against the committed inventory file by
the emitter (`tools/AdmissionMap.lean`), because a `#guard` cannot
read a file.

## What a verdict means, and what it does not

- `ADMITTED` — the door decodes this variant today. Pinned by a
  WITNESS: a code of the carrier whose revision-1 projection carries
  that variant's `_tag` and whose envelope survives `ingest`.
- `DEFERRED(code)` — no row of the carrier spells it, and the named
  code says what would change that. **Landing a deferred row admits
  nothing.** `Suspend` and `Reference` stay behind increment C6
  whether or not this table exists; the table records the claim, the
  increment changes the behaviour.
- `REJECTED(code)` — it is not coming. Effect's own persistent codec
  cannot restore it, so there is no faithful carriage to design.

Both non-admitted verdicts are pinned the same way: the keyword-shaped
probe under that `_tag` is REFUSED at the door. So the map cannot
claim a variant is unadmitted while the door quietly takes it, and it
cannot claim one is admitted while the projection cannot spell it —
the guards below run both directions over the whole table.

## What the map does NOT claim

Shape, not semantics — the inventory's own non-claim, carried
forward. The escape hatches (`Declaration.run`, the open annotation
bag, encoding transformations, filter closures) stay outside
first-order content, and transformations in particular are erased by
Effect's own lowering and stay erased here. A decoder built from this
map must refuse anything it does not disposition; it must never
synthesize coverage.
-/

namespace Cas.Schema

open Cas.Json

/-! ## The vocabulary -/

/-- Why a variant is not admitted. A closed list: a row that needs a
reason outside it is a change to this type, not a free-text note. -/
inductive AdmissionReason where
  /-- Cheap to admit, no store meaning yet; admission waits for a real
  consumer (grammar-grill ruling 5). -/
  | consumerGated
  /-- No bounded integer carrier fixes the width, and the
  Integer-semantics ruling — SafeInt bounds versus a bare `isInt`
  filter — has to settle the number rows first. -/
  | intWidth
  /-- Regex-adjacent semantics; Effect's own importer defaults
  `patterns: "error"` for the same reason. -/
  | patternHazard
  /-- Effect's persistent codec itself rejects or cannot restore it,
  so there is no faithful carriage to design. -/
  | noReconstructableIdentity
  deriving DecidableEq, Repr

/-- Every code, in wire order. The guards below demand that each one
is actually carried by a row: a vocabulary with a dead word is a
vocabulary that has stopped describing the table. -/
def AdmissionReason.all : List AdmissionReason :=
  [.consumerGated, .intWidth, .patternHazard,
   .noReconstructableIdentity]

/-- The code's wire spelling — the word the emitted artifact and the
proposal both print. -/
def AdmissionReason.wire : AdmissionReason → String
  | .consumerGated => "CONSUMER-GATED"
  | .intWidth => "INT-WIDTH"
  | .patternHazard => "PATTERN-HAZARD"
  | .noReconstructableIdentity => "NO-RECONSTRUCTABLE-IDENTITY"

/-- The code in one sentence: the artifact carries its own legend, so a
reader never has to find this file to read the table. -/
def AdmissionReason.means : AdmissionReason → String
  | .consumerGated =>
    "cheap to admit, no store meaning yet; admission waits for a real consumer"
  | .intWidth =>
    "no bounded integer carrier fixes the width, and the Integer-semantics ruling — SafeInt bounds versus the bare isInt filter — settles the number rows first"
  | .patternHazard =>
    "regex-adjacent semantics; Effect's own importer refuses patterns for the same reason"
  | .noReconstructableIdentity =>
    "Effect's persistent codec rejects or cannot restore it, so no faithful carriage exists"

/-- The three words the map answers. A code is carried by exactly the
two that are not `admitted` — the shape says so, so no row can defer
without saying behind what. -/
inductive AdmissionVerdict where
  | admitted
  | deferred (code : AdmissionReason)
  | rejected (code : AdmissionReason)
  deriving DecidableEq, Repr

/-- The verdict's wire spelling. -/
def AdmissionVerdict.word : AdmissionVerdict → String
  | .admitted => "ADMITTED"
  | .deferred _ => "DEFERRED"
  | .rejected _ => "REJECTED"

/-- The code a verdict carries — `none` for `admitted` alone, which is
why an admitted row cannot name a reason and a deferred one cannot
omit it. -/
def AdmissionVerdict.code : AdmissionVerdict → Option AdmissionReason
  | .admitted => none
  | .deferred c | .rejected c => some c

/-- Does the door take this variant today? -/
def AdmissionVerdict.isAdmitted : AdmissionVerdict → Bool
  | .admitted => true
  | _ => false

/-- One row of the map: one variant of the Representation union, its
verdict, where it lands in the carrier when it lands at all, the prose
that says why, and — for an admitted row — the WITNESS code that makes
the claim checkable against behaviour. -/
structure AdmissionRow where
  /-- The variant's `_tag`, verbatim as Effect spells it. -/
  variant : String
  /-- Is this also a variant of the 21-member AST union the committed
  inventory enumerates? False for `Reference` alone. -/
  inAst : Bool
  verdict : AdmissionVerdict
  /-- The carrier constructor(s) an admitted variant lands in. -/
  carrier : Option String
  reason : String
  /-- A code of the carrier that projects to this variant, for an
  admitted row; `none` otherwise. The guards below demand exactly that
  correspondence in both directions. -/
  witness : Option Ast

/-- The map: the whole carrier-adequacy table, as data. -/
structure AdmissionMap where
  mapVersion : Nat
  /-- The carrier every row is dispositioned against. -/
  carrier : String
  /-- The source algebra, pinned to the extraction the inventory
  records. -/
  source : String
  rows : List AdmissionRow

/-! ## The table -/

/-- v0 — the eleven variants that had no row in any gated artifact get
one here, and the ten the emitgate table already realizes are pinned
to it. Row order is the proposal's, so the two read side by side. -/
def admissionMapV0 : AdmissionMap where
  mapVersion := 0
  carrier := "Cas.Schema.Ast"
  source := "SchemaRepresentation.Representation (effect@4.0.0-rc.111)"
  rows := [
    { variant := "Null", inAst := true, verdict := .admitted,
      carrier := some "Ast.null", witness := some .null,
      reason := "the keyword code; checks must be empty and annotations absent until the annotation increment" },
    { variant := "Boolean", inAst := true, verdict := .admitted,
      carrier := some "Ast.bool", witness := some .bool,
      reason := "the keyword code, disciplined as Null" },
    { variant := "String", inAst := true, verdict := .admitted,
      carrier := some "Ast.str", witness := some .str,
      reason := "the keyword code, disciplined as Null" },
    { variant := "Number", inAst := true, verdict := .admitted,
      carrier := some "Ast.int", witness := some .int,
      reason := "admitted with the verbatim isInt filter, which the projection re-emits; a bare Number and every other check wait on the Integer-semantics ruling" },
    { variant := "Literal", inAst := true, verdict := .admitted,
      carrier := some "Ast.lit", witness := some (.lit (.str "x")),
      reason := "boolean, number and string literals carried; a bigint literal waits with the BigInt row, and a null literal arrives as the Null keyword — the projection collapses it" },
    { variant := "Arrays", inAst := true, verdict := .admitted,
      carrier := some "Ast.arr, Ast.tuple", witness := some (.arr .str),
      reason := "increment C2: elements and their optionality carried, a rest of length zero or one carried as an Option; a longer rest and the empty tuple have no spelling on this side and die in the decoder" },
    { variant := "Objects", inAst := true, verdict := .admitted,
      carrier := some "Ast.struct", witness := some (.struct [("a", false, .str)]),
      reason := "property signatures with string names, carried with their optionality; number and symbol names, the mutability bit and index signatures are increment C3 and are refused until it lands" },
    { variant := "Union", inAst := true, verdict := .admitted,
      carrier := some "Ast.union", witness := some (.union [.str, .bool] .anyOf),
      reason := "increment C1: member order is identity, nothing flattens or deduplicates, both modes are carried and always spelled, and the empty union is Never and is refused at the gate" },
    { variant := "Enum", inAst := true, verdict := .admitted,
      carrier := some "Ast.enum", witness := some (.enum [("A", .str "a")]),
      reason := "increment C4: string and safe-int members, source order is identity, member names pairwise distinct, member values deliberately free because TypeScript spells aliases" },
    { variant := "Declaration", inAst := true, verdict := .admitted,
      carrier := some "Ast.ref, Ast.decl", witness := some (.decl .option .null [.str]),
      reason := "increment C-decl: the id is registry-gated and an id outside the registry is refused unknownDeclaration by name; payload shape and type-parameter count are read off the row" },
    { variant := "Suspend", inAst := true, verdict := .admitted,
      carrier := some "Ast.susp", witness := some (.susp .str),
      reason := "increment C6: the thunk is carried INLINE as a nested code, which is Effect's own shape, and the always-empty checks field needs no term. This is the GUARD the guardedness law is about — bareRefs stops here, so a cycle through a susp is admitted and one without is refused" },
    { variant := "Reference", inAst := false, verdict := .admitted,
      carrier := some "Ast.reference", witness := some (.reference "Node"),
      reason := "increment C6: the references table is read now, and a reference is the name into it — the one admitted node with no checks key. The name is nonempty as Effect requires; the address discipline and resolvability are the door's and the materializer's, not WF's. A Representation-layer variant only: it is no member of the AST union the inventory enumerates" },
    { variant := "Undefined", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "a fieldless keyword, cheap to admit, with no store meaning yet" },
    { variant := "Void", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "a fieldless keyword, cheap to admit, with no store meaning yet" },
    { variant := "Never", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "the empty type, cheap to admit; the empty union and the empty enum already spell it and are refused at the gate, so admitting it would need that refusal to become a code" },
    { variant := "Unknown", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "a fieldless keyword, cheap to admit, with no store meaning yet" },
    { variant := "Any", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "a fieldless keyword, cheap to admit, with no store meaning yet" },
    { variant := "ObjectKeyword", inAst := true, verdict := .deferred .consumerGated,
      carrier := none, witness := none,
      reason := "a fieldless keyword, cheap to admit, with no store meaning yet" },
    { variant := "BigInt", inAst := true, verdict := .deferred .intWidth,
      carrier := none, witness := none,
      reason := "the carrier has no unbounded integer, and the width a bigint would be given is downstream of the Integer-semantics ruling the Number row already waits on" },
    { variant := "Symbol", inAst := true, verdict := .rejected .noReconstructableIdentity,
      carrier := none, witness := none,
      reason := "a symbol's identity is its creation, not its content; nothing addressable reconstructs it" },
    { variant := "UniqueSymbol", inAst := true, verdict := .rejected .noReconstructableIdentity,
      carrier := none, witness := none,
      reason := "Effect's own persistent codec rejects local symbols, so there is no faithful carriage to design" },
    { variant := "TemplateLiteral", inAst := true, verdict := .deferred .patternHazard,
      carrier := none, witness := none,
      reason := "regex-adjacent semantics with a derived cache Effect itself refuses to persist by default" }
  ]

/-! ## Reading the table -/

/-- The rows the door takes today. -/
def AdmissionMap.admittedRows (m : AdmissionMap) : List AdmissionRow :=
  m.rows.filter (·.verdict.isAdmitted)

/-- The rows the door refuses today, deferred and rejected alike — the
domain of the backward pin. -/
def AdmissionMap.unadmittedRows (m : AdmissionMap) : List AdmissionRow :=
  m.rows.filter (!·.verdict.isAdmitted)

/-- The variants the map says the door takes. -/
def AdmissionMap.admittedNames (m : AdmissionMap) : List String :=
  m.admittedRows.map (·.variant)

/-- The AST-union variants, in row order: the domain the ACC-1
totality gate is stated over. -/
def AdmissionMap.astNames (m : AdmissionMap) : List String :=
  (m.rows.filter (·.inAst)).map (·.variant)

/-- How many rows answer one verdict word. -/
def AdmissionMap.count (m : AdmissionMap) (word : String) : Nat :=
  (m.rows.filter (fun r => r.verdict.word == word)).length

/-- The reason codes some row actually carries — the legend the
emitted artifact prints. -/
def AdmissionMap.reasonsUsed (m : AdmissionMap) : List AdmissionReason :=
  AdmissionReason.all.filter fun c => m.rows.any fun r => r.verdict.code == some c

/-! ## The pins — the map cannot lie about the code

Three readings, each run at elaboration. The shape reading (the table
is a table: distinct rows, one keying, every non-admitted row without
a witness). The forward reading (every ADMITTED row has a witness the
projection spells with that tag and the door takes). The backward
reading (every non-admitted row's tag is REFUSED at the door, and the
carrier can emit no tag the map does not admit). -/

/-- The `_tag` of a representation value, when it has one. -/
private def tagOf : Json.Value → Option String
  | .obj fields =>
    match fields.lookup "_tag" with
    | some (.str s) => some s
    | _ => none
  | _ => none

/-- One witness per CONSTRUCTOR of the carrier — the emitgate table
read off the projection rather than transcribed. `.ref` and `.decl`
both spell `Declaration`, and `.lit .null` spells `Null`; that is the
projection's own collapse, and the two-directional guard below holds
across it. -/
private def carrierWitnesses : List Ast :=
  [.null, .bool, .int, .str, .lit (.str "x"), .lit .null, .arr .str,
   .struct [("a", false, .str)], .ref 0, .decl .option .null [.str],
   .union [.str, .bool] .anyOf, .enum [("A", .str "a")],
   .tuple (false, .str) [] none, .reference "Node", .susp .str]

/-- The keyword-shaped probe: a revision-1 schema node whose
representation is nothing but a `_tag` and an empty `checks` list.
Every admitted keyword decodes from exactly this shape, so a variant
the map calls unadmitted must be refused from it. -/
private def keywordProbe (tag : String) : Json.Value :=
  .obj [("revision", .nat schemaRevision),
        ("value", .obj [("references", .obj []),
          ("representation", .obj [("_tag", .str tag), ("checks", .arr [])])])]

private def distinctNames : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinctNames ns

-- THE TABLE IS A TABLE: no variant is rowed twice.
#guard distinctNames (admissionMapV0.rows.map (·.variant))

-- THE KEYING, stated: 22 rows over the Representation union, 21 of
-- them over the AST union the inventory enumerates, and `Reference` is
-- the one that is not.
#guard admissionMapV0.rows.length == 22
#guard admissionMapV0.astNames.length == 21
#guard (admissionMapV0.rows.filter (!·.inAst)).map (·.variant) == ["Reference"]

-- THE VERDICTS partition the table.
#guard admissionMapV0.count "ADMITTED" == 12
#guard admissionMapV0.count "DEFERRED" == 8
#guard admissionMapV0.count "REJECTED" == 2

-- NO DEAD VOCABULARY: every declared reason code is carried by some
-- row, so the legend the artifact prints is the whole vocabulary.
#guard admissionMapV0.reasonsUsed == AdmissionReason.all

-- A witness is exactly an admitted row's business.
#guard admissionMapV0.rows.all fun r =>
  r.witness.isSome == r.verdict.isAdmitted

-- ...as is a carrier constructor.
#guard admissionMapV0.rows.all fun r =>
  r.carrier.isSome == r.verdict.isAdmitted

-- FORWARD: every ADMITTED row's witness projects to that row's tag,
-- so the map cannot name a variant the carrier does not spell.
#guard admissionMapV0.rows.all fun r =>
  match r.witness with
  | some a => tagOf a.toRepresentationJson == some r.variant
  | none => true

-- FORWARD: and the door takes that witness. An ADMITTED row that the
-- ingestion door would refuse is red here, not in review.
#guard admissionMapV0.rows.all fun r =>
  match r.witness with
  | some a => (match ingest a.envelope with | .ok _ => true | .error _ => false)
  | none => true

-- BACKWARD: every row the map does NOT admit is refused at the door
-- under the keyword spelling. Deferring a variant on paper while the
-- door quietly decodes it is red here.
#guard admissionMapV0.unadmittedRows.all fun r =>
  match ingest (keywordProbe r.variant) with
  | .error .notASchema => true
  | _ => false

-- BACKWARD: the carrier emits NO tag the map fails to admit — every
-- constructor of `Ast` projects into the admitted set.
#guard carrierWitnesses.all fun a =>
  match tagOf a.toRepresentationJson with
  | some t => admissionMapV0.admittedNames.contains t
  | none => false

-- ...and the admitted set is no larger than what the carrier emits:
-- every ADMITTED row is some constructor's tag.
#guard admissionMapV0.admittedNames.all fun t =>
  carrierWitnesses.any fun a => tagOf a.toRepresentationJson == some t

/-! ## The projection -/

private def AdmissionRow.toValue (r : AdmissionRow) : Json.Value :=
  .obj [
    ("variant", .str r.variant),
    ("unions", .arr (if r.inAst then [.str "ast", .str "representation"]
                     else [.str "representation"])),
    ("verdict", .str r.verdict.word),
    ("code", match r.verdict.code with
      | some c => .str c.wire
      | none => .null),
    ("carrier", match r.carrier with
      | some c => .str c
      | none => .null),
    ("witnessPayload", match r.witness with
      | some a => .str a.payload
      | none => .null),
    ("reason", .str r.reason)]

/-- The map as a JSON value (keys sort at render, per the house
printer). -/
def AdmissionMap.toValue (m : AdmissionMap) : Json.Value :=
  .obj [
    ("mapVersion", .nat m.mapVersion),
    ("carrier", .str m.carrier),
    ("source", .str m.source),
    ("keying", .str "rows are keyed to the 22-member Representation union; `unions` says which rows are also members of the 21-member AST union the committed inventory enumerates, and the ACC-1 totality gate is stated over those"),
    ("inventory", .obj [
      ("path", .str "experiments/entity-store-extract/inventory.json"),
      ("astVariants", .nat m.astNames.length)]),
    ("reasonCodes", .obj (m.reasonsUsed.map fun c => (c.wire, .str c.means))),
    ("counts", .obj [
      ("rows", .nat m.rows.length),
      ("admitted", .nat (m.count "ADMITTED")),
      ("deferred", .nat (m.count "DEFERRED")),
      ("rejected", .nat (m.count "REJECTED"))]),
    ("rows", .arr (m.rows.map AdmissionRow.toValue))]

/-- The rendered document — the bytes of `conformance/admission-map.json`. -/
def admissionDocument : String := Cas.Json.document admissionMapV0.toValue

end Cas.Schema
