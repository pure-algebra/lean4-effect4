import Cas.Backend.Ts
import Cas.Schema.Ingest

/-!
# The admission table — the door's shape, as first-order data

`Cas.Schema.ingest` is `Ast.ofRepresentationJson` composed with
`Ast.wf`: a strict decoder that says WHICH spellings are nodes, and a
runtime gate that says which decoded codes are well-formed. The
TypeScript door has to answer the same questions, and until this module
it answered them from a second, hand-written 330-line copy —
`CanonicalSchema.admitNode` — with the check spelling, the safe-integer
bound, the union modes, the declaration columns and the refusal prose
all duplicated verbatim by eye.

This is the ONE home (R11 applied to the door): the table below is the
whole of what the TypeScript gate needs, and `lake exe emitgate` prints
it byte-identically into `src/cas/generated/SchemaAdmission.ts`, where a
small interpreter walks it. Nothing about the admitted subset is typed
twice.

## What is derived and what is stated

DERIVED — read off the Lean definitions, so it cannot drift:

- every node's TAG and its exact key list, read off
  `Ast.toRepresentationJson` of a witness code;
- the one admitted check spelling, read off the `Number` witness's
  `checks` array (`isIntCheckSpelling` in TypeScript was this object,
  retyped);
- the property-signature, element, literal, enum-member, declaration
  identity, document and envelope key lists, read off the same
  projection;
- the union modes, from `UnionMode.all`;
- the declaration rows — wire, arity, and payload column — from
  `DeclarationId.all`, with the payload column PROBED out of
  `DeclarationId.payloadWf` rather than transcribed, and the kind-tag
  bound counted out of the same gate;
- the safe-integer bound (`maxSafeNat`) and the two revisions.

STATED — the clause table: a clause name, the `IngestRefusal` it
carries, and the prose the refusal reads. There is no metaprogram that
extracts "the empty union is `illFormed`" from `Ast.wf`'s pattern match,
so the clause column is a hand table — but it is a hand table in ONE
file, and every family of it is tied to `ingest`'s actual answer by a
`#guard` below. A clause whose refusal name stops matching what the
door does fails to elaborate.

## The second divergence this table does not close (increment C6)

An EMPTY reference name is refused by both doors under different names.
Lean's decoder reads `{"$ref":"","_tag":"Reference"}` as a shape and the
gate turns it away `illFormed`; Effect's own persistent decoder refuses
the spelling outright, because `$ref` is `Schema.NonEmptyString`, so the
TypeScript door answers `notASchema` before this table is consulted.

Why it is recorded rather than closed: refusing the empty name in Lean's
DECODER would falsify `ofRepresentationJson_toRepresentationJson`, which
holds unconditionally over every code, and making the name nonempty BY
CONSTRUCTION would change `Ast.reference`'s ruled signature. Both are
rulings, not translations. The conformance corpus therefore carries no
row for this spelling — an omission stated there, in `tools/Verdicts.lean`,
rather than left to be discovered.

Nothing else about C6 diverges: the guardedness walk, the two node
shapes, the empty table key and the duplicate table key are all
interpreted from the columns below and agree case for case.

## The refusal ORDER is this table's too (break pass, finding F5)

A document can have two defects, and then the doors have to agree on
which one it is named for. Lean's order, in `Cas.Schema.ingestDocument`:

1. the SPELLING — a references table naming one entry twice is refused
   `illFormed` before anything is decoded;
2. the DECODER — a spelling that is no code at all is `notASchema`, or
   `unknownDeclaration` where the allowlist is what turned it away;
3. GUARDEDNESS — `unguardedCycle`, ahead of every other discipline;
4. everything else `Ast.wf` and `Document.WF` ask — `illFormed`.

The TypeScript gate used to run its per-entry admission before its
guardedness filter, so a table entry that was both cyclic and ill
formed earned `unguardedCycle` from Lean and `illFormed` from
TypeScript. It mirrors the order above now. The interpreter can tell
stage 2 from stage 4 by the refusal NAME the table gives a clause —
`notASchema` and `unknownDeclaration` are the decoder's, `illFormed` is
the discipline's — so the ordering is read off this table rather than
hand-kept beside it.

## The one divergence this table does NOT close

Lean's decoder is EXACT on keys: a node carrying a key the projection
does not emit has no spelling and dies `notASchema`. Effect's own
`toJson` emits an `annotations` bag on a `Declaration` node
(`Schema.Date` persists `{"annotations":{"expected":"a valid Date"},…}`),
so exact-key enforcement on the TypeScript side would refuse three of
the four registry rows as they are actually stored. The key lists here
are therefore consumed as the REQUIRED keys — present and of the right
shape — and an extra key is tolerated exactly as the hand gate tolerated
it. Closing that gap is a ruling (does the estate store Effect's
annotation bag, or strip it?), not a translation.
-/

namespace Cas.Backend.Admission

open Cas.Schema Cas.Backend.Ts

/-! ## Reading the projection

Three accessors, so every derived column below is a fact about
`Ast.toRepresentationJson` rather than a transcription of it. -/

/-- An object's keys, in the order the projection writes them — which is
canonical (sorted) order, because the projection is canonical. -/
def keysOf : Cas.Json.Value → List String
  | .obj fs => fs.map (·.1)
  | _ => []

/-- The value under one key, or `null` when there is none. -/
def fieldOf (k : String) : Cas.Json.Value → Cas.Json.Value
  | .obj fs => ((fs.find? (·.1 == k)).map (·.2)).getD .null
  | _ => .null

/-- A node's `_tag`. -/
def tagOf (v : Cas.Json.Value) : String :=
  match fieldOf "_tag" v with
  | .str s => s
  | _ => ""

/-- A string value, or the empty string. -/
def stringOf : Cas.Json.Value → String
  | .str s => s
  | _ => ""

/-! ## The refusal vocabulary -/

/-- `IngestRefusal` by name — the five words the two doors share. -/
def refusalName : IngestRefusal → String
  | .notASchema => "notASchema"
  | .illFormed => "illFormed"
  | .wrongRevision => "wrongRevision"
  | .nonEmptyReferences => "nonEmptyReferences"
  | .unguardedCycle => "unguardedCycle"
  | .unknownDeclaration => "unknownDeclaration"

/-- Every refusal, in declaration order. -/
def refusals : List IngestRefusal :=
  [.notASchema, .illFormed, .wrongRevision, .nonEmptyReferences,
    .unguardedCycle, .unknownDeclaration]

/-- The vocabulary is complete: a new refusal cannot be minted without
appearing here, and therefore in the generated TypeScript union. -/
theorem refusals_complete (r : IngestRefusal) : r ∈ refusals := by
  cases r <;> decide

-- The names collide with nothing.
#guard decide ((refusals.map refusalName).Nodup)

/-! ## The node rows

One row per admitted `_tag`. The row carries a WITNESS code, not a
transcribed shape: the tag and the key list are read off that witness's
own projection, so a change to `Ast.toRepresentationJson` moves the
generated bytes rather than silently parting from them. -/

structure NodeRow where
  /-- Which arm of the TypeScript interpreter reads this node. -/
  form : String
  /-- A code whose projection IS this row's shape. -/
  witness : Ast
  /-- The checks policy: `empty` everywhere, `isInt` on `Number`. -/
  checks : String

def NodeRow.rep (r : NodeRow) : Cas.Json.Value := r.witness.toRepresentationJson

def NodeRow.tag (r : NodeRow) : String := tagOf r.rep

def NodeRow.keys (r : NodeRow) : List String := keysOf r.rep

/-- A safe integer witness. -/
private def zero : SafeInt := ⟨0, by decide⟩

/-- THE node table. `Arrays` appears ONCE: the decoder's plain-array and
tuple arms carry the same tag and the same four keys, and the
TypeScript arm that reads them tells them apart exactly as the decoder
does — by whether `elements` is empty. -/
def nodes : List NodeRow := [
  { form := "keyword", witness := .null, checks := "empty" },
  { form := "keyword", witness := .bool, checks := "empty" },
  { form := "keyword", witness := .str, checks := "empty" },
  { form := "number", witness := .int, checks := "isInt" },
  { form := "literal", witness := .lit (.str "x"), checks := "empty" },
  { form := "arrays", witness := .arr .str, checks := "empty" },
  { form := "objects", witness := .struct [("a", false, .str)], checks := "empty" },
  { form := "declaration", witness := .ref 0, checks := "empty" },
  { form := "union", witness := .union [.str] .anyOf, checks := "empty" },
  { form := "enum", witness := .enum [("A", .str "a")], checks := "empty" },
  -- The C6 rows. `Reference` is the ONE admitted node with no `checks`
  -- key at all — Effect's own shape — which is why its checks policy
  -- reads `none` rather than `empty`: there is no array to be empty.
  { form := "reference", witness := .reference "Node", checks := "none" },
  { form := "suspend", witness := .susp .str, checks := "empty" }
]

-- One row per tag, and every witness really is an admitted code.
#guard decide ((nodes.map NodeRow.tag).Nodup)
#guard nodes.all fun r => (ingest r.witness.envelope).toOption.isSome

-- The tuple arm shares the plain array's tag AND its key list: the
-- table has one `Arrays` row because the projection spells one shape.
#guard (Ast.tuple (false, .str) [] none).toRepresentationJson |> fun t =>
  tagOf t == "Arrays" && keysOf t == keysOf (Ast.arr .str).toRepresentationJson

/-! ## The sub-shapes

The shapes that are not nodes: what a property signature, a tuple
element, a literal, an enum member value, a declaration identity, a
document and an envelope spell. Each key list is read off the emitter
that writes it. -/

/-- One property signature's keys. -/
def propertyKeys : List String :=
  match fieldsToRepresentationJson [("a", false, .str)] with
  | [p] => keysOf p
  | _ => []

/-- A property signature's `name` slot: the typed string key. -/
def propertyNameKeys : List String :=
  match fieldsToRepresentationJson [("a", false, .str)] with
  | [p] => keysOf (fieldOf "name" p)
  | _ => []

/-- One tuple element's keys — `isOptional` and `type`, and no
annotation bag (C-ann). -/
def elementKeys : List String :=
  keysOf (elementToRepresentationJson (false, .str))

/-- A literal's typed-value keys. -/
def literalKeys : List String :=
  keysOf (fieldOf "literal" (Ast.lit (.str "x")).toRepresentationJson)

/-- An enum member value's keys. -/
def enumValueKeys : List String :=
  match enumMembersToJson [("A", .str "a")] with
  | [.arr [_, v]] => keysOf v
  | _ => []

/-- A declaration identity's keys. -/
def declarationIdentityKeys : List String :=
  keysOf (fieldOf "representation" (Ast.ref 0).toRepresentationJson)

/-- The representation document's keys. -/
def documentKeys : List String := keysOf (Ast.representationDocument .str)

/-- The schema-node envelope's keys. -/
def envelopeKeys : List String := keysOf (Ast.envelope .str)

/-! ## The typed-value tables

Effect spells a literal and an enum member as `{type, value}`. WHICH
type tags are admitted is read off the projection; which TypeScript
predicate admits the value under each is the one hand column, and it is
three words long. -/

/-- The `type` tag the projection writes for one literal. -/
def literalTypeOf (v : LitVal) : String :=
  stringOf (fieldOf "type" (fieldOf "literal" (Ast.lit v).toRepresentationJson))

/-- The `type` tag the projection writes for one enum member value. -/
def enumTypeOf (v : EnumValue) : String :=
  match enumMembersToJson [("A", v)] with
  | [.arr [_, m]] => stringOf (fieldOf "type" m)
  | _ => ""

/-- The admitted literal spellings: the projection's type tag, and the
predicate the TypeScript reader applies to `value`. A NULL literal has
no row — it is the `Null` keyword (register R13). -/
def literalTypes : List (String × String) :=
  [(literalTypeOf (.bool true), "boolean"),
    (literalTypeOf (.int zero), "safeInteger"),
    (literalTypeOf (.str ""), "string")]

/-- The admitted enum member value spellings — Effect's `Enum` persists
exactly two (`SchemaRepresentation.ts:1015-1022`). -/
def enumValueTypes : List (String × String) :=
  [(enumTypeOf (.str ""), "string"), (enumTypeOf (.int zero), "safeInteger")]

-- Neither table has a hole, and neither carries a null row.
#guard literalTypes.all fun r => r.1 != "" && r.2 != ""
#guard enumValueTypes.all fun r => r.1 != "" && r.2 != ""

/-! ## The declaration registry, as columns

The wire spelling and the arity come straight off the row. The payload
column is PROBED out of `DeclarationId.payloadWf` — the gate itself
answers which shape it admits — so the column cannot say `null` about a
row whose gate wants a kind tag. -/

/-- The payload column a row's own gate implies. -/
def payloadColumn (d : DeclarationId) : String :=
  if d.payloadWf .null then "null"
  else if d.payloadWf (.nat 0) then "byte"
  else "unclassified"

/-- The kind-tag bound, counted out of the gate rather than restated:
how many naturals the byte row actually admits. -/
def payloadByteBound : Nat :=
  match DeclarationId.all.find? (fun d => payloadColumn d == "byte") with
  | some d => ((List.range 4096).filter (fun n => d.payloadWf (.nat n))).length
  | none => 0

/-- The registry as the three columns the TypeScript door reads. -/
def declarations : List (String × Nat × String) :=
  DeclarationId.all.map fun d => (d.wire, d.arity, payloadColumn d)

-- Every row is classified, and the byte row's bound is the one the
-- TypeScript gate has been spelling by hand.
#guard declarations.all fun r => r.2.2 != "unclassified"
#guard payloadByteBound == 256

/-! ## The clause table

The hand column, and the only one. Each clause names the refusal it
carries and the prose the door reads; `{path}` is the node's path,
`{it}` the offending value as canonical JSON, and `{keys}` the list the
clause is about. The `#guard`s below tie one representative spelling per
family to `ingest`'s actual answer. -/

structure Clause where
  clause : String
  refusal : IngestRefusal
  detail : String

/-- LAW SM-19: the two doors are held in agreement by this table,
interpreted into the TypeScript gate rather than restated there.

THE clause table. -/
def clauses : List Clause := [
  { clause := "notAnObject", refusal := .notASchema,
    detail := "{path} is not an object" },
  { clause := "notAnArray", refusal := .notASchema,
    detail := "{path} is not an array" },
  { clause := "unadmittedNode", refusal := .notASchema,
    detail := "{path} is a {it} node, which the admitted subset does not carry" },
  { clause := "nodeKeys", refusal := .notASchema,
    detail := "{path} does not carry {keys}, which is what the canonical spelling of this node writes" },
  { clause := "checksNotEmpty", refusal := .notASchema,
    detail := "{path} carries checks: the admitted subset carries the isInt check on Number and no other (the checks layer is Slice C5)" },
  { clause := "notTheIntCheck", refusal := .notASchema,
    detail := "{path} is not the admitted integer: the subset carries Number under exactly the effect/schema/isInt check, and a bare Number would type a float the value plane has no term for (ruling 15, the float ceiling)" },
  { clause := "literalShape", refusal := .notASchema,
    detail := "{path} is not an admitted literal: booleans, strings, and safe integers only (a null literal is the Null keyword, register R13)" },
  { clause := "restTooMany", refusal := .notASchema,
    detail := "{path} carries {it} rest types, and the admitted subset refuses more than one structurally (trailing-rest semantics stay deferred)" },
  { clause := "emptyTuple", refusal := .notASchema,
    detail := "{path} is the empty tuple, which no constructor spells: a plain array is zero elements and one rest type, a tuple is at least one element" },
  { clause := "elementShape", refusal := .notASchema,
    detail := "{path} does not spell a tuple element: the admitted subset writes {keys} and no annotation bag (C-ann)" },
  { clause := "elementOptionality", refusal := .notASchema,
    detail := "{path}.isOptional is not a boolean" },
  { clause := "indexSignatures", refusal := .notASchema,
    detail := "{path} carries index signatures, which the admitted subset does not reach (records are Slice C3)" },
  { clause := "propertyShape", refusal := .notASchema,
    detail := "{path} does not spell a property signature: the admitted subset writes {keys}" },
  { clause := "propertyMutable", refusal := .notASchema,
    detail := "{path} is mutable, which the admitted subset does not carry" },
  { clause := "propertyOptionality", refusal := .notASchema,
    detail := "{path}.isOptional is not a boolean" },
  { clause := "propertyName", refusal := .notASchema,
    detail := "{path}.name is not a string name (symbol keys have no reconstructable identity)" },
  { clause := "propertyOrder", refusal := .illFormed,
    detail := "{path} declares {it} after {keys}: struct field names are in strict ascending order, which is what makes the canonical spelling unique and forbids a duplicate name" },
  { clause := "declarationShape", refusal := .notASchema,
    detail := "{path}.representation does not spell a declaration identity: the admitted subset writes {keys}" },
  { clause := "unknownDeclaration", refusal := .unknownDeclaration,
    detail := "unknown declaration {it} at {path} — the canonical schema registry admits only {keys}" },
  { clause := "declarationPayload", refusal := .illFormed,
    detail := "{path}: the declaration's registry row does not admit the payload {it}" },
  { clause := "declarationArity", refusal := .illFormed,
    detail := "{path}: the declaration's registry row does not take {it} type parameters" },
  { clause := "unionMode", refusal := .notASchema,
    detail := "{path}.mode is {it}, which is no union mode — the modes are {keys}" },
  { clause := "unionEmpty", refusal := .illFormed,
    detail := "{path} is the empty union, which is Never — and Never is not admitted" },
  { clause := "enumEmpty", refusal := .illFormed,
    detail := "{path} is the empty enum, which names no member — and the empty type is Never, which is not admitted" },
  { clause := "enumMemberShape", refusal := .notASchema,
    detail := "{path} is not a [name, value] pair" },
  { clause := "enumMemberValue", refusal := .notASchema,
    detail := "{path} carries a member value outside the admitted subset: strings and safe integers only (ruling 15, the float ceiling)" },
  { clause := "enumMemberName", refusal := .illFormed,
    detail := "{path} declares the member name {it} twice — member names are the enum's identity and never repeat (values may alias; names may not)" },
  { clause := "documentShape", refusal := .notASchema,
    detail := "{path} does not spell a representation document: the admitted subset writes {keys}" },
  { clause := "referenceName", refusal := .illFormed,
    detail := "{path} names an empty reference: a reference names a references-table entry, and the empty name names none (Effect refuses it too — $ref is a non-empty string)" },
  { clause := "referenceKeyEmpty", refusal := .illFormed,
    detail := "the references table carries an entry under the empty name, which no reference can point at" },
  { clause := "duplicateReferenceKey", refusal := .illFormed,
    detail := "the references table names {it} twice, so the two readers of this payload get two different documents — Lean's parser keeps both entries and takes the first, JSON.parse keeps the last. Give each entry one name; a canonical spelling has its keys in strict ascending order and cannot repeat one" },
  { clause := "unguardedCycle", refusal := .unguardedCycle,
    detail := "the references table has a cycle with no Suspend on it ({it}): resolving it never finishes, because unfolding the name gives the name back. Put the recursive position under a Suspend, which is what Effect writes for a recursive schema" },
  { clause := "nonEmptyReferences", refusal := .nonEmptyReferences,
    detail := "the document allocates a reference table ({it}), and this reader answers a single code — read it as a document instead" },
  { clause := "wrongRevision", refusal := .wrongRevision,
    detail := "unsupported canonical schema revision {it}" },
  { clause := "notASchema", refusal := .notASchema,
    detail := "Effect's persistent decoder does not read this spelling: {it}" },
  { clause := "excessProperties", refusal := .notASchema,
    detail := "canonical schema representation contains unsupported or excess properties" }
]

-- Clause names are unique: the interpreter looks a clause up by name.
#guard decide ((clauses.map (·.clause)).Nodup)

/-! ### The clause table, tied to the door

One representative spelling per family, run through `ingest` at
elaboration. The clause column is a hand table; these are what stop it
from being a hand table that LIES. -/

private def envelopeOf (rep : Cas.Json.Value) : Cas.Json.Value :=
  .obj [("revision", .nat schemaRevision),
    ("value", .obj [("references", .obj []), ("representation", rep)])]

/-- What the door answers for one representation.

This runs the DOCUMENT door, because the document door is what the
emitted table describes and what the TypeScript interpreter mirrors. On
an empty table the two doors give the same answers — `ingestDocument_nil`
is that agreement as a theorem — so every clause tied here before C6 is
tied to the same answer it always was. -/
private def refusalFor (rep : Cas.Json.Value) : String :=
  match ingestDocument (envelopeOf rep) with
  | .ok _ => "admitted"
  | .error r => refusalName r

/-- What the door answers for a whole document, table included. -/
private def documentRefusalFor (refs : List (String × Cas.Json.Value))
    (rep : Cas.Json.Value) : String :=
  match ingestDocument (.obj [("revision", .nat schemaRevision),
      ("value", .obj [("references", .obj refs), ("representation", rep)])]) with
  | .ok _ => "admitted"
  | .error r => refusalName r

/-- What the table says one clause refuses with. -/
private def clauseRefusal (name : String) : String :=
  match clauses.find? (·.clause == name) with
  | some c => refusalName c.refusal
  | none => "no such clause"

private def strRep : Cas.Json.Value := (Ast.str).toRepresentationJson

#guard clauseRefusal "unadmittedNode" ==
  refusalFor (.obj [("_tag", .str "BigInt"), ("checks", .arr [])])

#guard clauseRefusal "checksNotEmpty" ==
  refusalFor (.obj [("_tag", .str "String"),
    ("checks", .arr [fieldOf "checks" (Ast.int).toRepresentationJson])])

#guard clauseRefusal "notTheIntCheck" ==
  refusalFor (.obj [("_tag", .str "Number"), ("checks", .arr [])])

#guard clauseRefusal "literalShape" ==
  refusalFor (.obj [("_tag", .str "Literal"), ("checks", .arr []),
    ("literal", .obj [("type", .str "bigint"), ("value", .str "1")])])

#guard clauseRefusal "emptyTuple" ==
  refusalFor (.obj [("_tag", .str "Arrays"), ("checks", .arr []),
    ("elements", .arr []), ("rest", .arr [])])

#guard clauseRefusal "restTooMany" ==
  refusalFor (.obj [("_tag", .str "Arrays"), ("checks", .arr []),
    ("elements", .arr [elementToRepresentationJson (false, .str)]),
    ("rest", .arr [strRep, strRep])])

#guard clauseRefusal "elementShape" ==
  refusalFor (.obj [("_tag", .str "Arrays"), ("checks", .arr []),
    ("elements", .arr [.obj [("annotations", .obj [("title", .str "first")]),
      ("isOptional", .bool false), ("type", strRep)]]),
    ("rest", .arr [])])

#guard clauseRefusal "indexSignatures" ==
  refusalFor (.obj [("_tag", .str "Objects"), ("checks", .arr []),
    ("indexSignatures", .arr [.obj [("parameter", strRep), ("type", strRep)]]),
    ("propertySignatures", .arr [])])

#guard clauseRefusal "propertyMutable" ==
  refusalFor (.obj [("_tag", .str "Objects"), ("checks", .arr []),
    ("indexSignatures", .arr []),
    ("propertySignatures", .arr [.obj [("isMutable", .bool true),
      ("isOptional", .bool false),
      ("name", .obj [("type", .str "string"), ("value", .str "a")]),
      ("type", strRep)]])])

#guard clauseRefusal "propertyOrder" ==
  refusalFor (Ast.struct [("b", false, .str), ("a", false, .str)]).toRepresentationJson

#guard clauseRefusal "unknownDeclaration" ==
  refusalFor (.obj [("_tag", .str "Declaration"), ("checks", .arr []),
    ("representation", .obj [("id", .str "vendor/x/Widget"), ("payload", .null)]),
    ("typeParameters", .arr [])])

#guard clauseRefusal "declarationPayload" ==
  refusalFor (Ast.decl .date (.str "not a null payload") []).toRepresentationJson

#guard clauseRefusal "declarationArity" ==
  refusalFor (Ast.decl .date .null [.str]).toRepresentationJson

#guard clauseRefusal "unionMode" ==
  refusalFor (.obj [("_tag", .str "Union"), ("checks", .arr []),
    ("mode", .str "allOf"), ("types", .arr [strRep])])

#guard clauseRefusal "unionEmpty" ==
  refusalFor (Ast.union [] .anyOf).toRepresentationJson

#guard clauseRefusal "enumEmpty" == refusalFor (Ast.enum []).toRepresentationJson

#guard clauseRefusal "enumMemberValue" ==
  refusalFor (.obj [("_tag", .str "Enum"), ("checks", .arr []),
    ("enums", .arr [.arr [.str "A",
      .obj [("type", .str "boolean"), ("value", .bool true)]]])])

#guard clauseRefusal "enumMemberName" ==
  refusalFor (Ast.enum [("A", .str "x"), ("A", .str "y")]).toRepresentationJson

#guard clauseRefusal "nonEmptyReferences" ==
  (match ingest (.obj [("revision", .nat schemaRevision),
      ("value", .obj [("references", .obj [("Node", strRep)]),
        ("representation", strRep)])]) with
   | .ok _ => "admitted"
   | .error r => refusalName r)

#guard clauseRefusal "wrongRevision" ==
  (match ingest (.obj [("revision", .nat 7),
      ("value", .obj [("references", .obj []), ("representation", strRep)])]) with
   | .ok _ => "admitted"
   | .error r => refusalName r)

/-! ### The C6 clauses, tied the same way

The table's own disciplines, each run through the document door. -/

private def refNode (n : String) : Cas.Json.Value :=
  (Ast.reference n).toRepresentationJson

#guard clauseRefusal "referenceName" == refusalFor (refNode "")

#guard clauseRefusal "referenceKeyEmpty" ==
  documentRefusalFor [("", strRep)] (refNode "")

-- THE DUPLICATE TABLE KEY, both directions, one name. Which pair a
-- parser keeps is its own habit, so the door refuses the spelling
-- before it decodes anything (PDD-3 break-pass finding F1, assumed
-- ruling). The TypeScript side reads this from the BYTES, because
-- `JSON.parse` has thrown one of the pairs away by the time any gate
-- could look.
#guard clauseRefusal "duplicateReferenceKey" ==
  documentRefusalFor [("A", refNode "A"), ("A", strRep)] strRep

#guard clauseRefusal "duplicateReferenceKey" ==
  documentRefusalFor [("A", strRep), ("A", refNode "A")] strRep

-- The partner: two entries under two different names is an ordinary
-- table, so the clause is not satisfied by refusing every table.
#guard "admitted" ==
  documentRefusalFor [("A", refNode "B"), ("B", strRep)] strRep

-- THE TABLE'S KEY ORDER IS NOT A REFUSAL, and there is deliberately no
-- clause for it. The table is a JSON OBJECT, so `canonValue` sorts its
-- keys on the way in exactly as it sorts any object's — an out-of-order
-- table is NORMALIZED, not turned away. (Contrast a struct's fields,
-- which ride in an ARRAY that nothing sorts, which is why
-- `propertyOrder` IS a clause.) The strict-order conjunct of
-- `Document.WF` earns its place on the ENCODE side instead: it is what
-- `Document.representationDocument_canonical` needs.
#guard "admitted" ==
  documentRefusalFor [("B", strRep), ("A", refNode "B")] (refNode "A")

-- THE UNGUARDED CYCLE, both shapes: the alias chain and the bare
-- structural loop. Neither has a `Suspend` anywhere on it.
#guard clauseRefusal "unguardedCycle" ==
  documentRefusalFor [("A", refNode "B"), ("B", refNode "A")] (refNode "A")

#guard clauseRefusal "unguardedCycle" ==
  documentRefusalFor
    [("A", (Ast.struct [("next", false, .reference "A")]).toRepresentationJson)]
    (refNode "A")

-- AND THE PARTNER CALL, which is what stops the clause above from
-- being satisfied by a door that refuses every table: the recursion
-- Effect actually emits — a cycle THROUGH a `Suspend` — is admitted.
#guard "admitted" ==
  documentRefusalFor
    [("Node", (Ast.struct
        [("next", false, .susp (.union [.reference "Node", .null] .anyOf)),
          ("value", false, .str)]).toRepresentationJson)]
    (refNode "Node")

/-! ## The emission

The table as one TypeScript module: the types the interpreter reads it
at, then the columns. Layout is the house printer's; nothing here
chooses bytes by hand. -/

mutual

/-- One JSON value as a TypeScript expression — how the admitted check
spelling reaches the generated module without being retyped. -/
def jsonExpr : Cas.Json.Value → Expr
  | .null => .jsNull
  | .bool b => .bool b
  | .nat n => .int (Int.ofNat n)
  | .int i => .int i
  | .str s => .str s
  | .arr xs => .arr (jsonExprItems xs)
  | .obj fs => .object (jsonExprFields fs)

def jsonExprItems : List Cas.Json.Value → List Expr
  | [] => []
  | v :: vs => jsonExpr v :: jsonExprItems vs

def jsonExprFields : List (String × Cas.Json.Value) → List (String × Expr)
  | [] => []
  | (k, v) :: fs => (k, jsonExpr v) :: jsonExprFields fs

end

private def strings (xs : List String) : Expr := .arr (xs.map .str)

/-- The one admitted check, as the canonical JSON the TypeScript reader
compares against — the projection's own bytes, not a transcription. -/
def isIntCheckSpelling : String :=
  match fieldOf "checks" (Ast.int).toRepresentationJson with
  | .arr [c] => Cas.Json.renderCompact c
  | _ => ""

private def union (xs : List String) : String :=
  String.intercalate " | " (xs.map fun x => "\"" ++ x ++ "\"")

/-- The types the generated table is read at. A raw block: these are
TypeScript declarations, not expressions, and the fragment the printer
carries is deliberately expression-only. -/
private def typeBlock : String :=
  "/** THE refusal taxonomy, verbatim from Lean `Cas.Schema.IngestRefusal`:\n" ++
  " * the two doors name the same refusals or they are not two doors onto\n" ++
  " * one language. */\n" ++
  "export type Refusal = " ++ union (refusals.map refusalName) ++ "\n\n" ++
  "/** One discipline clause: the name the interpreter looks it up by, the\n" ++
  " * refusal it carries, and the prose it reads. `{path}`, `{it}` and\n" ++
  " * `{keys}` are the interpreter's three substitutions. */\n" ++
  "export interface Clause {\n" ++
  "  readonly clause: string\n" ++
  "  readonly refusal: Refusal\n" ++
  "  readonly detail: string\n" ++
  "}\n\n" ++
  "/** Which arm of the interpreter reads a node. */\n" ++
  "export type Form = " ++ union (nodes.map NodeRow.form).eraseDups ++ "\n\n" ++
  "/** One admitted representation node: its tag, the arm that reads it,\n" ++
  " * the keys the canonical spelling writes, and its checks policy.\n" ++
  " * `none` is the Reference row: that node carries no `checks` key at\n" ++
  " * all, so there is no array for a policy to be about. */\n" ++
  "export interface NodeRow {\n" ++
  "  readonly tag: string\n" ++
  "  readonly form: Form\n" ++
  "  readonly keys: ReadonlyArray<string>\n" ++
  "  readonly checks: " ++ union (nodes.map NodeRow.checks).eraseDups ++ "\n" ++
  "}\n\n" ++
  "/** One admitted `{type, value}` spelling: the type tag the projection\n" ++
  " * writes, and the predicate the reader applies to the value. */\n" ++
  "export interface TypedValueRow {\n" ++
  "  readonly type: string\n" ++
  "  readonly admits: \"boolean\" | \"safeInteger\" | \"string\"\n" ++
  "}\n\n" ++
  "/** A declaration row's payload discipline, mirroring Lean\n" ++
  " * `DeclarationId.payloadWf`: `byte` is a natural number below\n" ++
  " * `PayloadByteBound` (a kind tag), `null` is the null payload. */\n" ++
  "export type DeclarationPayload = " ++
    union ((declarations.map (·.2.2)).eraseDups) ++ "\n\n" ++
  "/** One row of the declaration registry, without its reviver: the\n" ++
  " * persistence identity, the type parameters it takes, and the payload\n" ++
  " * its row admits. */\n" ++
  "export interface DeclarationRow {\n" ++
  "  readonly id: string\n" ++
  "  readonly arity: number\n" ++
  "  readonly payload: DeclarationPayload\n" ++
  "}"

private def clauseExpr (c : Clause) : Expr :=
  .objectML [("clause", .str c.clause),
    ("refusal", .str (refusalName c.refusal)),
    ("detail", .str c.detail)]

private def nodeExpr (r : NodeRow) : Expr :=
  .objectML [("tag", .str r.tag), ("form", .str r.form),
    ("keys", strings r.keys), ("checks", .str r.checks)]

private def typedExpr (r : String × String) : Expr :=
  .object [("type", .str r.1), ("admits", .str r.2)]

private def declExpr (r : String × Nat × String) : Expr :=
  .objectML [("id", .str r.1), ("arity", .int (Int.ofNat r.2.1)),
    ("payload", .str r.2.2)]

/-- One exported column of the table. -/
private def entry (name : String) (ty : Option String) (doc : List String)
    (value : Expr) : Decl :=
  .const { doc, name, type := ty, value }

/-- A column whose inferred type is already the right one. -/
private def plain (name : String) (doc : List String) (value : Expr) : Decl :=
  entry name none doc value

private def keyList (name : String) (what : String) (keys : List String) : Decl :=
  entry name (some "ReadonlyArray<string>")
    ["The keys " ++ what ++ " writes."] (strings keys)

def decls : List Decl := [
  .raw typeBlock,
  entry "Refusals" (some "ReadonlyArray<Refusal>")
    ["Every refusal the door can name, in Lean's declaration order."]
    (strings (refusals.map refusalName)),
  entry "Clauses" (some "ReadonlyArray<Clause>")
    ["The discipline clauses, by name."]
    (.arr (clauses.map clauseExpr)),
  entry "Nodes" (some "ReadonlyArray<NodeRow>")
    ["The admitted representation nodes. `Arrays` is ONE row: the plain",
      "array and the tuple are one tag and one key list, told apart by",
      "whether `elements` is empty, exactly as the Lean decoder tells them",
      "apart."]
    (.arr (nodes.map nodeExpr)),
  plain "IsIntCheckSpelling"
    ["THE admitted check spelling, as its canonical JSON: Effect's",
      "`effect/schema/isInt`, read off the `Number` node's own projection",
      "and rendered by the canonical encoder rather than retyped. The",
      "interpreter compares `canonicalJson(checks[0])` against this."]
    (.str isIntCheckSpelling),
  entry "LiteralTypes" (some "ReadonlyArray<TypedValueRow>")
    ["The admitted literal spellings."]
    (.arr (literalTypes.map typedExpr)),
  entry "EnumValueTypes" (some "ReadonlyArray<TypedValueRow>")
    ["The admitted enum member value spellings."]
    (.arr (enumValueTypes.map typedExpr)),
  entry "UnionModes" (some "ReadonlyArray<string>")
    ["The union modes, from `Cas.Schema.UnionMode`."]
    (strings (UnionMode.all.map UnionMode.wire)),
  entry "Declarations" (some "ReadonlyArray<DeclarationRow>")
    ["THE declaration registry's columns, from `Cas.Schema.DeclarationId`,",
      "row zero first. The payload column is probed out of",
      "`DeclarationId.payloadWf`, not transcribed."]
    (.arr (declarations.map declExpr)),
  keyList "PropertyKeys" "one property signature" propertyKeys,
  keyList "PropertyNameKeys" "a property signature's `name` slot" propertyNameKeys,
  keyList "ElementKeys" "one tuple element" elementKeys,
  keyList "LiteralKeys" "a literal's typed value" literalKeys,
  keyList "EnumValueKeys" "an enum member's value" enumValueKeys,
  keyList "DeclarationIdentityKeys" "a declaration identity"
    declarationIdentityKeys,
  keyList "DocumentKeys" "the representation document" documentKeys,
  keyList "EnvelopeKeys" "the schema-node envelope" envelopeKeys,
  plain "PayloadByteBound"
    ["The kind-tag bound a `byte` payload obeys, counted out of",
      "`DeclarationId.payloadWf` rather than restated."]
    (.int (Int.ofNat payloadByteBound)),
  plain "MaxSafeInteger"
    ["The safe-integer bound (`Cas.Schema.maxSafeNat`): the one number",
      "range whose decimal rendering is language-neutral (CAS-004)."]
    (.int (Int.ofNat maxSafeNat)),
  plain "Revision" ["The revision the door speaks."]
    (.int (Int.ofNat schemaRevision)),
  plain "LegacyRevision"
    ["The retired revision, kept readable for already-addressed nodes."]
    (.int (Int.ofNat legacySchemaRevision))
]

def module : Ts.Module where
  header := [
    "GENERATED — do not edit. THE ADMISSION TABLE: what",
    "`Cas.Schema.ingest` admits, as data, emitted from",
    "`library/cas/Cas/Backend/Admission.lean` by `lake exe emitgate`;",
    "regeneration is byte-identity-gated (`--check`, wired into",
    "`check:cas`).",
    "",
    "`CanonicalSchema.admitDocument` is an interpreter over this table.",
    "Every column here is read off the Lean definitions — the node tags",
    "and key lists off `Ast.toRepresentationJson`, the check spelling off",
    "the `Number` node's own projection, the declaration payload column",
    "probed out of `DeclarationId.payloadWf` — except the clause table,",
    "which is a hand column tied to `ingest`'s answers by `#guard`.",
    "",
    "The key lists are the REQUIRED keys, not an exact set: Effect's own",
    "`toJson` writes an `annotations` bag on a `Declaration` node that",
    "the Lean spelling does not carry, so exact-key enforcement would",
    "refuse three registry rows as they are actually stored. That gap is",
    "a ruling, recorded in Admission.lean, not a translation."
  ]
  imports := []
  decls := decls

def rendered : String := Render.module house0 module

end Cas.Backend.Admission
