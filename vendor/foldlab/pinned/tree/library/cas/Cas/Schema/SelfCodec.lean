import Cas.Schema.Ast
import Cas.Values.Json

/-!
# Self-description — a code is a value

The named third increment of the schema plane: the codes' own JSON
projection, the schema-node envelope, and the canonical payload — the
Lean twin of the TypeScript side's `CanonicalSchema.payloadOf`.
Revision 1 stores Effect's native persistent `SchemaRepresentation`
document. Revision 0's tagged projection remains below as the strict
compatibility decoder for already-addressed schema nodes.
This is the cross-runtime pin surface: the same code must yield the
same payload bytes in both runtimes, and `lake exe schemas --check`
holds the committed fixtures to it.

The projection is total and structural; the byte-level rendering
theorem binding it to `encode` and the store envelope remains the
increment's open obligation (pending, per the facade's increment
list) — nothing here claims it.

The OTHER direction — "bytes determine the canonical value", i.e.
injectivity of the payload — is PROVED in `Cas.Schema.PayloadInj`
(`payload_inj`, `payload_inj'`, `payloadBytes_inj`), unconditionally.
It rests on `Cas.Json.renderPlain_injective` (`Cas.Values.JsonParse`,
from the strict parser), which was this lane's last named open
obligation.
-/

namespace Cas.Schema

/-- The `.schema` sort's wire kind tag (grammar-grill ruling 3; the
Lean carrier of the TypeScript `SchemaKindTag`). -/
def schemaKindTag : UInt8 := 0x53

/-- The schema-node envelope revision (TS `CanonicalSchema.Revision`). -/
def schemaRevision : Nat := 1

/-- The retired tagged-projection revision, retained for read compatibility. -/
def legacySchemaRevision : Nat := 0

/-- A pinned literal as a JSON value. -/
def LitVal.toJson : LitVal → Json.Value
  | .null => .null
  | .bool b => .bool b
  | .int i => .int i.val
  | .str s => .str s

/-! ### The enum's member list — one spelling, both revisions

An enum member carries no code, so its projection is not part of the
recursion over `Ast` and lives outside the mutual blocks. There is ONE
spelling of a member pair, and both revisions use it: Effect's own
`[name, {type, value}]`. Revision 0 is a read-compatibility arm and has
no legacy enum bytes to be compatible with — inventing a second
spelling for it would be a second thing to keep in step, for nothing. -/

/-- An enum member's value, in Effect's typed-value spelling
(`makeValueSchema`, `SchemaRepresentation.ts:990-999`). -/
def EnumValue.toJson : EnumValue → Json.Value
  | .str s => .obj [("type", .str "string"), ("value", .str s)]
  | .int i => .obj [("type", .str "number"), ("value", .int i.val)]

/-- One enum member: the positional `[name, value]` pair Effect
persists. -/
def enumMemberToJson (m : String × EnumValue) : Json.Value :=
  .arr [.str m.1, m.2.toJson]

/-- An enum's members, in order — the order they were written, which is
`Object.keys` order on Effect's side and therefore SOURCE order. There
is no sort here, on the way in or out. -/
def enumMembersToJson : List (String × EnumValue) → List Json.Value
  | [] => []
  | m :: ms => enumMemberToJson m :: enumMembersToJson ms

/-- The strict decoder of a member value: exactly the two spellings
`EnumValue.toJson` emits. -/
def EnumValue.ofJson : Json.Value → Option EnumValue
  | .obj [("type", .str "string"), ("value", .str s)] => some (.str s)
  | .obj [("type", .str "number"), ("value", .int i)] =>
    if h : i.natAbs ≤ maxSafeNat then some (.int ⟨i, h⟩) else none
  | _ => none

/-- The member-list decoder, preserving order verbatim. -/
def enumMembersOfJson : List Json.Value → Option (List (String × EnumValue))
  | [] => some []
  | .arr [.str n, v] :: rest =>
    (EnumValue.ofJson v).bind fun ev =>
    (enumMembersOfJson rest).map fun ms => (n, ev) :: ms
  | _ => none

theorem EnumValue.ofJson_toJson (v : EnumValue) :
    EnumValue.ofJson v.toJson = some v := by
  cases v with
  | int i => simp only [EnumValue.toJson, EnumValue.ofJson, dif_pos i.property]
  | str _ => rfl

theorem enumMembersOfJson_toJson :
    ∀ (ms : List (String × EnumValue)),
      enumMembersOfJson (enumMembersToJson ms) = some ms
  | [] => rfl
  | (n, v) :: ms => by
    simp only [enumMembersToJson, enumMemberToJson, enumMembersOfJson,
      EnumValue.ofJson_toJson v, enumMembersOfJson_toJson ms,
      Option.bind_some, Option.map_some]

mutual

/-- The retired revision-0 tagged JSON projection of a code (`_tag`
discriminated; struct fields as a name-keyed record of `{optional, schema}`).
Key order here is immaterial: the canonical rendering sorts at render time. -/
def Ast.toJson : Ast → Json.Value
  | .null => .obj [("_tag", .str "Null")]
  | .bool => .obj [("_tag", .str "Boolean")]
  | .int => .obj [("_tag", .str "Integer")]
  | .str => .obj [("_tag", .str "String")]
  | .lit v => .obj [("_tag", .str "Literal"), ("value", v.toJson)]
  | .arr a => .obj [("_tag", .str "Array"), ("item", a.toJson)]
  | .struct fs => .obj [("_tag", .str "Struct"), ("fields", .obj (fieldsToJson fs))]
  | .ref t => .obj [("_tag", .str "Ref"), ("tag", .nat t.toNat)]
  | .decl id p ps => .obj [
      ("_tag", .str "Decl"),
      ("id", .str id.wire),
      ("payload", p.toJson),
      ("typeParameters", .arr (paramsToJson ps))]
  | .union ms m => .obj [
      ("_tag", .str "Union"),
      ("members", .arr (membersToJson ms)),
      ("mode", .str m.wire)]
  | .enum ms => .obj [
      ("_tag", .str "Enum"),
      ("members", .arr (enumMembersToJson ms))]
  | .tuple e es r => .obj [
      ("_tag", .str "Tuple"),
      ("elements", .arr (elementToJson e :: elementsToJson es)),
      ("rest", .arr (restToJson r))]
  -- The C6 codes at the RETIRED revision. No revision-0 schema node in
  -- the store carries one — revision 0 was retired before this
  -- increment, so these spellings address nothing and mint nothing.
  -- They exist so the retired projection stays TOTAL and its round trip
  -- (`ingestLegacy_toJson`) stays unconditional over the grown carrier;
  -- the alternative was a landed theorem acquiring a hypothesis, which
  -- is the worse trade.
  | .reference n => .obj [("_tag", .str "Reference"), ("name", .str n)]
  | .susp a => .obj [("_tag", .str "Suspend"), ("thunk", a.toJson)]

/-- One record entry per struct field: `name ↦ {optional, schema}`. -/
def fieldsToJson : List (String × Bool × Ast) → List (String × Json.Value)
  | [] => []
  | (name, opt, a) :: fs =>
    (name, .obj [("optional", .bool opt), ("schema", a.toJson)]) :: fieldsToJson fs

/-- A declaration's type parameters, in order. -/
def paramsToJson : List Ast → List Json.Value
  | [] => []
  | a :: as => a.toJson :: paramsToJson as

/-- A union's members, in order — the order they were written, which
is the order they are stored in and read back in. -/
def membersToJson : List Ast → List Json.Value
  | [] => []
  | a :: as => a.toJson :: membersToJson as

/-- One tuple element: `{optional, schema}`, the same pair a struct
field carries under its name. -/
def elementToJson : Bool × Ast → Json.Value
  | (opt, a) => .obj [("optional", .bool opt), ("schema", a.toJson)]

/-- A tuple's elements, in position order — position is the identity, so
there is no arrangement to normalize. -/
def elementsToJson : List (Bool × Ast) → List Json.Value
  | [] => []
  | e :: es => elementToJson e :: elementsToJson es

/-- A tuple's rest type: the empty list, or the one type. -/
def restToJson : Option Ast → List Json.Value
  | none => []
  | some a => [a.toJson]

end

/-! ## Effect Schema's persistent representation

The project-owned `Ast` remains the denotation (I-004). This projection
is the exact native Effect v4 `SchemaRepresentation.toJson` image of the
generated Effect Schema for the supported closed fragment. TypeScript
therefore consumes Effect's AST and representation directly; it does not
define a second schema-code algebra.
-/

private def keywordRepresentation (tag : String) : Json.Value :=
  .obj [("_tag", .str tag), ("checks", .arr [])]

private def intCheck : Json.Value :=
  .obj [
    ("_tag", .str "Filter"),
    ("aborted", .bool false),
    ("annotations", .obj [
      ("arbitrary", .obj [
        ("constraint", .obj [("integer", .bool true)])]),
      ("expected", .str "an integer")]),
    ("representation", .obj [
      ("id", .str "effect/schema/isInt"),
      ("payload", .null)])]

mutual

/-- Effect's native persistent representation of one schema code. -/
def Ast.toRepresentationJson : Ast → Json.Value
  | .null => keywordRepresentation "Null"
  | .bool => keywordRepresentation "Boolean"
  | .int => .obj [
      ("_tag", .str "Number"),
      ("checks", .arr [intCheck])]
  | .str => keywordRepresentation "String"
  | .lit .null => keywordRepresentation "Null"
  | .lit (.bool b) => .obj [
      ("_tag", .str "Literal"),
      ("checks", .arr []),
      ("literal", .obj [("type", .str "boolean"), ("value", .bool b)])]
  | .lit (.int i) => .obj [
      ("_tag", .str "Literal"),
      ("checks", .arr []),
      ("literal", .obj [("type", .str "number"), ("value", .int i.val)])]
  | .lit (.str s) => .obj [
      ("_tag", .str "Literal"),
      ("checks", .arr []),
      ("literal", .obj [("type", .str "string"), ("value", .str s)])]
  | .arr a => .obj [
      ("_tag", .str "Arrays"),
      ("checks", .arr []),
      ("elements", .arr []),
      ("rest", .arr [a.toRepresentationJson])]
  | .struct fs => .obj [
      ("_tag", .str "Objects"),
      ("checks", .arr []),
      ("indexSignatures", .arr []),
      ("propertySignatures", .arr (fieldsToRepresentationJson fs))]
  | .ref tag => .obj [
      ("_tag", .str "Declaration"),
      ("checks", .arr []),
      ("representation", .obj [
        ("id", .str "foldlab/cas/ref"),
        ("payload", .nat tag.toNat)]),
      ("typeParameters", .arr [])]
  | .decl id p ps => .obj [
      ("_tag", .str "Declaration"),
      ("checks", .arr []),
      ("representation", .obj [
        ("id", .str id.wire),
        ("payload", p.toJson)]),
      ("typeParameters", .arr (paramsToRepresentationJson ps))]
  | .union ms m => .obj [
      ("_tag", .str "Union"),
      ("checks", .arr []),
      ("mode", .str m.wire),
      ("types", .arr (membersToRepresentationJson ms))]
  | .enum ms => .obj [
      ("_tag", .str "Enum"),
      ("checks", .arr []),
      ("enums", .arr (enumMembersToJson ms))]
  | .tuple e es r => .obj [
      ("_tag", .str "Arrays"),
      ("checks", .arr []),
      ("elements", .arr (elementToRepresentationJson e ::
        elementsToRepresentationJson es)),
      ("rest", .arr (restToRepresentationJson r))]
  -- `$ref` sorts BEFORE `_tag` — `$` is 0x24 and `_` is 0x5F — so this
  -- is the only admitted node whose tag is not the first key. The order
  -- is the canonical one, not a choice; `reference_canonical` proves it.
  | .reference n => .obj [
      ("$ref", .str n),
      ("_tag", .str "Reference")]
  | .susp a => .obj [
      ("_tag", .str "Suspend"),
      ("checks", .arr []),
      ("thunk", a.toRepresentationJson)]

/-- Effect property-signature representations, preserving canonical field order. -/
def fieldsToRepresentationJson : List (String × Bool × Ast) → List Json.Value
  | [] => []
  | (name, opt, a) :: fs =>
    .obj [
      ("isMutable", .bool false),
      ("isOptional", .bool opt),
      ("name", .obj [("type", .str "string"), ("value", .str name)]),
      ("type", a.toRepresentationJson)] :: fieldsToRepresentationJson fs

/-- A declaration's type-parameter representations, in order. -/
def paramsToRepresentationJson : List Ast → List Json.Value
  | [] => []
  | a :: as => a.toRepresentationJson :: paramsToRepresentationJson as

/-- A union's member representations, in order. The emitter has no
sort: `types` comes out in exactly the order the code holds, which is
what makes the payload bytes carry the identity. -/
def membersToRepresentationJson : List Ast → List Json.Value
  | [] => []
  | a :: as => a.toRepresentationJson :: membersToRepresentationJson as

/-- One Effect element representation. Effect's own `ElementSchema` is
`{isOptional, type, annotations}` (`SchemaRepresentation.ts:1028-1032`);
the annotation bag is elided when empty, exactly as it is on a property
signature. -/
def elementToRepresentationJson : Bool × Ast → Json.Value
  | (opt, a) =>
    .obj [("isOptional", .bool opt), ("type", a.toRepresentationJson)]

/-- Effect element representations, in position order. -/
def elementsToRepresentationJson : List (Bool × Ast) → List Json.Value
  | [] => []
  | e :: es =>
    elementToRepresentationJson e :: elementsToRepresentationJson es

/-- A tuple's rest, as Effect's `rest` array: empty, or the one type.
Length two or more has no spelling on this side at all — the carrier
holds an `Option` — so the deferred trailing-rest semantics are refused
by construction rather than by a clause. -/
def restToRepresentationJson : Option Ast → List Json.Value
  | none => []
  | some a => [a.toRepresentationJson]

end

/-- Effect's single-root persistent representation document. -/
def Ast.representationDocument (a : Ast) : Json.Value :=
  .obj [
    ("references", .obj []),
    ("representation", a.toRepresentationJson)]

/-- The retired revision-0 envelope, retained as a decoder pin. -/
def Ast.legacyEnvelope (a : Ast) : Json.Value :=
  .obj [("revision", .nat legacySchemaRevision), ("value", a.toJson)]

/-- The revision-1 schema-node envelope. -/
def Ast.envelope (a : Ast) : Json.Value :=
  .obj [("revision", .nat schemaRevision), ("value", a.representationDocument)]

/-- THE canonical payload: the compact canonical rendering of the
envelope — byte-for-byte the TypeScript `CanonicalSchema.payloadOf`. -/
def Ast.payload (a : Ast) : String :=
  Json.renderCompact a.envelope

/-- The payload's UTF-8 bytes — what the schema node carries and what
its content identity is computed over. -/
def Ast.payloadBytes (a : Ast) : ByteArray :=
  a.payload.toUTF8

end Cas.Schema

namespace Cas.Schema

/-! ## The revision-0 projection's laws — canonical spelling, decode, round trip

The self-codec inherits the plane's discipline: under `WF` the
retired tagged projection is canonically spelled
(`toJson_canonical`, `legacyEnvelope_canonical`,
`legacyEnvelope_renderPlain`), and `ofJson` is its strict decoder
with the round trip proved (`ofJson_toJson`), making the projection
injective (`toJson_inj`): one code per projection value. Every law
below is about revision 0. The live revision-1 representation
(`toRepresentationJson`/`envelope`/`payload`) has no canonicality
theorem, no decoder, and no round trip yet — it is held by the
cross-runtime byte pin alone, and its laws are the named open
obligation of this module. -/

open Cas.Json

/-- A pinned literal's image is scalar, hence canonical. -/
theorem LitVal.toJson_canonical (v : LitVal) : v.toJson.Canonical := by
  cases v <;> trivial

/-- An enum member value's image is canonically spelled
(`"type" < "value"`). -/
theorem EnumValue.toJson_canonical (v : EnumValue) : v.toJson.Canonical := by
  cases v <;>
    exact ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["type", "value"]),
      trivial, trivial, trivial⟩

/-- An enum's member list is canonically spelled. There is no premise
about the ORDER — the pairs are array items, not object keys, so no
sort has anything to say about them, which is the point. -/
theorem enumMembersToJson_canonical :
    ∀ (ms : List (String × EnumValue)),
      CanonicalItems (enumMembersToJson ms)
  | [] => trivial
  | (_, v) :: ms =>
    ⟨⟨trivial, EnumValue.toJson_canonical v, trivial⟩,
      enumMembersToJson_canonical ms⟩

/-- The field record preserves the struct's key list verbatim. -/
theorem fieldsToJson_keys (fs : List (String × Bool × Ast)) :
    (fieldsToJson fs).map (·.1) = fs.map (fun f => f.1) := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨n, opt, a⟩ := f
    simp [fieldsToJson, ih]

mutual

/-- Under a well-formed code the projection is canonically spelled:
`_tag` leads every discriminated object, the fields record inherits
the struct's strict order, and `optional < schema` holds inside every
field entry. -/
theorem toJson_canonical : ∀ (a : Ast), a.WF → a.toJson.Canonical
  | .null, _ => by
    exact ⟨List.pairwise_singleton _ _, trivial, trivial⟩
  | .bool, _ => by
    exact ⟨List.pairwise_singleton _ _, trivial, trivial⟩
  | .int, _ => by
    exact ⟨List.pairwise_singleton _ _, trivial, trivial⟩
  | .str, _ => by
    exact ⟨List.pairwise_singleton _ _, trivial, trivial⟩
  | .lit v, _ => by
    refine ⟨?_, trivial, LitVal.toJson_canonical v, trivial⟩
    refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at hb
    subst hb
    show ("_tag" : String) < "value"
    decide
  | .arr a, ha => by
    refine ⟨?_, trivial, toJson_canonical a ha, trivial⟩
    refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at hb
    subst hb
    show ("_tag" : String) < "item"
    decide
  | .struct fs, ⟨hsorted, hwf⟩ => by
    refine ⟨?_, trivial, ⟨?_, fieldsToJson_canonical fs hwf⟩, trivial⟩
    · refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
      simp only [List.mem_singleton] at hb
      subst hb
      show ("_tag" : String) < "fields"
      decide
    · refine (List.pairwise_map).mp ?_
      rw [fieldsToJson_keys fs]
      exact (List.pairwise_map).mpr hsorted
  | .ref t, _ => by
    refine ⟨?_, trivial, trivial, trivial⟩
    refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at hb
    subst hb
    show ("_tag" : String) < "tag"
    decide
  | .decl _ p ps, ⟨_, _, hps⟩ => by
    refine ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·) ["_tag", "id", "payload", "typeParameters"]),
      trivial, trivial, DeclPayload.toJson_canonical p,
      paramsToJson_canonical ps hps, trivial⟩
  | .union ms _, ⟨_, hms⟩ => by
    refine ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "members", "mode"]),
      trivial, membersToJson_canonical ms hms, trivial, trivial⟩
  | .enum ms, _ => by
    refine ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "members"]),
      trivial, enumMembersToJson_canonical ms, trivial⟩
  | .tuple e es r, ⟨he, hes, hr⟩ => by
    refine ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "elements", "rest"]),
      trivial, ⟨elementToJson_canonical e he, elementsToJson_canonical es hes⟩,
      restToJson_canonical r hr, trivial⟩
  | .reference _, _ => by
    refine ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "name"]),
      trivial, trivial, trivial⟩
  | .susp a, ha => by
    refine ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "thunk"]),
      trivial, toJson_canonical a ha, trivial⟩

theorem membersToJson_canonical :
    ∀ (ms : List Ast), WFMembers ms → CanonicalItems (membersToJson ms)
  | [], _ => trivial
  | a :: as, ⟨ha, has⟩ =>
    ⟨toJson_canonical a ha, membersToJson_canonical as has⟩

theorem elementToJson_canonical :
    ∀ (e : Bool × Ast), WFElement e → (elementToJson e).Canonical
  | (_, a), ha => by
    refine ⟨?_, trivial, toJson_canonical a ha, trivial⟩
    exact List.pairwise_map.mp
      (by decide : List.Pairwise (· < ·) ["optional", "schema"])

theorem elementsToJson_canonical :
    ∀ (es : List (Bool × Ast)), WFElements es →
      CanonicalItems (elementsToJson es)
  | [], _ => trivial
  | e :: es, ⟨he, hes⟩ =>
    ⟨elementToJson_canonical e he, elementsToJson_canonical es hes⟩

theorem restToJson_canonical :
    ∀ (r : Option Ast), WFRest r → CanonicalItems (restToJson r)
  | none, _ => trivial
  | some a, ha => ⟨toJson_canonical a ha, trivial⟩

theorem paramsToJson_canonical :
    ∀ (ps : List Ast), WFParams ps → CanonicalItems (paramsToJson ps)
  | [], _ => trivial
  | a :: as, ⟨ha, has⟩ =>
    ⟨toJson_canonical a ha, paramsToJson_canonical as has⟩

theorem fieldsToJson_canonical :
    ∀ (fs : List (String × Bool × Ast)), WFFields fs →
      CanonicalFields (fieldsToJson fs)
  | [], _ => trivial
  | (n, opt, a) :: fs, ⟨ha, hwf⟩ => by
    refine ⟨⟨?_, trivial, toJson_canonical a ha, trivial⟩,
      fieldsToJson_canonical fs hwf⟩
    refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
    simp only [List.mem_singleton] at hb
    subst hb
    show ("optional" : String) < "schema"
    decide

end

/-- The retired envelope of a well-formed code is canonical
(`"revision" < "value"`). -/
theorem legacyEnvelope_canonical {a : Ast} (ha : a.WF) :
    a.legacyEnvelope.Canonical := by
  refine ⟨?_, trivial, toJson_canonical a ha, trivial⟩
  refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
  simp only [List.mem_singleton] at hb
  subst hb
  show ("revision" : String) < "value"
  decide

/-- The revision-0 byte binding retained for compatibility auditing. -/
theorem legacyEnvelope_renderPlain {a : Ast} (ha : a.WF) :
    Json.renderCompact a.legacyEnvelope = Json.renderPlain a.legacyEnvelope :=
  Json.renderCompact_eq_renderPlain _ (legacyEnvelope_canonical ha)

/-! ## The strict decoder and the round trip -/

def LitVal.ofJson : Json.Value → Option LitVal
  | .null => some .null
  | .bool b => some (.bool b)
  | .int i =>
    if h : i.natAbs ≤ maxSafeNat then some (.int ⟨i, h⟩) else none
  | .str s => some (.str s)
  | _ => none

theorem LitVal.ofJson_toJson (v : LitVal) : LitVal.ofJson v.toJson = some v := by
  cases v with
  | int i =>
    simp only [LitVal.toJson, LitVal.ofJson, dif_pos i.property]
  | _ => rfl

mutual

/-- The strict decoder of the projection: exactly the spellings
`toJson` emits, nothing else. -/
def Ast.ofJson : Json.Value → Option Ast
  | .obj [("_tag", .str "Null")] => some .null
  | .obj [("_tag", .str "Boolean")] => some .bool
  | .obj [("_tag", .str "Integer")] => some .int
  | .obj [("_tag", .str "String")] => some .str
  | .obj [("_tag", .str "Literal"), ("value", v)] =>
    (LitVal.ofJson v).map .lit
  | .obj [("_tag", .str "Array"), ("item", v)] =>
    (Ast.ofJson v).map .arr
  | .obj [("_tag", .str "Struct"), ("fields", .obj kvs)] =>
    (ofJsonFields kvs).map .struct
  | .obj [("_tag", .str "Ref"), ("tag", .nat t)] =>
    if _h : t < 256 then some (.ref (UInt8.ofNat t)) else none
  | .obj [("_tag", .str "Decl"), ("id", .str w), ("payload", p),
      ("typeParameters", .arr tps)] =>
    match DeclarationId.General.ofWire w with
    | none => none
    | some g =>
      (DeclPayload.ofJson p).bind fun pay =>
      (ofJsonParams tps).map fun ps => .decl g pay ps
  | .obj [("_tag", .str "Union"), ("members", .arr ms), ("mode", .str w)] =>
    match UnionMode.ofWire w with
    | none => none
    | some m => (ofJsonMembers ms).map fun bs => .union bs m
  | .obj [("_tag", .str "Enum"), ("members", .arr ms)] =>
    (enumMembersOfJson ms).map .enum
  | .obj [("_tag", .str "Tuple"), ("elements", .arr (e :: es)),
      ("rest", .arr rs)] =>
    (ofJsonElement e).bind fun x =>
    (ofJsonElements es).bind fun xs =>
    (ofJsonRest rs).map fun r => .tuple x xs r
  | .obj [("_tag", .str "Reference"), ("name", .str n)] => some (.reference n)
  | .obj [("_tag", .str "Suspend"), ("thunk", v)] => (Ast.ofJson v).map .susp
  | _ => none

def ofJsonFields :
    List (String × Json.Value) → Option (List (String × Bool × Ast))
  | [] => some []
  | (n, .obj [("optional", .bool opt), ("schema", v)]) :: rest =>
    (Ast.ofJson v).bind fun a =>
    (ofJsonFields rest).map fun fs => (n, opt, a) :: fs
  | _ => none

def ofJsonParams : List Json.Value → Option (List Ast)
  | [] => some []
  | v :: vs =>
    (Ast.ofJson v).bind fun a =>
    (ofJsonParams vs).map fun as => a :: as

def ofJsonMembers : List Json.Value → Option (List Ast)
  | [] => some []
  | v :: vs =>
    (Ast.ofJson v).bind fun a =>
    (ofJsonMembers vs).map fun as => a :: as

def ofJsonElement : Json.Value → Option (Bool × Ast)
  | .obj [("optional", .bool opt), ("schema", v)] =>
    (Ast.ofJson v).map fun a => (opt, a)
  | _ => none

def ofJsonElements : List Json.Value → Option (List (Bool × Ast))
  | [] => some []
  | v :: vs =>
    (ofJsonElement v).bind fun x =>
    (ofJsonElements vs).map fun xs => x :: xs

def ofJsonRest : List Json.Value → Option (Option Ast)
  | [] => some none
  | [v] => (Ast.ofJson v).map some
  | _ => none

end

mutual

/-- The round trip: the decoder answers every projection. With
`Option.some.inj` this makes the projection injective — one code per
payload value. -/
theorem ofJson_toJson : ∀ (a : Ast), Ast.ofJson a.toJson = some a
  | .null | .bool | .int | .str => rfl
  | .lit v => by
    simp only [Ast.toJson, Ast.ofJson, LitVal.ofJson_toJson v, Option.map_some]
  | .arr a => by
    simp only [Ast.toJson, Ast.ofJson, ofJson_toJson a, Option.map_some]
  | .struct fs => by
    simp only [Ast.toJson, Ast.ofJson, ofJsonFields_fieldsToJson fs,
      Option.map_some]
  | .ref t => by
    simp only [Ast.toJson, Ast.ofJson]
    rw [dif_pos (UInt8.toNat_lt_size t)]
    simp
  | .decl g p ps => by
    simp only [Ast.toJson, Ast.ofJson, DeclarationId.General.ofWire_wire g,
      DeclPayload.ofJson_toJson p, ofJsonParams_paramsToJson ps,
      Option.bind_some, Option.map_some]
  | .union ms m => by
    cases m <;>
      simp only [Ast.toJson, Ast.ofJson, UnionMode.wire, UnionMode.ofWire,
        ofJsonMembers_membersToJson ms, Option.map_some]
  | .enum ms => by
    simp only [Ast.toJson, Ast.ofJson, enumMembersOfJson_toJson ms,
      Option.map_some]
  | .tuple e es r => by
    simp only [Ast.toJson, Ast.ofJson, ofJsonElement_elementToJson e,
      ofJsonElements_elementsToJson es, ofJsonRest_restToJson r,
      Option.bind_some, Option.map_some]
  | .reference _ => rfl
  | .susp a => by
    simp only [Ast.toJson, Ast.ofJson, ofJson_toJson a, Option.map_some]

theorem ofJsonElement_elementToJson :
    ∀ (e : Bool × Ast), ofJsonElement (elementToJson e) = some e
  | (o, a) => by
    simp only [elementToJson, ofJsonElement, ofJson_toJson a, Option.map_some]

theorem ofJsonElements_elementsToJson :
    ∀ (es : List (Bool × Ast)), ofJsonElements (elementsToJson es) = some es
  | [] => rfl
  | e :: es => by
    simp only [elementsToJson, ofJsonElements, ofJsonElement_elementToJson e,
      ofJsonElements_elementsToJson es, Option.bind_some, Option.map_some]

theorem ofJsonRest_restToJson :
    ∀ (r : Option Ast), ofJsonRest (restToJson r) = some r
  | none => rfl
  | some a => by
    simp only [restToJson, ofJsonRest, ofJson_toJson a, Option.map_some]

theorem ofJsonMembers_membersToJson :
    ∀ (ms : List Ast), ofJsonMembers (membersToJson ms) = some ms
  | [] => rfl
  | a :: as => by
    simp only [membersToJson, ofJsonMembers, ofJson_toJson a,
      ofJsonMembers_membersToJson as, Option.bind_some, Option.map_some]

theorem ofJsonFields_fieldsToJson :
    ∀ (fs : List (String × Bool × Ast)),
      ofJsonFields (fieldsToJson fs) = some fs
  | [] => rfl
  | (n, opt, a) :: fs => by
    simp only [fieldsToJson, ofJsonFields, ofJson_toJson a,
      ofJsonFields_fieldsToJson fs, Option.bind_some, Option.map_some]

theorem ofJsonParams_paramsToJson :
    ∀ (ps : List Ast), ofJsonParams (paramsToJson ps) = some ps
  | [] => rfl
  | a :: as => by
    simp only [paramsToJson, ofJsonParams, ofJson_toJson a,
      ofJsonParams_paramsToJson as, Option.bind_some, Option.map_some]

end

/-- One code per projection value. -/
theorem toJson_inj {a b : Ast} (h : a.toJson = b.toJson) : a = b := by
  have ha := ofJson_toJson a
  rw [h, ofJson_toJson b] at ha
  injection ha with ha
  exact ha.symm

end Cas.Schema

namespace Cas.Schema

/-! ## The revision-1 representation's laws — canonicality, decoder, round trip

The live revision's discipline, discharging the named open obligations
of this module. Three statements, in dependency order:

- `toRepresentationJson_canonical` / `representationDocument_canonical` /
  `envelope_canonical` — the representation is canonically spelled BY
  CONSTRUCTION, unconditionally: every emitted object's keys are already
  in strict codepoint order, and revision 1 carries a struct's property
  signatures as an ARRAY, so field-name order is not a canonicality
  premise (unlike revision 0, where the struct record's keys are the
  field names and `WF` is needed). `payload_renderPlain` is the byte
  consequence: the canonical payload hides no sort.
- `Ast.ofRepresentationJson` — the strict decoder: exactly the spellings
  `Ast.toRepresentationJson` emits, nothing else.
- `ofRepresentationJson_toRepresentationJson` — the round trip, stated
  MODULO the literal-null collapse.

### The literal-null collapse (register R13)

`Ast.toRepresentationJson` sends both `.null` and `.lit .null` to the
`Null` keyword — Effect's representation has no null literal. So the
revision-1 projection is NOT injective on `Ast`, and no decoder can
answer `some a` for every `a`. `Ast.repNorm` is that collapse as a
function on codes (the only two-to-one identification the projection
makes), `Ast.RepNormal` names its fixed points, and the laws are stated
against them: the round trip answers `a.repNorm`, injectivity holds up
to `repNorm`, and on `RepNormal` codes — every code the decoder can
ever produce — both hold on the nose. That last clause is a THEOREM,
not a remark: `ofRepresentationJson_repNormal` (and its document and
envelope corollaries) shows the decoder's image lies in `RepNormal`, so
`RepNormal` is exactly the subset the projection is a bijection onto.

### The general declaration code adds no second collapse

Increment C-decl grows `Ast.decl` (a registry id, a first-order
payload, the type parameters) and `declOfRepresentation` — the
registry-driven dispatch every persisted `Declaration` goes through.
It introduces NO new identification: `Ast.repNorm_decl` shows the
normal form rewrites only the type parameters, and
`decl_wire_ne_casRef` shows why nothing more is owed — the general code
cannot spell row zero (`foldlab/cas/ref`), which keeps the dedicated
code `.ref` the unique spelling of its own representation.

### The union code adds no third collapse either

Increment C1 grows `Ast.union` (an ordered member list and the mode).
Its key set is alphabetical like every other node's
(`_tag < checks < mode < types`), so the unconditional canonicality
theorem extends with no premise; `Ast.repNorm_union` shows the normal
form rewrites the members positionwise and touches neither the mode nor
the order, so the projection identifies no two unions that differ in
mode, member count, or member order. ORDER IS IDENTITY, ratified: there
is no sort anywhere on this path — not in the encoder, not in the
decoder, not in the normal form.

### The enum code adds no collapse at all

Increment C4 grows `Ast.enum` (an ordered `(name, value)` member list).
Its key set is alphabetical like every other node's
(`_tag < checks < enums`), so the unconditional canonicality theorem
extends with no premise; and it is a FIXED POINT of the normal form
(`Ast.repNorm_enum`) because it carries no sub-code for the literal-null
identification to reach. Order is identity here too — Effect's own
constructor reads `Object.keys` order, which is source order
(`Schema.ts:3021-3030`) — and the member pairs are ARRAY ITEMS rather
than object keys, so no canonical rendering has anything to say about
their arrangement.

### The tuple code adds no collapse either — by the carrier, not the
    normal form

Increment C2 grows `Ast.tuple` (a first element, the rest of them, an
optional rest type). Its key set is the array node's own
(`_tag < checks < elements < rest`), so canonicality extends with no
premise, and `Ast.repNorm_tuple` shows the normal form rewrites element
TYPES positionwise and the rest type and nothing else — the optionality
bits, the element count, and the positions all survive.

The collision this shape could have had is the interesting part, and it
is closed by the CARRIER rather than by the normal form:
`{elements:[], rest:[t]}` is `Ast.arr t`'s representation, and
`Ast.tuple` takes a FIRST element, so no tuple code can spell it. Had
the elements been a plain list, `tuple [] (some t)` and `arr t` would
have been two codes at one representation — a second two-to-one map, and
this section's claim that R13 is the only one would have been false.
Making the collision unspellable is the cheaper repair, and it is the
one taken. -/

open Cas.Json

/-! ### Canonicality -/

/-- The `isInt` check is canonically spelled: `_tag < aborted <
annotations < representation`, and `arbitrary < expected` inside. -/
private theorem intCheck_canonical : intCheck.Canonical := by
  unfold intCheck
  repeat' first | exact True.intro | decide | apply And.intro

/-- Every keyword representation is canonically spelled (`_tag < checks`). -/
private theorem keywordRepresentation_canonical (tag : String) :
    (keywordRepresentation tag).Canonical :=
  ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["_tag", "checks"]),
    trivial, trivial, trivial⟩

mutual

/-- The representation is canonically spelled by construction — no
well-formedness premise: revision 1 keys every object with a fixed,
alphabetically ordered key set, and carries a struct's fields as an
array rather than as a record, so no field name ever becomes a key. -/
theorem toRepresentationJson_canonical :
    ∀ (a : Ast), a.toRepresentationJson.Canonical
  | .null => keywordRepresentation_canonical _
  | .bool => keywordRepresentation_canonical _
  | .str => keywordRepresentation_canonical _
  | .lit .null => keywordRepresentation_canonical _
  | .int =>
    ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["_tag", "checks"]),
      trivial, ⟨intCheck_canonical, trivial⟩, trivial⟩
  | .lit (.bool _) | .lit (.int _) | .lit (.str _) =>
    ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "checks", "literal"]),
      trivial, trivial,
      ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["type", "value"]),
        trivial, trivial, trivial⟩,
      trivial⟩
  | .arr a =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·) ["_tag", "checks", "elements", "rest"]),
      trivial, trivial, trivial,
      ⟨toRepresentationJson_canonical a, trivial⟩, trivial⟩
  | .struct fs =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·)
            ["_tag", "checks", "indexSignatures", "propertySignatures"]),
      trivial, trivial, trivial, fieldsToRepresentationJson_canonical fs, trivial⟩
  | .ref _ =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·)
            ["_tag", "checks", "representation", "typeParameters"]),
      trivial, trivial,
      ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["id", "payload"]),
        trivial, trivial, trivial⟩,
      trivial, trivial⟩
  | .decl _ p ps =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·)
            ["_tag", "checks", "representation", "typeParameters"]),
      trivial, trivial,
      ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["id", "payload"]),
        trivial, DeclPayload.toJson_canonical p, trivial⟩,
      paramsToRepresentationJson_canonical ps, trivial⟩
  | .union ms _ =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·) ["_tag", "checks", "mode", "types"]),
      trivial, trivial, trivial,
      membersToRepresentationJson_canonical ms, trivial⟩
  | .enum ms =>
    ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "checks", "enums"]),
      trivial, trivial, enumMembersToJson_canonical ms, trivial⟩
  | .tuple e es r =>
    ⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·) ["_tag", "checks", "elements", "rest"]),
      trivial, trivial,
      ⟨elementToRepresentationJson_canonical e,
        elementsToRepresentationJson_canonical es⟩,
      restToRepresentationJson_canonical r, trivial⟩
  -- `$ref < _tag`, and this is the one admitted node whose `_tag` is not
  -- the first key. `decide` settles it on the characters: `$` is 0x24.
  | .reference _ =>
    ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["$ref", "_tag"]),
      trivial, trivial, trivial⟩
  | .susp a =>
    ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["_tag", "checks", "thunk"]),
      trivial, trivial, toRepresentationJson_canonical a, trivial⟩

/-- A union's member representations are canonically spelled. The
union's own key set (`_tag < checks < mode < types`) is alphabetical
like every other node's, so the unconditional canonicality theorem
extends over the new arm with no premise about the members' order —
which is the point: there is no order to be premised on. -/
theorem membersToRepresentationJson_canonical :
    ∀ (ms : List Ast), CanonicalItems (membersToRepresentationJson ms)
  | [] => trivial
  | a :: as =>
    ⟨toRepresentationJson_canonical a,
      membersToRepresentationJson_canonical as⟩

/-- Every emitted element is canonically spelled
(`isOptional < type`). Like every other revision-1 node, by
construction and with no premise — a tuple's positions are ARRAY
indices, so no element name ever becomes an object key. -/
theorem elementToRepresentationJson_canonical :
    ∀ (e : Bool × Ast), (elementToRepresentationJson e).Canonical
  | (_, a) =>
    ⟨List.pairwise_map.mp
        (by decide : List.Pairwise (· < ·) ["isOptional", "type"]),
      trivial, toRepresentationJson_canonical a, trivial⟩

theorem elementsToRepresentationJson_canonical :
    ∀ (es : List (Bool × Ast)),
      CanonicalItems (elementsToRepresentationJson es)
  | [] => trivial
  | e :: es =>
    ⟨elementToRepresentationJson_canonical e,
      elementsToRepresentationJson_canonical es⟩

theorem restToRepresentationJson_canonical :
    ∀ (r : Option Ast), CanonicalItems (restToRepresentationJson r)
  | none => trivial
  | some a => ⟨toRepresentationJson_canonical a, trivial⟩

/-- A declaration's type-parameter representations are canonically
spelled — like every other representation, by construction. -/
theorem paramsToRepresentationJson_canonical :
    ∀ (ps : List Ast), CanonicalItems (paramsToRepresentationJson ps)
  | [] => trivial
  | a :: as =>
    ⟨toRepresentationJson_canonical a, paramsToRepresentationJson_canonical as⟩

/-- Every emitted property signature is canonically spelled
(`isMutable < isOptional < name < type`, and `type < value` inside the
name). -/
theorem fieldsToRepresentationJson_canonical :
    ∀ (fs : List (String × Bool × Ast)),
      CanonicalItems (fieldsToRepresentationJson fs)
  | [] => trivial
  | (_, _, a) :: fs =>
    ⟨⟨List.pairwise_map.mp
        (by decide :
          List.Pairwise (· < ·) ["isMutable", "isOptional", "name", "type"]),
      trivial, trivial,
      ⟨List.pairwise_map.mp (by decide : List.Pairwise (· < ·) ["type", "value"]),
        trivial, trivial, trivial⟩,
      toRepresentationJson_canonical a, trivial⟩,
      fieldsToRepresentationJson_canonical fs⟩

end

/-- The single-root document is canonically spelled
(`references < representation`). -/
theorem representationDocument_canonical (a : Ast) :
    a.representationDocument.Canonical :=
  ⟨List.pairwise_map.mp
      (by decide : List.Pairwise (· < ·) ["references", "representation"]),
    ⟨List.Pairwise.nil, trivial⟩, toRepresentationJson_canonical a, trivial⟩

/-- The revision-1 envelope is canonically spelled (`revision < value`). -/
theorem envelope_canonical (a : Ast) : a.envelope.Canonical :=
  ⟨List.pairwise_map.mp
      (by decide : List.Pairwise (· < ·) ["revision", "value"]),
    trivial, representationDocument_canonical a, trivial⟩

/-- THE byte consequence: the canonical payload performs no reordering —
the payload bytes are the structural fold of the envelope as spelled. -/
theorem payload_renderPlain (a : Ast) :
    a.payload = Json.renderPlain a.envelope :=
  Json.renderCompact_eq_renderPlain _ (envelope_canonical a)

/-! ### The literal-null collapse, as a function -/

mutual

/-- The revision-1 normal form: `.lit .null` rewritten to `.null`, the
one identification `toRepresentationJson` makes (register R13). -/
def Ast.repNorm : Ast → Ast
  | .lit .null => .null
  | .arr a => .arr a.repNorm
  | .struct fs => .struct (repNormFields fs)
  | .decl id p ps => .decl id p (repNormParams ps)
  | .union ms m => .union (repNormMembers ms) m
  | .tuple e es r => .tuple (repNormElement e) (repNormElements es) (repNormRest r)
  -- C6 adds NO collapse of its own. A reference is a NAME and carries no
  -- sub-code at all, so it is its own normal form; a suspend rewrites its
  -- thunk and nothing else. The literal-null identification stays the
  -- only two-to-one map the revision-1 projection makes.
  | .susp a => .susp a.repNorm
  | a => a

def repNormFields :
    List (String × Bool × Ast) → List (String × Bool × Ast)
  | [] => []
  | (n, o, a) :: fs => (n, o, a.repNorm) :: repNormFields fs

/-- The general declaration code adds NO collapse of its own: this arm
rewrites the type parameters and nothing else, so the id and the
payload survive verbatim. That is by construction, not by luck —
`DeclarationId.General` excludes the registry rows that already have a
dedicated code, so no representation ever has two spellings
(`DeclarationId.General.row_not_dedicated`). The literal-null
identification stays the only two-to-one map the revision-1 projection
makes. -/
def repNormParams : List Ast → List Ast
  | [] => []
  | a :: as => a.repNorm :: repNormParams as

/-- The union code adds NO collapse of its own either: this rewrites
the members POSITION BY POSITION, so the list's length and order are
untouched and the mode is not read at all. `union [x, lit null]`
normalizes to `union [x, null]` — which is Effect's own `NullOr`, and
is the existing R13 identification firing inside a member, not a new
one. -/
def repNormMembers : List Ast → List Ast
  | [] => []
  | a :: as => a.repNorm :: repNormMembers as

/-- The tuple code adds NO collapse of its own either: this rewrites the
element's TYPE and leaves its optionality bit alone. -/
def repNormElement : Bool × Ast → Bool × Ast
  | (o, a) => (o, a.repNorm)

/-- Elements rewrite POSITION BY POSITION, so the tuple's length and the
order of its positions are untouched. -/
def repNormElements : List (Bool × Ast) → List (Bool × Ast)
  | [] => []
  | e :: es => repNormElement e :: repNormElements es

def repNormRest : Option Ast → Option Ast
  | none => none
  | some a => some a.repNorm

end

/-- A code the revision-1 projection identifies with nothing else:
its own normal form. -/
def Ast.RepNormal (a : Ast) : Prop := a.repNorm = a

mutual

/-- The normal form is a normal form. -/
theorem Ast.repNorm_idem : ∀ (a : Ast), a.repNorm.repNorm = a.repNorm
  | .null | .bool | .int | .str | .ref _ | .enum _ | .reference _ => rfl
  | .susp a => by
    simp only [Ast.repNorm, Ast.repNorm_idem a]
  | .lit .null => rfl
  | .lit (.bool _) | .lit (.int _) | .lit (.str _) => rfl
  | .arr a => by
    simp only [Ast.repNorm, Ast.repNorm_idem a]
  | .struct fs => by
    simp only [Ast.repNorm, repNormFields_idem fs]
  | .decl _ _ ps => by
    simp only [Ast.repNorm, repNormParams_idem ps]
  | .union ms _ => by
    simp only [Ast.repNorm, repNormMembers_idem ms]
  | .tuple e es r => by
    simp only [Ast.repNorm, repNormElement_idem e, repNormElements_idem es,
      repNormRest_idem r]

theorem repNormElement_idem :
    ∀ (e : Bool × Ast), repNormElement (repNormElement e) = repNormElement e
  | (o, a) => by
    simp only [repNormElement, Ast.repNorm_idem a]

theorem repNormElements_idem :
    ∀ (es : List (Bool × Ast)),
      repNormElements (repNormElements es) = repNormElements es
  | [] => rfl
  | e :: es => by
    simp only [repNormElements, repNormElement_idem e, repNormElements_idem es]

theorem repNormRest_idem :
    ∀ (r : Option Ast), repNormRest (repNormRest r) = repNormRest r
  | none => rfl
  | some a => by
    simp only [repNormRest, Ast.repNorm_idem a]

theorem repNormMembers_idem :
    ∀ (ms : List Ast), repNormMembers (repNormMembers ms) = repNormMembers ms
  | [] => rfl
  | a :: as => by
    simp only [repNormMembers, Ast.repNorm_idem a, repNormMembers_idem as]

theorem repNormFields_idem :
    ∀ (fs : List (String × Bool × Ast)),
      repNormFields (repNormFields fs) = repNormFields fs
  | [] => rfl
  | (n, o, a) :: fs => by
    simp only [repNormFields, Ast.repNorm_idem a, repNormFields_idem fs]

theorem repNormParams_idem :
    ∀ (ps : List Ast), repNormParams (repNormParams ps) = repNormParams ps
  | [] => rfl
  | a :: as => by
    simp only [repNormParams, Ast.repNorm_idem a, repNormParams_idem as]

end

/-- Every normal form is `RepNormal`. -/
theorem Ast.repNorm_repNormal (a : Ast) : a.repNorm.RepNormal :=
  Ast.repNorm_idem a

/-- THE no-new-collapse statement for increment C-decl: on a general
declaration the normal form rewrites the type parameters and NOTHING
else — the id and the payload survive verbatim. So the general code
identifies no two declarations that differ in id or payload, and the
literal-null identification (register R13) remains the only two-to-one
map the revision-1 projection makes. -/
theorem Ast.repNorm_decl (g : DeclarationId.General) (p : DeclPayload)
    (ps : List Ast) :
    (Ast.decl g p ps).repNorm = .decl g p (repNormParams ps) := rfl

/-- Why there is no new collapse to make: the general code never
spells row zero, so no general declaration projects onto the dedicated
code's representation. This is `DeclarationId.General.row_not_dedicated`
read at the wire. -/
theorem decl_wire_ne_casRef (g : DeclarationId.General) :
    g.wire ≠ DeclarationId.casRef.wire := by
  cases g <;> decide

/-- THE no-new-collapse statement for increment C1: on a union the
normal form rewrites the members POSITIONWISE and NOTHING else — the
mode survives verbatim, the length survives, and the order survives.
So the union code identifies no two unions that differ in mode, in
member count, or in member order: `union [a, b] ≠ union [b, a]` stays
two codes at two addresses, and the literal-null identification
(register R13) remains the only two-to-one map revision 1 makes. -/
theorem Ast.repNorm_union (ms : List Ast) (m : UnionMode) :
    (Ast.union ms m).repNorm = .union (repNormMembers ms) m := rfl

/-- THE no-new-collapse statement for increment C4: the enum code is a
FIXED POINT of the normal form — it carries no sub-code, so there is
nothing under it for the literal-null identification to reach, and the
normal form has no arm of its own to add. Two enums that differ in
member count, in member order, in a name, or in a value are two codes
at two addresses. -/
theorem Ast.repNorm_enum (ms : List (String × EnumValue)) :
    (Ast.enum ms).repNorm = .enum ms := rfl

/-- THE no-new-collapse statement for increment C2: on a tuple the
normal form rewrites the element TYPES positionwise and the rest type,
and NOTHING else — the optionality bits survive verbatim, the element
count survives, and the positions survive. So the tuple code identifies
no two tuples that differ in length, in a position's optionality, or in
where a type sits.

What keeps it from identifying a tuple with an ARRAY — the one collision
this shape could have had — is not the normal form but the carrier:
`Ast.tuple` takes a first element, so `{elements:[],rest:[t]}` has no
tuple spelling and stays `Ast.arr t`'s alone. -/
theorem Ast.repNorm_tuple (e : Bool × Ast) (es : List (Bool × Ast))
    (r : Option Ast) :
    (Ast.tuple e es r).repNorm =
      .tuple (repNormElement e) (repNormElements es) (repNormRest r) := rfl

/-- The optionality bit is not something the normal form can move. -/
theorem repNormElement_fst (e : Bool × Ast) : (repNormElement e).1 = e.1 := by
  obtain ⟨_, _⟩ := e; rfl

mutual

/-- Normalization is invisible to the projection: the collapse is
exactly what the encoder already performs. -/
theorem toRepresentationJson_repNorm :
    ∀ (a : Ast), a.repNorm.toRepresentationJson = a.toRepresentationJson
  | .null | .bool | .int | .str | .ref _ | .enum _ | .reference _ => rfl
  | .susp a => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      toRepresentationJson_repNorm a]
  | .lit .null => rfl
  | .lit (.bool _) | .lit (.int _) | .lit (.str _) => rfl
  | .arr a => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      toRepresentationJson_repNorm a]
  | .struct fs => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      fieldsToRepresentationJson_repNorm fs]
  | .decl _ _ ps => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      paramsToRepresentationJson_repNorm ps]
  | .union ms _ => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      membersToRepresentationJson_repNorm ms]
  | .tuple e es r => by
    simp only [Ast.repNorm, Ast.toRepresentationJson,
      elementToRepresentationJson_repNorm e,
      elementsToRepresentationJson_repNorm es,
      restToRepresentationJson_repNorm r]

theorem elementToRepresentationJson_repNorm :
    ∀ (e : Bool × Ast),
      elementToRepresentationJson (repNormElement e) =
        elementToRepresentationJson e
  | (o, a) => by
    simp only [repNormElement, elementToRepresentationJson,
      toRepresentationJson_repNorm a]

theorem elementsToRepresentationJson_repNorm :
    ∀ (es : List (Bool × Ast)),
      elementsToRepresentationJson (repNormElements es) =
        elementsToRepresentationJson es
  | [] => rfl
  | e :: es => by
    simp only [repNormElements, elementsToRepresentationJson,
      elementToRepresentationJson_repNorm e,
      elementsToRepresentationJson_repNorm es]

theorem restToRepresentationJson_repNorm :
    ∀ (r : Option Ast),
      restToRepresentationJson (repNormRest r) = restToRepresentationJson r
  | none => rfl
  | some a => by
    simp only [repNormRest, restToRepresentationJson,
      toRepresentationJson_repNorm a]

theorem membersToRepresentationJson_repNorm :
    ∀ (ms : List Ast),
      membersToRepresentationJson (repNormMembers ms) =
        membersToRepresentationJson ms
  | [] => rfl
  | a :: as => by
    simp only [repNormMembers, membersToRepresentationJson,
      toRepresentationJson_repNorm a, membersToRepresentationJson_repNorm as]

theorem fieldsToRepresentationJson_repNorm :
    ∀ (fs : List (String × Bool × Ast)),
      fieldsToRepresentationJson (repNormFields fs) =
        fieldsToRepresentationJson fs
  | [] => rfl
  | (n, o, a) :: fs => by
    simp only [repNormFields, fieldsToRepresentationJson,
      toRepresentationJson_repNorm a, fieldsToRepresentationJson_repNorm fs]

theorem paramsToRepresentationJson_repNorm :
    ∀ (ps : List Ast),
      paramsToRepresentationJson (repNormParams ps) =
        paramsToRepresentationJson ps
  | [] => rfl
  | a :: as => by
    simp only [repNormParams, paramsToRepresentationJson,
      toRepresentationJson_repNorm a, paramsToRepresentationJson_repNorm as]

end

/-- Normalization preserves a declaration's arity — it rewrites the
type parameters in place. -/
theorem repNormParams_length :
    ∀ (ps : List Ast), (repNormParams ps).length = ps.length
  | [] => rfl
  | a :: as => by
    simp only [repNormParams, List.length_cons, repNormParams_length as]

/-- Normalization preserves a union's member count — it rewrites the
members in place, so the arity of the union is not something the
normal form can change. -/
theorem repNormMembers_length :
    ∀ (ms : List Ast), (repNormMembers ms).length = ms.length
  | [] => rfl
  | a :: as => by
    simp only [repNormMembers, List.length_cons, repNormMembers_length as]

/-- In particular a nonempty union stays nonempty: the `WF` clause the
empty union is refused by survives normalization. -/
theorem repNormMembers_ne_nil :
    ∀ {ms : List Ast}, ms ≠ [] → repNormMembers ms ≠ []
  | [], h => absurd rfl h
  | _ :: _, _ => by simp [repNormMembers]

mutual

/-- Well-formedness survives normalization: the collapse rewrites leaves
only, so no struct's field names move. -/
theorem Ast.repNorm_wf : ∀ (a : Ast), a.WF → a.repNorm.WF
  | .null, h | .bool, h | .int, h | .str, h | .ref _, h | .enum _, h
  | .reference _, h => h
  | .susp a, h => Ast.repNorm_wf a h
  | .lit .null, _ => trivial
  | .lit (.bool _), h | .lit (.int _), h | .lit (.str _), h => h
  | .arr a, h => Ast.repNorm_wf a h
  | .struct fs, ⟨hsorted, hwf⟩ => by
    refine ⟨?_, repNormFields_wf fs hwf⟩
    have hkeys : (repNormFields fs).map (fun f => f.1) = fs.map (fun f => f.1) :=
      repNormFields_keys fs
    exact List.pairwise_map.mp (hkeys ▸ List.pairwise_map.mpr hsorted)
  | .decl _ _ ps, ⟨hp, harity, hps⟩ =>
    ⟨hp, (repNormParams_length ps).trans harity, repNormParams_wf ps hps⟩
  | .union ms _, ⟨hne, hms⟩ =>
    ⟨repNormMembers_ne_nil hne, repNormMembers_wf ms hms⟩
  | .tuple e es r, ⟨he, hes, hr⟩ =>
    ⟨repNormElement_wf e he, repNormElements_wf es hes, repNormRest_wf r hr⟩

theorem repNormElement_wf :
    ∀ (e : Bool × Ast), WFElement e → WFElement (repNormElement e)
  | (_, a), ha => Ast.repNorm_wf a ha

theorem repNormElements_wf :
    ∀ (es : List (Bool × Ast)), WFElements es → WFElements (repNormElements es)
  | [], _ => trivial
  | e :: es, ⟨he, hes⟩ => ⟨repNormElement_wf e he, repNormElements_wf es hes⟩

theorem repNormRest_wf :
    ∀ (r : Option Ast), WFRest r → WFRest (repNormRest r)
  | none, _ => trivial
  | some a, ha => Ast.repNorm_wf a ha

theorem repNormMembers_wf :
    ∀ (ms : List Ast), WFMembers ms → WFMembers (repNormMembers ms)
  | [], _ => trivial
  | a :: as, ⟨ha, has⟩ => ⟨Ast.repNorm_wf a ha, repNormMembers_wf as has⟩

theorem repNormFields_wf :
    ∀ (fs : List (String × Bool × Ast)), WFFields fs → WFFields (repNormFields fs)
  | [], _ => trivial
  | (_, _, a) :: fs, ⟨ha, hfs⟩ => ⟨Ast.repNorm_wf a ha, repNormFields_wf fs hfs⟩

theorem repNormParams_wf :
    ∀ (ps : List Ast), WFParams ps → WFParams (repNormParams ps)
  | [], _ => trivial
  | a :: as, ⟨ha, has⟩ => ⟨Ast.repNorm_wf a ha, repNormParams_wf as has⟩

theorem repNormFields_keys :
    ∀ (fs : List (String × Bool × Ast)),
      (repNormFields fs).map (fun f => f.1) = fs.map (fun f => f.1)
  | [] => rfl
  | (n, o, a) :: fs => by
    simp only [repNormFields, List.map_cons, repNormFields_keys fs]

end

/-! ### The strict decoder -/

/-- The one admitted check spelling: Effect's `effect/schema/isInt`,
exactly as `intCheck` emits it. -/
private def isIntCheck : Json.Value → Bool
  | .obj [
      ("_tag", .str "Filter"),
      ("aborted", .bool false),
      ("annotations", .obj [
        ("arbitrary", .obj [
          ("constraint", .obj [("integer", .bool true)])]),
        ("expected", .str "an integer")]),
      ("representation", .obj [
        ("id", .str "effect/schema/isInt"),
        ("payload", .null)])] => true
  | _ => false

/-- The typed-literal payload: Effect's `{type, value}` pair. There is
no null spelling — a null literal is the `Null` keyword (register R13). -/
private def litOfRepresentationJson : Json.Value → Option LitVal
  | .obj [("type", .str "boolean"), ("value", .bool b)] => some (.bool b)
  | .obj [("type", .str "number"), ("value", .int i)] =>
    if h : i.natAbs ≤ maxSafeNat then some (.int ⟨i, h⟩) else none
  | .obj [("type", .str "string"), ("value", .str s)] => some (.str s)
  | _ => none

/-- The general declaration code, from its decoded parts. -/
private def generalDeclOf (g : DeclarationId.General) (p : Json.Value)
    (ps : List Ast) : Option Ast :=
  (DeclPayload.ofJson p).map fun pay => .decl g pay ps

/-- THE declaration gate: a persisted `{id, payload}` and its decoded
type parameters, dispatched through the registry.

Row zero answers the DEDICATED code (`.ref`); every general row answers
the general code (`.decl`); an id that is no row at all is refused —
which is exactly the allowlist P4 requires, and the refusal the door
names `IngestRefusal.unknownDeclaration`. The match is exhaustive over
`DeclarationId`, so a new registry row cannot be added without
dispositioning it here. -/
def declOfRepresentation (w : String) (p : Json.Value) (ps : List Ast) :
    Option Ast :=
  match DeclarationId.ofWire w with
  | none => none
  | some .casRef =>
    match p, ps with
    | .nat tag, [] => if _h : tag < 256 then some (.ref (UInt8.ofNat tag)) else none
    | _, _ => none
  | some .effectDate => generalDeclOf .date p ps
  | some .effectUrl => generalDeclOf .url p ps
  | some .effectOption => generalDeclOf .option p ps

mutual

/-- The strict decoder of the revision-1 representation: exactly the
spellings `Ast.toRepresentationJson` emits, key order and all, nothing
else. Every foreign spelling dies here; normalization is the caller's
job (`Cas.Schema.ingest`). -/
def Ast.ofRepresentationJson : Json.Value → Option Ast
  | .obj [("_tag", .str "Null"), ("checks", .arr [])] => some .null
  | .obj [("_tag", .str "Boolean"), ("checks", .arr [])] => some .bool
  | .obj [("_tag", .str "String"), ("checks", .arr [])] => some .str
  | .obj [("_tag", .str "Number"), ("checks", .arr [c])] =>
    if isIntCheck c then some .int else none
  | .obj [("_tag", .str "Literal"), ("checks", .arr []), ("literal", l)] =>
    (litOfRepresentationJson l).map .lit
  | .obj [("_tag", .str "Arrays"), ("checks", .arr []), ("elements", .arr []),
      ("rest", .arr [item])] =>
    (Ast.ofRepresentationJson item).map .arr
  | .obj [("_tag", .str "Objects"), ("checks", .arr []),
      ("indexSignatures", .arr []), ("propertySignatures", .arr ps)] =>
    (ofRepresentationProperties ps).map .struct
  | .obj [("_tag", .str "Declaration"), ("checks", .arr []),
      ("representation", .obj [("id", .str w), ("payload", p)]),
      ("typeParameters", .arr tps)] =>
    (ofRepresentationParams tps).bind fun ps => declOfRepresentation w p ps
  | .obj [("_tag", .str "Union"), ("checks", .arr []), ("mode", .str w),
      ("types", .arr ts)] =>
    match UnionMode.ofWire w with
    | none => none
    | some m => (ofRepresentationMembers ts).map fun ms => .union ms m
  | .obj [("_tag", .str "Enum"), ("checks", .arr []), ("enums", .arr ms)] =>
    (enumMembersOfJson ms).map .enum
  -- The tuple arm is reached only when `elements` is NONEMPTY: the plain
  -- array arm above claims `{elements:[], rest:[t]}`, and the two are
  -- disjoint by that pattern. `{elements:[], rest:[]}` — the empty tuple
  -- — matches neither and is refused, as it was before this increment.
  | .obj [("_tag", .str "Arrays"), ("checks", .arr []),
      ("elements", .arr (e :: es)), ("rest", .arr rs)] =>
    (ofRepresentationElement e).bind fun x =>
    (ofRepresentationElements es).bind fun xs =>
    (ofRepresentationRest rs).map fun r => .tuple x xs r
  -- The two C6 arms. `Reference` carries NO `checks` key — it is the one
  -- admitted node that does not, which is Effect's own shape and not an
  -- omission here.
  | .obj [("$ref", .str n), ("_tag", .str "Reference")] => some (.reference n)
  | .obj [("_tag", .str "Suspend"), ("checks", .arr []), ("thunk", t)] =>
    (Ast.ofRepresentationJson t).map .susp
  | _ => none

/-- The property-signature list decoder, preserving order verbatim. -/
private def ofRepresentationProperties :
    List Json.Value → Option (List (String × Bool × Ast))
  | [] => some []
  | .obj [("isMutable", .bool false), ("isOptional", .bool opt),
      ("name", .obj [("type", .str "string"), ("value", .str n)]),
      ("type", t)] :: rest =>
    (Ast.ofRepresentationJson t).bind fun a =>
    (ofRepresentationProperties rest).map fun fs => (n, opt, a) :: fs
  | _ => none

/-- The type-parameter list decoder, preserving order verbatim. -/
def ofRepresentationParams : List Json.Value → Option (List Ast)
  | [] => some []
  | v :: vs =>
    (Ast.ofRepresentationJson v).bind fun a =>
    (ofRepresentationParams vs).map fun as => a :: as

/-- The union-member list decoder, preserving order verbatim. There is
no sort on the way in either: the decoder answers the members in the
order the bytes carry them, which is the only reading that agrees with
order-is-identity. An EMPTY `types` array decodes — to `union [] m`,
which the door then refuses at the gate (`Ast.wf`), exactly the way an
unsorted struct decodes and is then refused. Shape is the decoder's
question; discipline is the gate's. -/
def ofRepresentationMembers : List Json.Value → Option (List Ast)
  | [] => some []
  | v :: vs =>
    (Ast.ofRepresentationJson v).bind fun a =>
    (ofRepresentationMembers vs).map fun as => a :: as

/-- One element: exactly the spelling `elementsToRepresentationJson`
emits. An element carrying an annotation bag has no spelling here and
dies — annotations are `GROW(C-ann)`, on elements as everywhere else. -/
def ofRepresentationElement : Json.Value → Option (Bool × Ast)
  | .obj [("isOptional", .bool opt), ("type", t)] =>
    (Ast.ofRepresentationJson t).map fun a => (opt, a)
  | _ => none

/-- The element list decoder, preserving position verbatim. -/
def ofRepresentationElements : List Json.Value → Option (List (Bool × Ast))
  | [] => some []
  | v :: vs =>
    (ofRepresentationElement v).bind fun x =>
    (ofRepresentationElements vs).map fun xs => x :: xs

/-- The rest decoder: none, or exactly one. A `rest` of length two or
more is refused HERE, in the decoder, rather than at the gate — the
carrier has no term for it, so it is not a shape the plane can spell,
which is the same reading `Never` gets. -/
def ofRepresentationRest : List Json.Value → Option (Option Ast)
  | [] => some none
  | [v] => (Ast.ofRepresentationJson v).map some
  | _ => none

end

/-- The document decoder, BARE-CODE arm: a single-root document with an
EMPTY references table. A non-empty table is refused because this arm
answers ONE CODE, and a code is not where a table lives — admitting one
would answer a code the projection cannot re-emit.

NARROWED by increment C6, alongside the identical sentence on
`IngestRefusal.nonEmptyReferences`; the twin was left behind and the
break pass caught it (2026-08-30, note N2). It used to read "revision
1's `references` is unreachable from the Lean side today (no `Suspend`,
no `Reference` constructor)", which stopped being true in the commit
that added both constructors. `Document.ofRepresentationDocument`
(`Cas/Schema/Guarded.lean`) is the arm that reads a table. -/
def Ast.ofRepresentationDocument : Json.Value → Option Ast
  | .obj [("references", .obj []), ("representation", r)] =>
    Ast.ofRepresentationJson r
  | _ => none

/-- The envelope decoder: revision 1 only. Revision 0 has its own door
(`ingestLegacy`); every other revision is refused. -/
def Ast.ofEnvelope : Json.Value → Option Ast
  | .obj [("revision", .nat r), ("value", d)] =>
    if r = schemaRevision then Ast.ofRepresentationDocument d else none
  | _ => none

/-! ### The round trip -/

mutual

/-- The round trip, modulo the literal-null collapse: the decoder
answers every projection with the projected code's normal form. On
`RepNormal` codes — which is every code the decoder itself produces —
it answers the code on the nose (`ofRepresentationJson_toRepresentationJson'`). -/
theorem ofRepresentationJson_toRepresentationJson :
    ∀ (a : Ast),
      Ast.ofRepresentationJson a.toRepresentationJson = some a.repNorm
  | .null | .bool | .int | .str | .reference _ => rfl
  | .susp a => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      ofRepresentationJson_toRepresentationJson a, Option.map_some, Ast.repNorm]
  | .lit .null => rfl
  | .lit (.bool _) | .lit (.str _) => rfl
  | .lit (.int i) => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      litOfRepresentationJson, dif_pos i.property, Option.map_some,
      Ast.repNorm]
  | .arr a => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      ofRepresentationJson_toRepresentationJson a, Option.map_some, Ast.repNorm]
  | .struct fs => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      ofRepresentationProperties_fieldsToRepresentationJson fs,
      Option.map_some, Ast.repNorm]
  | .ref t => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      ofRepresentationParams, Option.bind_some, declOfRepresentation,
      DeclarationId.ofWire]
    rw [dif_pos (UInt8.toNat_lt_size t)]
    simp [Ast.repNorm]
  | .decl g p ps => by
    cases g <;>
      simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
        DeclarationId.General.wire, DeclarationId.General.row,
        DeclarationId.wire,
        ofRepresentationParams_paramsToRepresentationJson ps,
        Option.bind_some, declOfRepresentation, DeclarationId.ofWire,
        generalDeclOf, DeclPayload.ofJson_toJson p, Option.map_some,
        Ast.repNorm]
  | .union ms m => by
    cases m <;>
      simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
        UnionMode.wire, UnionMode.ofWire,
        ofRepresentationMembers_membersToRepresentationJson ms,
        Option.map_some, Ast.repNorm]
  | .enum ms => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      enumMembersOfJson_toJson ms, Option.map_some, Ast.repNorm]
  | .tuple e es r => by
    simp only [Ast.toRepresentationJson, Ast.ofRepresentationJson,
      ofRepresentationElement_elementToRepresentationJson e,
      ofRepresentationElements_elementsToRepresentationJson es,
      ofRepresentationRest_restToRepresentationJson r,
      Option.bind_some, Option.map_some, Ast.repNorm]

theorem ofRepresentationElement_elementToRepresentationJson :
    ∀ (e : Bool × Ast),
      ofRepresentationElement (elementToRepresentationJson e) =
        some (repNormElement e)
  | (o, a) => by
    simp only [elementToRepresentationJson, ofRepresentationElement,
      ofRepresentationJson_toRepresentationJson a, Option.map_some,
      repNormElement]

theorem ofRepresentationElements_elementsToRepresentationJson :
    ∀ (es : List (Bool × Ast)),
      ofRepresentationElements (elementsToRepresentationJson es) =
        some (repNormElements es)
  | [] => rfl
  | e :: es => by
    simp only [elementsToRepresentationJson, ofRepresentationElements,
      ofRepresentationElement_elementToRepresentationJson e,
      ofRepresentationElements_elementsToRepresentationJson es,
      Option.bind_some, Option.map_some, repNormElements]

theorem ofRepresentationRest_restToRepresentationJson :
    ∀ (r : Option Ast),
      ofRepresentationRest (restToRepresentationJson r) = some (repNormRest r)
  | none => rfl
  | some a => by
    simp only [restToRepresentationJson, ofRepresentationRest,
      ofRepresentationJson_toRepresentationJson a, Option.map_some, repNormRest]

theorem ofRepresentationMembers_membersToRepresentationJson :
    ∀ (ms : List Ast),
      ofRepresentationMembers (membersToRepresentationJson ms) =
        some (repNormMembers ms)
  | [] => rfl
  | a :: as => by
    simp only [membersToRepresentationJson, ofRepresentationMembers,
      ofRepresentationJson_toRepresentationJson a,
      ofRepresentationMembers_membersToRepresentationJson as,
      Option.bind_some, Option.map_some, repNormMembers]

theorem ofRepresentationParams_paramsToRepresentationJson :
    ∀ (ps : List Ast),
      ofRepresentationParams (paramsToRepresentationJson ps) =
        some (repNormParams ps)
  | [] => rfl
  | a :: as => by
    simp only [paramsToRepresentationJson, ofRepresentationParams,
      ofRepresentationJson_toRepresentationJson a,
      ofRepresentationParams_paramsToRepresentationJson as,
      Option.bind_some, Option.map_some, repNormParams]

theorem ofRepresentationProperties_fieldsToRepresentationJson :
    ∀ (fs : List (String × Bool × Ast)),
      ofRepresentationProperties (fieldsToRepresentationJson fs) =
        some (repNormFields fs)
  | [] => rfl
  | (n, opt, a) :: fs => by
    simp only [fieldsToRepresentationJson, ofRepresentationProperties,
      ofRepresentationJson_toRepresentationJson a,
      ofRepresentationProperties_fieldsToRepresentationJson fs,
      Option.bind_some, Option.map_some, repNormFields]

end

/-- The round trip on normal codes: exactly the code back. -/
theorem ofRepresentationJson_toRepresentationJson' {a : Ast}
    (ha : a.RepNormal) : Ast.ofRepresentationJson a.toRepresentationJson = some a := by
  rw [ofRepresentationJson_toRepresentationJson a, ha]

/-- The document round trip. -/
theorem ofRepresentationDocument_representationDocument (a : Ast) :
    Ast.ofRepresentationDocument a.representationDocument = some a.repNorm :=
  ofRepresentationJson_toRepresentationJson a

/-- The envelope round trip. -/
theorem ofEnvelope_envelope (a : Ast) :
    Ast.ofEnvelope a.envelope = some a.repNorm := by
  show (if schemaRevision = schemaRevision then
      Ast.ofRepresentationDocument a.representationDocument else none) = _
  rw [if_pos rfl]
  exact ofRepresentationDocument_representationDocument a

/-- The envelope round trip on normal codes. -/
theorem ofEnvelope_envelope' {a : Ast} (ha : a.RepNormal) :
    Ast.ofEnvelope a.envelope = some a := by
  rw [ofEnvelope_envelope a, ha]

/-! ### Injectivity -/

/-- One normal code per representation value: the projection is
injective up to the literal-null collapse, and that collapse is the
only identification it makes. -/
theorem toRepresentationJson_inj {a b : Ast}
    (h : a.toRepresentationJson = b.toRepresentationJson) :
    a.repNorm = b.repNorm := by
  have ha := ofRepresentationJson_toRepresentationJson a
  rw [h, ofRepresentationJson_toRepresentationJson b] at ha
  injection ha with ha
  exact ha.symm

/-- On normal codes the projection is injective outright. -/
theorem toRepresentationJson_inj' {a b : Ast}
    (ha : a.RepNormal) (hb : b.RepNormal)
    (h : a.toRepresentationJson = b.toRepresentationJson) : a = b := by
  have := toRepresentationJson_inj h
  rwa [ha, hb] at this

/-- One normal code per envelope value. -/
theorem envelope_inj {a b : Ast} (h : a.envelope = b.envelope) :
    a.repNorm = b.repNorm := by
  have ha := ofEnvelope_envelope a
  rw [h, ofEnvelope_envelope b] at ha
  injection ha with ha
  exact ha.symm

/-! ### Decoder soundness for `RepNormal`

The decoder's image is contained in `RepNormal`, and with
`ofRepresentationJson_toRepresentationJson'` that makes `RepNormal`
exactly the subset the revision-1 projection is a bijection onto.

The obligation stood parked because the proof was looked for in the
wrong place. Lean 4.33 emits no functional-induction principle for a
mutually recursive definition, so an induction FOLLOWING THE DECODER
has no principle to run on, and `split` on the decoder's own equation
severs the input from its sub-values — the termination argument is
gone before the first recursive call.

The decomposition that works inducts on the OUTPUT instead. `repNorm`
recurses structurally on `Ast`, and the estate already runs a mutual
block over exactly that recursion (`Ast.repNorm_idem`,
`ofRepresentationJson_toRepresentationJson`); this proof is a third
one, mirroring the same six families. The decoder then appears only
through INVERSION lemmas — one per output constructor that carries a
sub-code — each a single `split` with no recursion under it, so
`split`'s loss of the input is free. `inv_lit` is where the question is
actually decided: `litOfRepresentationJson` has no null spelling, so
the decoder can never answer `.lit .null`, and every other arm merely
carries `RepNormal` up from its parts. -/

/-! #### Inversion — which arm answered, read off the output

One `split` over the decoder's twelve arms, once, discharging every
question the induction below asks of it. Six implications rather than a
twelve-way disjunction, so the use sites are applications rather than
case analyses; the five that do not match an arm's output constructor
are vacuous and close by clash. There is no recursion under this
`split`, which is exactly why `split`'s loss of the input costs
nothing here. -/

/-- The declaration gate answers a dedicated `.ref` or a general
`.decl` over the parameters it was handed, and nothing else. Stated
because it is the one decoder arm whose body is a registry dispatch
rather than a constructor application, so the clash the other arms give
`simp` for free has to be proved here. -/
private theorem declOfRepresentation_image {w : String} {p : Json.Value}
    {ps : List Ast} {a : Ast} (h : declOfRepresentation w p ps = some a) :
    (∃ t, a = .ref t) ∨ (∃ g pay, a = .decl g pay ps) := by
  rw [declOfRepresentation.eq_def] at h
  split at h
  · simp at h
  · split at h <;> simp_all
    exact Or.inl ⟨_, h.2.symm⟩
  all_goals
    simp only [generalDeclOf, Option.map_eq_some_iff] at h
    obtain ⟨pay, _, hpay⟩ := h
    exact Or.inr ⟨_, pay, hpay.symm⟩

/-- The literal decoder has no null spelling: it answers `.bool`,
`.int`, or `.str` and nothing else. THE fact the whole obligation rests
on — every other decoder arm merely carries `RepNormal` up from its
parts. -/
private theorem litOfRepresentationJson_ne_null {j : Json.Value} {l : LitVal}
    (h : litOfRepresentationJson j = some l) : l ≠ .null := by
  intro hnull
  subst hnull
  rw [litOfRepresentationJson.eq_def] at h
  split at h <;> simp_all

/-- The decoder's arms, read off its OUTPUT: seven implications, one per
constructor that the induction below has to look inside. Proved by a
single `split` over the fourteen arms — the implications that do not
match an arm's output constructor are vacuous and close by clash.
`.reference` needs no clause: it carries no sub-code for the induction
to descend into. -/
private theorem ofRepresentationJson_inv {v : Json.Value} {a : Ast}
    (h : Ast.ofRepresentationJson v = some a) :
    (∀ l, a = .lit l → l ≠ .null)
    ∧ (∀ b, a = .arr b → ∃ item, Ast.ofRepresentationJson item = some b)
    ∧ (∀ fs, a = .struct fs → ∃ ps, ofRepresentationProperties ps = some fs)
    ∧ (∀ g p params, a = .decl g p params →
        ∃ tps, ofRepresentationParams tps = some params)
    ∧ (∀ ms m, a = .union ms m → ∃ ts, ofRepresentationMembers ts = some ms)
    ∧ (∀ e es r, a = .tuple e es r →
        (∃ x, ofRepresentationElement x = some e)
          ∧ (∃ xs, ofRepresentationElements xs = some es)
          ∧ (∃ rs, ofRepresentationRest rs = some r))
    ∧ (∀ b, a = .susp b → ∃ t, Ast.ofRepresentationJson t = some b) := by
  rw [Ast.ofRepresentationJson.eq_def] at h
  split at h
  -- Null, Boolean, String
  case h_1 | h_2 | h_3 => simp only [Option.some.injEq] at h; subst h; simp
  -- Number
  case h_4 =>
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · simp at h
  -- Literal
  case h_5 =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨lv, hlv, rfl⟩ := h
    refine ⟨?_, by simp, by simp, by simp, by simp, by simp, by simp⟩
    intro l hl
    injection hl with hl
    exact hl ▸ litOfRepresentationJson_ne_null hlv
  -- Arrays, plain
  case h_6 item =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨by simp, fun b hb => ⟨item, by rw [hx]; injection hb with hb; rw [hb]⟩,
      by simp, by simp, by simp, by simp, by simp⟩
  -- Objects
  case h_7 ps =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨by simp, by simp,
      fun fs hfs => ⟨ps, by rw [hx]; injection hfs with hfs; rw [hfs]⟩,
      by simp, by simp, by simp, by simp⟩
  -- Declaration
  case h_8 tps =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨params, hparams, hd⟩ := h
    rcases declOfRepresentation_image hd with ⟨t, rfl⟩ | ⟨g, pay, rfl⟩
    · exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · refine ⟨by simp, by simp, by simp, ?_, by simp, by simp, by simp⟩
      intro g' p' params' hp'
      injection hp' with _ _ hp'
      exact ⟨tps, by rw [hparams, hp']⟩
  -- Union
  case h_9 ts =>
    split at h
    · simp at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      refine ⟨by simp, by simp, by simp, by simp, ?_, by simp, by simp⟩
      intro ms m hm
      injection hm with hm _
      exact ⟨ts, by rw [hx, hm]⟩
  -- Enum
  case h_10 =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, _, rfl⟩ := h
    exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  -- Arrays, tuple
  case h_11 e es rs =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, xs, hxs, r, hr, rfl⟩ := h
    refine ⟨by simp, by simp, by simp, by simp, by simp, ?_, by simp⟩
    intro e' es' r' he'
    injection he' with h1 h2 h3
    exact ⟨⟨e, by rw [hx, h1]⟩, ⟨es, by rw [hxs, h2]⟩, ⟨rs, by rw [hr, h3]⟩⟩
  -- Reference: a NAME, no sub-code, so every clause is vacuous
  case h_12 =>
    simp only [Option.some.injEq] at h; subst h; simp
  -- Suspend
  case h_13 t =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro b hb
    injection hb with hb
    exact ⟨t, by rw [hx, hb]⟩
  -- The catch-all: nothing decoded
  case h_14 => simp at h

/-! #### Inversion for the list families

The helper decoders are plain list recursions, so their inversions are
two-arm splits with nothing under them. -/

private theorem ofRepresentationProperties_inv {ps : List Json.Value}
    {f : String × Bool × Ast} {fs : List (String × Bool × Ast)}
    (h : ofRepresentationProperties ps = some (f :: fs)) :
    (∃ t, Ast.ofRepresentationJson t = some f.2.2)
      ∧ (∃ ps', ofRepresentationProperties ps' = some fs) := by
  rw [ofRepresentationProperties.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, gs, hgs, heq⟩ := h
    injection heq with h1 h2
    subst h1
    subst h2
    exact ⟨⟨_, hx⟩, ⟨_, hgs⟩⟩
  · simp at h

private theorem ofRepresentationParams_inv {vs : List Json.Value}
    {a : Ast} {as : List Ast}
    (h : ofRepresentationParams vs = some (a :: as)) :
    (∃ t, Ast.ofRepresentationJson t = some a)
      ∧ (∃ vs', ofRepresentationParams vs' = some as) := by
  rw [ofRepresentationParams.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, ys, hys, heq⟩ := h
    injection heq with h1 h2
    subst h1
    subst h2
    exact ⟨⟨_, hx⟩, ⟨_, hys⟩⟩

private theorem ofRepresentationMembers_inv {vs : List Json.Value}
    {a : Ast} {as : List Ast}
    (h : ofRepresentationMembers vs = some (a :: as)) :
    (∃ t, Ast.ofRepresentationJson t = some a)
      ∧ (∃ vs', ofRepresentationMembers vs' = some as) := by
  rw [ofRepresentationMembers.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, ys, hys, heq⟩ := h
    injection heq with h1 h2
    subst h1
    subst h2
    exact ⟨⟨_, hx⟩, ⟨_, hys⟩⟩

private theorem ofRepresentationElement_inv {v : Json.Value} {e : Bool × Ast}
    (h : ofRepresentationElement v = some e) :
    ∃ t, Ast.ofRepresentationJson t = some e.2 := by
  rw [ofRepresentationElement.eq_def] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, heq⟩ := h
    subst heq
    exact ⟨_, hx⟩
  · simp at h

private theorem ofRepresentationElements_inv {vs : List Json.Value}
    {e : Bool × Ast} {es : List (Bool × Ast)}
    (h : ofRepresentationElements vs = some (e :: es)) :
    (∃ t, ofRepresentationElement t = some e)
      ∧ (∃ vs', ofRepresentationElements vs' = some es) := by
  rw [ofRepresentationElements.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, ys, hys, heq⟩ := h
    injection heq with h1 h2
    subst h1
    subst h2
    exact ⟨⟨_, hx⟩, ⟨_, hys⟩⟩

private theorem ofRepresentationRest_inv {vs : List Json.Value} {a : Ast}
    (h : ofRepresentationRest vs = some (some a)) :
    ∃ t, Ast.ofRepresentationJson t = some a := by
  rw [ofRepresentationRest.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, heq⟩ := h
    injection heq with heq
    subst heq
    exact ⟨_, hx⟩
  · simp at h

/-! #### The induction, on the OUTPUT

Six families, the same six `repNorm` recurses on and the same six the
round-trip block above already runs over. Every recursive call is on a
structural subterm of an `Ast`, so there is no termination question at
all — which is the whole content of the restructuring. -/

mutual

/-- The decoder answers only codes that are their own normal form. -/
theorem ofRepresentationJson_repNorm :
    ∀ (a : Ast) (v : Json.Value),
      Ast.ofRepresentationJson v = some a → a.repNorm = a
  | .null, _, _ => rfl
  | .bool, _, _ => rfl
  | .int, _, _ => rfl
  | .str, _, _ => rfl
  | .ref _, _, _ => rfl
  | .enum _, _, _ => rfl
  | .reference _, _, _ => rfl
  | .susp b, _, h => by
    obtain ⟨t, ht⟩ := (ofRepresentationJson_inv h).2.2.2.2.2.2 b rfl
    simp only [Ast.repNorm, ofRepresentationJson_repNorm b t ht]
  | .lit .null, _, h => absurd rfl ((ofRepresentationJson_inv h).1 .null rfl)
  | .lit (.bool _), _, _ => rfl
  | .lit (.int _), _, _ => rfl
  | .lit (.str _), _, _ => rfl
  | .arr b, _, h => by
    obtain ⟨item, hitem⟩ := (ofRepresentationJson_inv h).2.1 b rfl
    simp only [Ast.repNorm, ofRepresentationJson_repNorm b item hitem]
  | .struct fs, _, h => by
    obtain ⟨ps, hps⟩ := (ofRepresentationJson_inv h).2.2.1 fs rfl
    simp only [Ast.repNorm, ofRepresentationProperties_repNorm fs ps hps]
  | .decl g p params, _, h => by
    obtain ⟨tps, htps⟩ := (ofRepresentationJson_inv h).2.2.2.1 g p params rfl
    simp only [Ast.repNorm, ofRepresentationParams_repNorm params tps htps]
  | .union ms m, _, h => by
    obtain ⟨ts, hts⟩ := (ofRepresentationJson_inv h).2.2.2.2.1 ms m rfl
    simp only [Ast.repNorm, ofRepresentationMembers_repNorm ms ts hts]
  | .tuple e es r, _, h => by
    obtain ⟨⟨x, hx⟩, ⟨xs, hxs⟩, ⟨rs, hrs⟩⟩ :=
      (ofRepresentationJson_inv h).2.2.2.2.2.1 e es r rfl
    simp only [Ast.repNorm, ofRepresentationElement_repNorm e x hx,
      ofRepresentationElements_repNorm es xs hxs,
      ofRepresentationRest_repNorm r rs hrs]

theorem ofRepresentationProperties_repNorm :
    ∀ (fs : List (String × Bool × Ast)) (ps : List Json.Value),
      ofRepresentationProperties ps = some fs → repNormFields fs = fs
  | [], _, _ => rfl
  | (n, o, a) :: fs, _, h => by
    obtain ⟨⟨t, ht⟩, ⟨ps', hps'⟩⟩ := ofRepresentationProperties_inv h
    simp only [repNormFields, ofRepresentationJson_repNorm a t ht,
      ofRepresentationProperties_repNorm fs ps' hps']

theorem ofRepresentationParams_repNorm :
    ∀ (as : List Ast) (vs : List Json.Value),
      ofRepresentationParams vs = some as → repNormParams as = as
  | [], _, _ => rfl
  | a :: as, _, h => by
    obtain ⟨⟨t, ht⟩, ⟨vs', hvs'⟩⟩ := ofRepresentationParams_inv h
    simp only [repNormParams, ofRepresentationJson_repNorm a t ht,
      ofRepresentationParams_repNorm as vs' hvs']

theorem ofRepresentationMembers_repNorm :
    ∀ (as : List Ast) (vs : List Json.Value),
      ofRepresentationMembers vs = some as → repNormMembers as = as
  | [], _, _ => rfl
  | a :: as, _, h => by
    obtain ⟨⟨t, ht⟩, ⟨vs', hvs'⟩⟩ := ofRepresentationMembers_inv h
    simp only [repNormMembers, ofRepresentationJson_repNorm a t ht,
      ofRepresentationMembers_repNorm as vs' hvs']

theorem ofRepresentationElement_repNorm :
    ∀ (e : Bool × Ast) (v : Json.Value),
      ofRepresentationElement v = some e → repNormElement e = e
  | (o, a), _, h => by
    obtain ⟨t, ht⟩ := ofRepresentationElement_inv h
    simp only [repNormElement, ofRepresentationJson_repNorm a t ht]

theorem ofRepresentationElements_repNorm :
    ∀ (es : List (Bool × Ast)) (vs : List Json.Value),
      ofRepresentationElements vs = some es → repNormElements es = es
  | [], _, _ => rfl
  | e :: es, _, h => by
    obtain ⟨⟨t, ht⟩, ⟨vs', hvs'⟩⟩ := ofRepresentationElements_inv h
    simp only [repNormElements, ofRepresentationElement_repNorm e t ht,
      ofRepresentationElements_repNorm es vs' hvs']

theorem ofRepresentationRest_repNorm :
    ∀ (r : Option Ast) (vs : List Json.Value),
      ofRepresentationRest vs = some r → repNormRest r = r
  | none, _, _ => rfl
  | some a, _, h => by
    obtain ⟨t, ht⟩ := ofRepresentationRest_inv h
    simp only [repNormRest, ofRepresentationJson_repNorm a t ht]

end

/-- **Decoder soundness for `RepNormal`** (the obligation this module
carried as open until slice 2's secondary): every code the revision-1
decoder answers is its own normal form. With
`ofRepresentationJson_toRepresentationJson'` in the other direction,
`RepNormal` is exactly the subset the revision-1 projection is a
bijection onto — the projection identifies `.lit .null` with `.null`
and nothing else, and the decoder answers only the survivors. -/
theorem ofRepresentationJson_repNormal {v : Json.Value} {a : Ast}
    (h : Ast.ofRepresentationJson v = some a) : a.RepNormal :=
  ofRepresentationJson_repNorm a v h

/-- The document decoder inherits it. -/
theorem ofRepresentationDocument_repNormal {v : Json.Value} {a : Ast}
    (h : Ast.ofRepresentationDocument v = some a) : a.RepNormal := by
  rw [Ast.ofRepresentationDocument.eq_def] at h
  split at h
  · exact ofRepresentationJson_repNormal h
  · simp at h

/-- The envelope decoder inherits it, so every code that comes through
the revision-1 door is `RepNormal` and `ofEnvelope_envelope'` applies
to it without a side condition to discharge. -/
theorem ofEnvelope_repNormal {v : Json.Value} {a : Ast}
    (h : Ast.ofEnvelope v = some a) : a.RepNormal := by
  rw [Ast.ofEnvelope.eq_def] at h
  split at h
  · split at h
    · exact ofRepresentationDocument_repNormal h
    · simp at h
  · simp at h

end Cas.Schema
