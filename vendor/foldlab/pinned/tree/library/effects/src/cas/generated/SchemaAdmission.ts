/**
 * GENERATED — do not edit. THE ADMISSION TABLE: what
 * `Cas.Schema.ingest` admits, as data, emitted from
 * `library/cas/Cas/Backend/Admission.lean` by `lake exe emitgate`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`).
 *
 * `CanonicalSchema.admitDocument` is an interpreter over this table.
 * Every column here is read off the Lean definitions — the node tags
 * and key lists off `Ast.toRepresentationJson`, the check spelling off
 * the `Number` node's own projection, the declaration payload column
 * probed out of `DeclarationId.payloadWf` — except the clause table,
 * which is a hand column tied to `ingest`'s answers by `#guard`.
 *
 * The key lists are the REQUIRED keys, not an exact set: Effect's own
 * `toJson` writes an `annotations` bag on a `Declaration` node that
 * the Lean spelling does not carry, so exact-key enforcement would
 * refuse three registry rows as they are actually stored. That gap is
 * a ruling, recorded in Admission.lean, not a translation.
 *
 * emitted — schemaVersion 1, emitter `emitgate`,
 * module `library/cas/tools/EmitGate.lean`, toolchain Lean 4.33.1.
 */

/** THE refusal taxonomy, verbatim from Lean `Cas.Schema.IngestRefusal`:
 * the two doors name the same refusals or they are not two doors onto
 * one language. */
export type Refusal = "notASchema" | "illFormed" | "wrongRevision" | "nonEmptyReferences" | "unguardedCycle" | "unknownDeclaration"

/** One discipline clause: the name the interpreter looks it up by, the
 * refusal it carries, and the prose it reads. `{path}`, `{it}` and
 * `{keys}` are the interpreter's three substitutions. */
export interface Clause {
  readonly clause: string
  readonly refusal: Refusal
  readonly detail: string
}

/** Which arm of the interpreter reads a node. */
export type Form = "keyword" | "number" | "literal" | "arrays" | "objects" | "declaration" | "union" | "enum" | "reference" | "suspend"

/** One admitted representation node: its tag, the arm that reads it,
 * the keys the canonical spelling writes, and its checks policy.
 * `none` is the Reference row: that node carries no `checks` key at
 * all, so there is no array for a policy to be about. */
export interface NodeRow {
  readonly tag: string
  readonly form: Form
  readonly keys: ReadonlyArray<string>
  readonly checks: "empty" | "isInt" | "none"
}

/** One admitted `{type, value}` spelling: the type tag the projection
 * writes, and the predicate the reader applies to the value. */
export interface TypedValueRow {
  readonly type: string
  readonly admits: "boolean" | "safeInteger" | "string"
}

/** A declaration row's payload discipline, mirroring Lean
 * `DeclarationId.payloadWf`: `byte` is a natural number below
 * `PayloadByteBound` (a kind tag), `null` is the null payload. */
export type DeclarationPayload = "byte" | "null"

/** One row of the declaration registry, without its reviver: the
 * persistence identity, the type parameters it takes, and the payload
 * its row admits. */
export interface DeclarationRow {
  readonly id: string
  readonly arity: number
  readonly payload: DeclarationPayload
}

/** Every refusal the door can name, in Lean's declaration order. */
export const Refusals: ReadonlyArray<Refusal> = ["notASchema", "illFormed", "wrongRevision", "nonEmptyReferences", "unguardedCycle", "unknownDeclaration"]

/** The discipline clauses, by name. */
export const Clauses: ReadonlyArray<Clause> = [
  {
    clause: "notAnObject",
    refusal: "notASchema",
    detail: "{path} is not an object",
  },
  {
    clause: "notAnArray",
    refusal: "notASchema",
    detail: "{path} is not an array",
  },
  {
    clause: "unadmittedNode",
    refusal: "notASchema",
    detail: "{path} is a {it} node, which the admitted subset does not carry",
  },
  {
    clause: "nodeKeys",
    refusal: "notASchema",
    detail: "{path} does not carry {keys}, which is what the canonical spelling of this node writes",
  },
  {
    clause: "checksNotEmpty",
    refusal: "notASchema",
    detail: "{path} carries checks: the admitted subset carries the isInt check on Number and no other (the checks layer is Slice C5)",
  },
  {
    clause: "notTheIntCheck",
    refusal: "notASchema",
    detail: "{path} is not the admitted integer: the subset carries Number under exactly the effect/schema/isInt check, and a bare Number would type a float the value plane has no term for (ruling 15, the float ceiling)",
  },
  {
    clause: "literalShape",
    refusal: "notASchema",
    detail: "{path} is not an admitted literal: booleans, strings, and safe integers only (a null literal is the Null keyword, register R13)",
  },
  {
    clause: "restTooMany",
    refusal: "notASchema",
    detail: "{path} carries {it} rest types, and the admitted subset refuses more than one structurally (trailing-rest semantics stay deferred)",
  },
  {
    clause: "emptyTuple",
    refusal: "notASchema",
    detail: "{path} is the empty tuple, which no constructor spells: a plain array is zero elements and one rest type, a tuple is at least one element",
  },
  {
    clause: "elementShape",
    refusal: "notASchema",
    detail: "{path} does not spell a tuple element: the admitted subset writes {keys} and no annotation bag (C-ann)",
  },
  {
    clause: "elementOptionality",
    refusal: "notASchema",
    detail: "{path}.isOptional is not a boolean",
  },
  {
    clause: "indexSignatures",
    refusal: "notASchema",
    detail: "{path} carries index signatures, which the admitted subset does not reach (records are Slice C3)",
  },
  {
    clause: "propertyShape",
    refusal: "notASchema",
    detail: "{path} does not spell a property signature: the admitted subset writes {keys}",
  },
  {
    clause: "propertyMutable",
    refusal: "notASchema",
    detail: "{path} is mutable, which the admitted subset does not carry",
  },
  {
    clause: "propertyOptionality",
    refusal: "notASchema",
    detail: "{path}.isOptional is not a boolean",
  },
  {
    clause: "propertyName",
    refusal: "notASchema",
    detail: "{path}.name is not a string name (symbol keys have no reconstructable identity)",
  },
  {
    clause: "propertyOrder",
    refusal: "illFormed",
    detail: "{path} declares {it} after {keys}: struct field names are in strict ascending order, which is what makes the canonical spelling unique and forbids a duplicate name",
  },
  {
    clause: "declarationShape",
    refusal: "notASchema",
    detail: "{path}.representation does not spell a declaration identity: the admitted subset writes {keys}",
  },
  {
    clause: "unknownDeclaration",
    refusal: "unknownDeclaration",
    detail: "unknown declaration {it} at {path} — the canonical schema registry admits only {keys}",
  },
  {
    clause: "declarationPayload",
    refusal: "illFormed",
    detail: "{path}: the declaration's registry row does not admit the payload {it}",
  },
  {
    clause: "declarationArity",
    refusal: "illFormed",
    detail: "{path}: the declaration's registry row does not take {it} type parameters",
  },
  {
    clause: "unionMode",
    refusal: "notASchema",
    detail: "{path}.mode is {it}, which is no union mode — the modes are {keys}",
  },
  {
    clause: "unionEmpty",
    refusal: "illFormed",
    detail: "{path} is the empty union, which is Never — and Never is not admitted",
  },
  {
    clause: "enumEmpty",
    refusal: "illFormed",
    detail: "{path} is the empty enum, which names no member — and the empty type is Never, which is not admitted",
  },
  {
    clause: "enumMemberShape",
    refusal: "notASchema",
    detail: "{path} is not a [name, value] pair",
  },
  {
    clause: "enumMemberValue",
    refusal: "notASchema",
    detail: "{path} carries a member value outside the admitted subset: strings and safe integers only (ruling 15, the float ceiling)",
  },
  {
    clause: "enumMemberName",
    refusal: "illFormed",
    detail: "{path} declares the member name {it} twice — member names are the enum's identity and never repeat (values may alias; names may not)",
  },
  {
    clause: "documentShape",
    refusal: "notASchema",
    detail: "{path} does not spell a representation document: the admitted subset writes {keys}",
  },
  {
    clause: "referenceName",
    refusal: "illFormed",
    detail: "{path} names an empty reference: a reference names a references-table entry, and the empty name names none (Effect refuses it too — $ref is a non-empty string)",
  },
  {
    clause: "referenceKeyEmpty",
    refusal: "illFormed",
    detail: "the references table carries an entry under the empty name, which no reference can point at",
  },
  {
    clause: "duplicateReferenceKey",
    refusal: "illFormed",
    detail: "the references table names {it} twice, so the two readers of this payload get two different documents — Lean's parser keeps both entries and takes the first, JSON.parse keeps the last. Give each entry one name; a canonical spelling has its keys in strict ascending order and cannot repeat one",
  },
  {
    clause: "unguardedCycle",
    refusal: "unguardedCycle",
    detail: "the references table has a cycle with no Suspend on it ({it}): resolving it never finishes, because unfolding the name gives the name back. Put the recursive position under a Suspend, which is what Effect writes for a recursive schema",
  },
  {
    clause: "nonEmptyReferences",
    refusal: "nonEmptyReferences",
    detail: "the document allocates a reference table ({it}), and this reader answers a single code — read it as a document instead",
  },
  {
    clause: "wrongRevision",
    refusal: "wrongRevision",
    detail: "unsupported canonical schema revision {it}",
  },
  {
    clause: "notASchema",
    refusal: "notASchema",
    detail: "Effect's persistent decoder does not read this spelling: {it}",
  },
  {
    clause: "excessProperties",
    refusal: "notASchema",
    detail: "canonical schema representation contains unsupported or excess properties",
  },
]

/** The admitted representation nodes. `Arrays` is ONE row: the plain
 * array and the tuple are one tag and one key list, told apart by
 * whether `elements` is empty, exactly as the Lean decoder tells them
 * apart. */
export const Nodes: ReadonlyArray<NodeRow> = [
  {
    tag: "Null",
    form: "keyword",
    keys: ["_tag", "checks"],
    checks: "empty",
  },
  {
    tag: "Boolean",
    form: "keyword",
    keys: ["_tag", "checks"],
    checks: "empty",
  },
  {
    tag: "String",
    form: "keyword",
    keys: ["_tag", "checks"],
    checks: "empty",
  },
  {
    tag: "Number",
    form: "number",
    keys: ["_tag", "checks"],
    checks: "isInt",
  },
  {
    tag: "Literal",
    form: "literal",
    keys: ["_tag", "checks", "literal"],
    checks: "empty",
  },
  {
    tag: "Arrays",
    form: "arrays",
    keys: ["_tag", "checks", "elements", "rest"],
    checks: "empty",
  },
  {
    tag: "Objects",
    form: "objects",
    keys: ["_tag", "checks", "indexSignatures", "propertySignatures"],
    checks: "empty",
  },
  {
    tag: "Declaration",
    form: "declaration",
    keys: ["_tag", "checks", "representation", "typeParameters"],
    checks: "empty",
  },
  {
    tag: "Union",
    form: "union",
    keys: ["_tag", "checks", "mode", "types"],
    checks: "empty",
  },
  {
    tag: "Enum",
    form: "enum",
    keys: ["_tag", "checks", "enums"],
    checks: "empty",
  },
  {
    tag: "Reference",
    form: "reference",
    keys: ["$ref", "_tag"],
    checks: "none",
  },
  {
    tag: "Suspend",
    form: "suspend",
    keys: ["_tag", "checks", "thunk"],
    checks: "empty",
  },
]

/** THE admitted check spelling, as its canonical JSON: Effect's
 * `effect/schema/isInt`, read off the `Number` node's own projection
 * and rendered by the canonical encoder rather than retyped. The
 * interpreter compares `canonicalJson(checks[0])` against this. */
export const IsIntCheckSpelling = "{\"_tag\":\"Filter\",\"aborted\":false,\"annotations\":{\"arbitrary\":{\"constraint\":{\"integer\":true}},\"expected\":\"an integer\"},\"representation\":{\"id\":\"effect/schema/isInt\",\"payload\":null}}"

/** The admitted literal spellings. */
export const LiteralTypes: ReadonlyArray<TypedValueRow> = [{ type: "boolean", admits: "boolean" }, { type: "number", admits: "safeInteger" }, { type: "string", admits: "string" }]

/** The admitted enum member value spellings. */
export const EnumValueTypes: ReadonlyArray<TypedValueRow> = [{ type: "string", admits: "string" }, { type: "number", admits: "safeInteger" }]

/** The union modes, from `Cas.Schema.UnionMode`. */
export const UnionModes: ReadonlyArray<string> = ["anyOf", "oneOf"]

/** THE declaration registry's columns, from `Cas.Schema.DeclarationId`,
 * row zero first. The payload column is probed out of
 * `DeclarationId.payloadWf`, not transcribed. */
export const Declarations: ReadonlyArray<DeclarationRow> = [
  {
    id: "foldlab/cas/ref",
    arity: 0,
    payload: "byte",
  },
  {
    id: "effect/schema/Date",
    arity: 0,
    payload: "null",
  },
  {
    id: "effect/schema/URL",
    arity: 0,
    payload: "null",
  },
  {
    id: "effect/schema/Option",
    arity: 1,
    payload: "null",
  },
]

/** The keys one property signature writes. */
export const PropertyKeys: ReadonlyArray<string> = ["isMutable", "isOptional", "name", "type"]

/** The keys a property signature's `name` slot writes. */
export const PropertyNameKeys: ReadonlyArray<string> = ["type", "value"]

/** The keys one tuple element writes. */
export const ElementKeys: ReadonlyArray<string> = ["isOptional", "type"]

/** The keys a literal's typed value writes. */
export const LiteralKeys: ReadonlyArray<string> = ["type", "value"]

/** The keys an enum member's value writes. */
export const EnumValueKeys: ReadonlyArray<string> = ["type", "value"]

/** The keys a declaration identity writes. */
export const DeclarationIdentityKeys: ReadonlyArray<string> = ["id", "payload"]

/** The keys the representation document writes. */
export const DocumentKeys: ReadonlyArray<string> = ["references", "representation"]

/** The keys the schema-node envelope writes. */
export const EnvelopeKeys: ReadonlyArray<string> = ["revision", "value"]

/** The kind-tag bound a `byte` payload obeys, counted out of
 * `DeclarationId.payloadWf` rather than restated. */
export const PayloadByteBound = 256

/** The safe-integer bound (`Cas.Schema.maxSafeNat`): the one number
 * range whose decimal rendering is language-neutral (CAS-004). */
export const MaxSafeInteger = 9007199254740991

/** The revision the door speaks. */
export const Revision = 1

/** The retired revision, kept readable for already-addressed nodes. */
export const LegacyRevision = 0
