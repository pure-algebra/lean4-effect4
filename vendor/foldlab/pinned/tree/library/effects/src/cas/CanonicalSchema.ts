/**
 * Canonical Effect Schema identity.
 *
 * Effect's persistent `SchemaRepresentation.Document` is the schema-plane
 * carrier. The CAS adds only its versioned node envelope and the declaration
 * reviver for typed CAS references; it does not maintain a parallel AST.
 */
import {
  Effect,
  Option,
  Predicate,
  Result,
  Schema,
  SchemaAST,
  SchemaRepresentation,
} from "effect"
import {
  Byte,
  ContentId,
  CasNodeInput,
  UnknownKind,
  WrongKindReference,
  type CasError,
} from "./Node.ts"
import {
  CasLoader,
  CasSchemeVersion,
  CasStore,
  encodeCasNode,
  type CasAddress,
} from "./Store.ts"
import { resolveAnnotation } from "./Annotations.ts"
import {
  canonicalJson,
  decodedVersionedEnvelope,
  ProjectionCodecFailure,
  referenceRepresentation,
  ReferenceRepresentationId,
  referenceRepresentationReviver,
  type DecodedEnvelope,
  type ProjectionError,
} from "./Value.ts"
import { SchemaKindTag } from "../internal/kindTags.ts"
import * as Admission from "./generated/SchemaAdmission.ts"
import type { StoreFailure } from "./Node.ts"

/** The current projection revision of schema nodes, from the generated
 * admission table (`Cas.Schema.schemaRevision`). */
export const Revision = Admission.Revision

/** The legacy private-AST revision, retained for read compatibility
 * (`Cas.Schema.legacySchemaRevision`). */
export const LegacyRevision = Admission.LegacyRevision

/** The reserved kind tag schema nodes carry. */
export const KindTag = SchemaKindTag

/** The non-persistent annotation used to pin a carrier to an identity. */
export const AnnotationKey = Symbol.for("foldlab/cas/canonical")

const strictOptions = {
  onExcessProperty: "error",
} satisfies SchemaAST.ParseOptions

const utf8Encoder = new TextEncoder()
const utf8Decoder = new TextDecoder()

const deepFreeze = <A>(value: A): A => {
  if (!Predicate.isObject(value) || Object.isFrozen(value)) return value
  for (const key of Reflect.ownKeys(value)) {
    deepFreeze(Reflect.get(value, key))
  }
  return Object.freeze(value)
}

/** Canonicalize only order-insensitive object property declarations inside
 * Effect's representation. Union, tuple, check, and reference order remain
 * semantic and are never rearranged. */
const normalizeRepresentationJson = (input: Schema.Json): Schema.Json => {
  if (Array.isArray(input)) {
    return input.map((item) => normalizeRepresentationJson(item))
  }
  if (!Predicate.isObject(input)) return input

  const normalized: Record<string, Schema.Json> = Object.fromEntries(
    Object.entries(input as Schema.JsonObject).map(([key, value]) => [
      key,
      normalizeRepresentationJson(value),
    ]),
  )
  if (
    normalized._tag === "Objects"
    && Array.isArray(normalized.propertySignatures)
  ) {
    normalized.propertySignatures = [...normalized.propertySignatures]
      .toSorted((left, right) => {
        const leftName = Predicate.isObject(left) ? left.name : null
        const rightName = Predicate.isObject(right) ? right.name : null
        const leftText = canonicalJson(leftName)
        const rightText = canonicalJson(rightName)
        return leftText < rightText ? -1 : leftText > rightText ? 1 : 0
      })
  }
  return normalized
}

/** Decode into fresh Effect-owned data, reject excess properties, run the
 * admitted-subset gate on the door path, normalize Effect's
 * order-insensitive object fields, and freeze the identity snapshot.
 *
 * `requireCanonicalOrder` is what tells a DOOR from a LOWERING.
 * `fromJson`, `fromEnvelope`, and the annotation read are doors: they
 * take a spelling from outside and must answer exactly what Lean's
 * `Cas.Schema.ingest` answers, which is `admitDocument`'s job. The
 * lowering path (`snapshotDocument`, `nativeDocument`) is the estate
 * projecting a schema it already holds, where field order is Effect's
 * declaration order and nothing foreign has arrived; it keeps the
 * declaration allowlist and nothing more. */
const documentFromJson = (
  input: Schema.Json,
  requireCanonicalOrder = true,
): SchemaRepresentation.Document => {
  // Effect's own persistent decoder runs first, and its rejections are
  // renamed rather than left anonymous: a spelling `fromJson` will not
  // read is not a schema, which is the name Lean's decoder gives it.
  // Every refusal out of this door therefore carries a taxonomy name.
  const document = ((): SchemaRepresentation.Document => {
    try {
      return SchemaRepresentation.fromJson(input)
    } catch (issue) {
      return refuseBy("notASchema", "document", String(issue))
    }
  })()
  const encoded = SchemaRepresentation.toJson(document)
  if (canonicalJson(input) !== canonicalJson(encoded)) {
    refuseBy("excessProperties", "document")
  }
  const normalized = normalizeRepresentationJson(encoded)
  // ONE walk on the door path: `admitDocument` tests the declaration
  // allowlist at every node it visits, so the separate traversal is
  // what the LOWERING path — which admits spellings the door does not —
  // still needs and the door no longer pays for.
  //
  // On the spelling AS STORED, not on the normalized one: sortedness is
  // a property of the bytes that arrived, and normalizing first would
  // sort the very thing under test.
  if (requireCanonicalOrder) admitDocument(encoded)
  else refuseUnknownDeclarations(normalized)
  return deepFreeze(SchemaRepresentation.fromJson(normalized))
}

const snapshotDocument = (
  document: SchemaRepresentation.Document,
): SchemaRepresentation.Document =>
  documentFromJson(SchemaRepresentation.toJson(document), false)

/** THE refusal taxonomy, verbatim from Lean `Cas.Schema.IngestRefusal`
 * — generated, not retyped. The two doors name the same refusals or
 * they are not two doors onto one language. */
export type Refusal = Admission.Refusal

/** A refusal BY NAME. The schema plane's doors are synchronous and
 * throw, so their callers can wrap them in one failure channel; what
 * this adds is the name, so a caller (and a differential gate) can tell
 * `illFormed` from `notASchema` instead of reading English. */
export class SchemaRefusal extends TypeError {
  readonly refusal: Refusal
  readonly detail: string
  constructor(refusal: Refusal, detail: string) {
    super(`${refusal}: ${detail}`)
    this.name = "SchemaRefusal"
    this.refusal = refusal
    this.detail = detail
  }
}

// A function DECLARATION, not an arrow: TypeScript only treats a call as
// unreachable-after (narrowing the code that follows) when the callee is
// declared this way, and every gate below leans on that.
function refuse(refusal: Refusal, detail: string): never {
  throw new SchemaRefusal(refusal, detail)
}

/** One row of the declaration registry: the generated columns — a
 * persistence identity, the number of type parameters the row takes,
 * and the payload discipline its row admits — plus the reviver, which
 * is the one thing the Lean registry cannot hold. */
export interface DeclarationRow extends Admission.DeclarationRow {
  readonly reviver: SchemaRepresentation.AnyReviver
}

/** The revivers behind the registry ids. This is the whole of what the
 * TypeScript side adds: an id, an arity, and a payload discipline are
 * facts about the language and arrive generated; a reviver is a
 * FUNCTION, and functions do not travel through a manifest. */
const declarationRevivers: Readonly<
  Record<string, SchemaRepresentation.AnyReviver>
> = {
  [ReferenceRepresentationId]: referenceRepresentationReviver,
  "effect/schema/Date": Schema.DateReviver,
  "effect/schema/Option": Schema.OptionReviver,
  "effect/schema/URL": Schema.URLReviver,
}

/** THE declaration registry: every declaration id a persisted canonical
 * schema may carry, row zero first.
 *
 * The columns are GENERATED from `Cas.Schema.DeclarationId`
 * (`SchemaAdmission.Declarations`), so there is no second table to keep
 * in step and no scraper to read the Lean source at test time — the
 * byte gate `lake exe emitgate --check` is what holds the two sides
 * together. Growing the set is adding a row in Lean and a reviver here;
 * a row that arrives with no reviver behind it fails LOUDLY, at import,
 * because there is nothing to revive it with.
 *
 * The three Effect rows are ADOPTED, not minted (PLAN P3/P4): each is a
 * built-in already shipping the whole `{id, reviver, toCode,
 * toArbitrary}` contract, so admitting them costs the estate no new
 * identity and Effect's own revival and code generation apply
 * unchanged. Their adoption is pending operator ratification
 * (SCHEMA-MATERIALIZATION.md ruling-queue item 7): rejecting a row is
 * deleting its one line, in Lean.
 *
 * ONE LIST. The row carries its own reviver, so the declaration arm of
 * `Revivers` is derived from this table rather than hand-kept beside it
 * — the allowlist the door gates on and the reviver set revival runs
 * under cannot come apart, because they are the same rows. */
export const DeclarationRegistry: ReadonlyArray<DeclarationRow> = Admission
  .Declarations.map((row) => {
    const reviver = declarationRevivers[row.id]
    if (reviver === undefined) {
      refuse(
        "unknownDeclaration",
        `the admission table admits ${row.id} and this package has no reviver for it`,
      )
    }
    return { ...row, reviver }
  })

const declarationRow = (id: unknown): DeclarationRow | undefined =>
  typeof id === "string"
    ? DeclarationRegistry.find((row) => row.id === id)
    : undefined

const admittedDeclarationIds: ReadonlyArray<string> = DeclarationRegistry.map(
  (row) => row.id,
)

/** The LOWERING path's declaration gate: a structural walk that refuses
 * any `Declaration` node whose `representation.id` is not a registry
 * row. Fail-closed — a declaration with no representation identity at
 * all is refused too, because there is nothing to admit it by.
 *
 * The DOOR does not call this. Its walk (`admitNode`) tests the same
 * thing at every node it visits, so the door pays for one traversal
 * rather than two. This one remains because the lowering path admits
 * spellings the door does not — a revision-0 projection carries
 * `isBetween` checks, which the admitted subset has no arm for — and
 * still owes the allowlist. */
const refuseUnknownDeclarations = (input: Schema.Json): void => {
  if (Array.isArray(input)) {
    for (const item of input) refuseUnknownDeclarations(item)
    return
  }
  if (!Predicate.isObject(input)) return
  const node = input as Schema.JsonObject
  if (node._tag === "Declaration") gateDeclarationRow(node, "representation")
  for (const value of Object.values(node)) refuseUnknownDeclarations(value)
}

/** THE admitted-subset gate — the TypeScript face of Lean's
 * `Ast.ofRepresentationJson` composed with `Ast.wf`, which together are
 * `Cas.Schema.ingest`.
 *
 * Before this gate the two doors disagreed (JIT-substrate survey B8,
 * SCHEMA-MATERIALIZATION.md ruling-queue item 19): the TypeScript door
 * ran Effect's shape decode and the declaration allowlist and nothing
 * else, so a stored node Lean refuses `illFormed` still materialized
 * into a live validator. The corpus in
 * `library/cas/conformance/schema-verdicts.json` is what holds the two
 * to one answer; this is the code that makes them agree.
 *
 * What follows is an INTERPRETER over the generated admission table
 * (`generated/SchemaAdmission.ts`), not a second reading of the
 * language. Which nodes exist, what keys each spells, which check
 * spelling `Number` carries, which literal and enum value types are
 * admitted, the union modes, the declaration columns, the safe-integer
 * bound, and the refusal each clause names — all of that is Lean's,
 * emitted by `lake exe emitgate` under a byte gate. This file supplies
 * only the WALK.
 *
 * Two disciplines, one walk, because Lean applies both at one door:
 *
 * - WHICH NODES — the admitted subset. Everything the table has no row
 *   for is `notASchema`, the same name Lean's decoder gives it. The
 *   subset is a SLICE PLAN, not a limit of Effect: each clause in the
 *   table names the slice that would admit what it refuses.
 * - THE DISCIPLINE — `Ast.wf`. Struct property names in strict
 *   ascending order (which subsumes no-duplicates), unions and enums
 *   nonempty, enum names distinct, and every declaration honouring its
 *   registry row's payload shape and type-parameter count. These are
 *   `illFormed`.
 *
 * The declaration allowlist is folded in: the walk tests it at every
 * node that calls itself a `Declaration`, so the door pays for ONE
 * traversal where it used to pay for two.
 *
 * It runs PRE-REVIVAL, on the spelling as stored, so a refusal is a
 * named refusal on the caller's own failure path rather than a throw
 * out of Effect's reviver — which is what three of the corpus rows used
 * to be. */
const clauses: ReadonlyMap<string, Admission.Clause> = new Map(
  Admission.Clauses.map((one) => [one.clause, one]),
)

const nodes: ReadonlyMap<string, Admission.NodeRow> = new Map(
  Admission.Nodes.map((one) => [one.tag, one]),
)

/** Refuse BY CLAUSE. The refusal name and the prose are the table's;
 * the walk contributes only where it is (`{path}`), what it saw
 * (`{it}`), and the list the clause is about (`{keys}`). */
function refuseBy(
  clause: string,
  path: string,
  it: Schema.Json = null,
  keys: ReadonlyArray<string> = [],
): never {
  const row = clauses.get(clause)
  if (row === undefined) {
    refuse("notASchema", `${path}: no clause ${clause} in the admission table`)
  }
  refuse(
    row.refusal,
    row.detail
      .replaceAll("{path}", path)
      .replaceAll("{it}", canonicalJson(it))
      .replaceAll("{keys}", keys.join(", ")),
  )
}

const gateObject = (
  value: Schema.Json | undefined,
  path: string,
): Schema.JsonObject => {
  if (!Predicate.isObject(value) || Array.isArray(value)) {
    refuseBy("notAnObject", path)
  }
  return value as Schema.JsonObject
}

const gateArray = (
  value: Schema.Json | undefined,
  path: string,
): ReadonlyArray<Schema.Json> => {
  if (!Array.isArray(value)) refuseBy("notAnArray", path)
  return value
}

/** Every key the canonical spelling writes is present. REQUIRED, not
 * exact: Effect's own `toJson` adds an `annotations` bag to a
 * `Declaration` node that the Lean spelling does not carry, so exact
 * enforcement would refuse three registry rows as they are actually
 * stored. That gap is a recorded ruling, not a translation. */
const gateKeys = (
  node: Schema.JsonObject,
  keys: ReadonlyArray<string>,
  clause: string,
  path: string,
): void => {
  if (keys.some((key) => !(key in node))) refuseBy(clause, path, null, keys)
}

/** The checks policy: empty on every node but `Number`, which carries
 * exactly the one admitted spelling and nothing else — and `Reference`,
 * which carries no `checks` key at all, so there is no array for a
 * policy to be about. */
const gateChecks = (
  node: Schema.JsonObject,
  row: Admission.NodeRow,
  path: string,
): void => {
  if (row.checks === "none") return
  const checks = gateArray(node.checks, `${path}.checks`)
  if (row.checks === "empty") {
    if (checks.length !== 0) refuseBy("checksNotEmpty", path)
    return
  }
  if (
    checks.length !== 1
    || canonicalJson(checks[0] ?? null) !== Admission.IsIntCheckSpelling
  ) {
    refuseBy("notTheIntCheck", path)
  }
}

/** The two positions that carry a `{type, value}` pair, and the rows
 * admitted at each. The clause name is the key, so a call site names
 * the refusal and the admitted set at once. */
const typedValues = {
  enumMemberValue: {
    keys: Admission.EnumValueKeys,
    rows: Admission.EnumValueTypes,
  },
  literalShape: { keys: Admission.LiteralKeys, rows: Admission.LiteralTypes },
} as const

/** One `{type, value}` pair — a literal, or an enum member's value —
 * against the admitted rows for that position. */
const gateTypedValue = (
  value: Schema.Json | undefined,
  clause: keyof typeof typedValues,
  path: string,
): void => {
  const { keys, rows } = typedValues[clause]
  const typed = gateObject(value, path)
  gateKeys(typed, keys, clause, path)
  const row = rows.find((one) => one.type === typed.type)
  const carried = typed.value
  const admitted = row === undefined
    ? false
    : row.admits === "boolean"
    ? typeof carried === "boolean"
    : row.admits === "string"
    ? typeof carried === "string"
    : typeof carried === "number" && Number.isInteger(carried)
      && Math.abs(carried) <= Admission.MaxSafeInteger
  if (!admitted) refuseBy(clause, path, null, keys)
}

/** The allowlist, at one node, answering the ROW it admitted by.
 * Fail-closed: a `Declaration` with no readable identity is refused
 * too, because there is nothing to admit it by. */
const gateDeclarationRow = (
  node: Schema.JsonObject,
  path: string,
): DeclarationRow => {
  const identity = node.representation
  const id = Predicate.isObject(identity)
    ? (identity as Schema.JsonObject).id
    : undefined
  const row = declarationRow(id)
  if (row === undefined) {
    refuseBy(
      "unknownDeclaration",
      path,
      (id ?? null) as Schema.Json,
      admittedDeclarationIds,
    )
  }
  return row
}

/** The row's payload discipline, mirroring `DeclarationId.payloadWf`,
 * with the kind-tag bound read off the table. */
const admitsPayload = (
  row: DeclarationRow,
  payload: Schema.Json | undefined,
): boolean =>
  row.payload === "null"
    ? payload === null
    : typeof payload === "number" && Number.isInteger(payload)
      && payload >= 0 && payload < Admission.PayloadByteBound

const admitNode = (value: Schema.Json | undefined, path: string): void => {
  const node = gateObject(value, path)
  // The allowlist runs BEFORE the shape gate, so an unadmitted id is
  // named `unknownDeclaration` rather than dying of whatever else its
  // node happens to spell — the precedence the separate declaration
  // traversal used to give it, kept while folding it into this walk.
  const declaration = node._tag === "Declaration"
    ? gateDeclarationRow(node, path)
    : undefined
  const row = nodes.get(typeof node._tag === "string" ? node._tag : "")
  if (row === undefined) refuseBy("unadmittedNode", path, node._tag ?? null)
  gateKeys(node, row.keys, "nodeKeys", path)
  gateChecks(node, row, path)
  switch (row.form) {
    case "keyword":
    case "number": {
      return
    }
    case "literal": {
      gateTypedValue(node.literal, "literalShape", `${path}.literal`)
      return
    }
    case "arrays": {
      // ONE row, two shapes, told apart exactly as the Lean decoder
      // tells them apart: no elements and one rest type is the plain
      // array, at least one element is the tuple.
      const elements = gateArray(node.elements, `${path}.elements`)
      const rest = gateArray(node.rest, `${path}.rest`)
      if (rest.length > 1) refuseBy("restTooMany", path, rest.length)
      if (elements.length === 0 && rest.length !== 1) refuseBy("emptyTuple", path)
      for (const [index, element] of elements.entries()) {
        const at = `${path}.elements[${index}]`
        const signature = gateObject(element, at)
        if ("annotations" in signature) {
          refuseBy("elementShape", at, null, Admission.ElementKeys)
        }
        gateKeys(signature, Admission.ElementKeys, "elementShape", at)
        if (typeof signature.isOptional !== "boolean") {
          refuseBy("elementOptionality", at)
        }
        admitNode(signature.type, `${path}[${index}]`)
      }
      if (rest.length === 1) admitNode(rest[0], `${path}[]`)
      return
    }
    case "objects": {
      if (gateArray(node.indexSignatures, `${path}.indexSignatures`).length !== 0) {
        refuseBy("indexSignatures", path)
      }
      let previous: string | undefined
      const properties = gateArray(
        node.propertySignatures,
        `${path}.propertySignatures`,
      )
      for (const [index, property] of properties.entries()) {
        const at = `${path}.propertySignatures[${index}]`
        const signature = gateObject(property, at)
        gateKeys(signature, Admission.PropertyKeys, "propertyShape", at)
        if (signature.isMutable !== false) refuseBy("propertyMutable", at)
        if (typeof signature.isOptional !== "boolean") {
          refuseBy("propertyOptionality", at)
        }
        const name = gateObject(signature.name, `${at}.name`)
        gateKeys(name, Admission.PropertyNameKeys, "propertyShape", `${at}.name`)
        if (name.type !== "string" || typeof name.value !== "string") {
          refuseBy("propertyName", at)
        }
        const current = name.value
        if (previous !== undefined && !(previous < current)) {
          refuseBy("propertyOrder", path, current, [canonicalJson(previous)])
        }
        previous = current
        admitNode(signature.type, `${path}.${current}`)
      }
      return
    }
    case "declaration": {
      const identity = gateObject(node.representation, `${path}.representation`)
      gateKeys(
        identity,
        Admission.DeclarationIdentityKeys,
        "declarationShape",
        path,
      )
      // The allowlist ran at the head of this walk and answered the row;
      // the fallback is total, not a second gate.
      const admitted = declaration ?? gateDeclarationRow(node, path)
      if (!admitsPayload(admitted, identity.payload)) {
        refuseBy("declarationPayload", path, identity.payload ?? null)
      }
      const parameters = gateArray(node.typeParameters, `${path}.typeParameters`)
      if (parameters.length !== admitted.arity) {
        refuseBy("declarationArity", path, parameters.length)
      }
      for (const [index, parameter] of parameters.entries()) {
        admitNode(parameter, `${path}<${index}>`)
      }
      return
    }
    case "union": {
      const mode = node.mode
      if (typeof mode !== "string" || !Admission.UnionModes.includes(mode)) {
        refuseBy("unionMode", path, mode ?? null, Admission.UnionModes)
      }
      const types = gateArray(node.types, `${path}.types`)
      if (types.length === 0) refuseBy("unionEmpty", path)
      for (const [index, member] of types.entries()) {
        admitNode(member, `${path}|${index}`)
      }
      return
    }
    case "enum": {
      const members = gateArray(node.enums, `${path}.enums`)
      if (members.length === 0) refuseBy("enumEmpty", path)
      const seen = new Set<string>()
      for (const [index, member] of members.entries()) {
        const at = `${path}.enums[${index}]`
        if (!Array.isArray(member) || member.length !== 2) {
          refuseBy("enumMemberShape", at)
        }
        const name = member[0]
        if (typeof name !== "string") refuseBy("enumMemberShape", at)
        if (seen.has(name)) refuseBy("enumMemberName", path, name)
        seen.add(name)
        gateTypedValue(member[1], "enumMemberValue", at)
      }
      return
    }
    // The C6 arms. A reference is a NAME — nonempty, and nothing else is
    // asked of it here: whether it RESOLVES is not this gate's question
    // (Lean's `Ast.reference` records why), and whether the table it
    // names is guarded is the document gate's, below.
    case "reference": {
      if (typeof node.$ref !== "string" || node.$ref === "") {
        refuseBy("referenceName", path)
      }
      return
    }
    case "suspend": {
      admitNode(node.thunk, `${path}~`)
      break
    }
  }
}

/** Every table name a code mentions, at ANY position — the walk
 * `bareRefs` (below) is the guarded half of. This one does not stop at a
 * `Suspend`, because resolving a name is a question about reachability
 * and a delayed reference is still reached: the linked list's only
 * reference lives under its suspension, and a resolver that stopped
 * there would resolve nothing at all. */
const allRefs = (value: Schema.Json | undefined): ReadonlyArray<string> => {
  const out: Array<string> = []
  const walk = (v: Schema.Json | undefined): void => {
    if (Array.isArray(v)) {
      for (const item of v) walk(item)
      return
    }
    if (!Predicate.isObject(v)) return
    const node = v as Schema.JsonObject
    if (node._tag === "Reference") {
      if (typeof node.$ref === "string") out.push(node.$ref)
      return
    }
    for (const child of Object.values(node)) walk(child as Schema.Json)
  }
  walk(value)
  return out
}

/** The table names a code mentions at positions NO `Suspend` guards —
 * `Ast.bareRefs`, interpreted. The walk stops dead at a `Suspend`, which
 * is the whole content of the word "guarded". */
const bareRefs = (value: Schema.Json | undefined): ReadonlyArray<string> => {
  const out: Array<string> = []
  const walk = (v: Schema.Json | undefined): void => {
    if (Array.isArray(v)) {
      for (const item of v) walk(item)
      return
    }
    if (!Predicate.isObject(v)) return
    const node = v as Schema.JsonObject
    // THE GUARD. Everything under a Suspend is hidden from this walk.
    if (node._tag === "Suspend") return
    if (node._tag === "Reference") {
      if (typeof node.$ref === "string") out.push(node.$ref)
      return
    }
    for (const child of Object.values(node)) walk(child as Schema.Json)
  }
  walk(value)
  return out
}

/** The memoized search of `Document.settleAll`, interpreted: does every
 * bare path out of `name` run out within `fuel` steps?
 *
 * `settled` is the names already known to settle. Without it the search
 * re-walks every path and the door is `Θ(2ⁿ)` in the table size — a
 * table whose entries each name the next one twice took 18 271 ms at 23
 * ACYCLIC entries, and doubles per entry. That is the shape the break
 * pass measured (PDD-3 finding F3), and this is the ingestion door for
 * foreign content, so the input is attacker-chosen.
 *
 * A name enters `settled` only after its whole subtree settled, so
 * membership means "no bare path out of this name goes on forever" — a
 * property of the table and not of the fuel that happened to be left.
 * That is what makes a hit at one fuel sound at another, and it is why
 * a name on a cycle never enters the set: the walk never gets back out
 * to add it. Lean's `references_guarded_decidable_memo` is the same
 * statement over the same schedule. */
const settles = (
  references: Schema.JsonObject,
  fuel: number,
  name: string,
  settled: Set<string>,
): boolean => {
  if (settled.has(name)) return true
  const successors = Object.hasOwn(references, name)
    ? bareRefs(references[name])
    : []
  if (fuel === 0) {
    if (successors.length !== 0) return false
    settled.add(name)
    return true
  }
  for (const next of successors) {
    if (!settles(references, fuel - 1, next, settled)) return false
  }
  settled.add(name)
  return true
}

/** The document gate: the references table and one admitted root.
 *
 * The table is READ now (increment C6, ruled 2026-08-30) rather than
 * refused: every entry is an admitted code, no name is empty, and the
 * table is GUARDED — every cycle of the reference relation passes
 * through a `Suspend`. The guardedness search is `Document.guarded`
 * interpreted, fuel and all, and Lean's
 * `references_guarded_decidable` is what says that search decides the
 * absence of a cycle rather than approximating it.
 *
 * Not asked, deliberately, and each with its reason recorded in Lean: a
 * DANGLING name is admitted (it has no outgoing edge, so it lies on no
 * cycle), a DEAD entry is admitted, and key ORDER is normalised rather
 * than refused, because the table is a JSON object and the canonical
 * form sorts it. */
const admitDocument = (value: Schema.Json): void => {
  const document = gateObject(value, "document")
  gateKeys(document, Admission.DocumentKeys, "documentShape", "document")
  const references = gateObject(document.references, "document.references")
  const names = Object.keys(references)
  // THE ORDER IS LEAN'S, not this walk's (R10, and PDD-3 break-pass
  // finding F5: a table entry that was both cyclic and ill formed
  // earned `unguardedCycle` there and `illFormed` here).
  // `Cas.Schema.ingestDocument` decodes the whole document first, so a
  // spelling that is no code at all is refused before anything is
  // decided about the table; then it tests guardedness AHEAD of every
  // other discipline. One walk still does both, so the disciplines'
  // refusal is HELD and replayed after the guardedness filter.
  //
  // The stage a refusal belongs to is read off its NAME, which is the
  // admission table's column: `notASchema` and `unknownDeclaration` are
  // the decoder's answers and win immediately; `illFormed` is a
  // discipline's and waits.
  let held: SchemaRefusal | undefined
  const hold = (run: () => void): void => {
    try {
      run()
    } catch (issue) {
      if (!(issue instanceof SchemaRefusal) || issue.refusal !== "illFormed") {
        throw issue
      }
      held ??= issue
    }
  }
  for (const name of names) {
    hold(() => {
      if (name === "") refuseBy("referenceKeyEmpty", "document.references")
      admitNode(references[name], `document.references.${name}`)
    })
  }
  hold(() => admitNode(document.representation, "representation"))
  // Fuel is the table's own size, exactly as in Lean: a failing path
  // then visits one more name than the table has entries, which is what
  // forces a repeat and makes the search complete. The memo is shared
  // across the whole table, so each name is settled once however many
  // other names reach it.
  const settled = new Set<string>()
  const unguarded = names.filter((name) =>
    !settles(references, names.length, name, settled)
  )
  if (unguarded.length > 0) {
    refuseBy("unguardedCycle", "document.references", unguarded)
  }
  if (held !== undefined) throw held
}

/** A references-table key spelled TWICE, read from the payload BYTES.
 *
 * This has to happen before any parser runs, because `JSON.parse` keeps
 * the LAST pair of a duplicate key and Lean's `Cas.Json.parse` keeps
 * both and takes the FIRST — so one byte string is two different
 * documents depending on who read it, and the break pass exhibited both
 * directions (PDD-3 finding F1). Neither reading is more right, so the
 * door refuses the spelling instead of picking a winner. It costs
 * nothing real: a canonical spelling has its keys in strict ascending
 * order and cannot repeat one.
 *
 * SCOPED TO THE REFERENCES TABLE, deliberately. A duplicate key
 * elsewhere — a repeated `_tag` on a node — splits the same way, but it
 * predates the references table and the two doors have not been
 * reconciled on it; naming it here would claim an agreement nobody
 * ruled. It is recorded as owed in the PDD-3 packet.
 *
 * The scan needs no validation of its own: the payload is parsed either
 * side of it, so all it tracks is where it is. A string literal
 * followed by `:` inside an object is a key, and the key path that
 * reached each container says which object it belongs to. */
/** One JSON string literal's VALUE, from its source text — written out
 * rather than parsed, because the ratified JSON codec is
 * `src/cas/Value.ts` and this scan reads a payload the parser has not
 * seen yet. Two spellings of one key (`"A"` and `"A"`) are the
 * same name to Lean's reader, so the scan has to unescape before it
 * compares. */
const stringLiteral = (source: string): string => {
  let out = ""
  let index = 1
  while (index < source.length - 1) {
    const char = source[index] ?? ""
    if (char !== "\\") {
      out += char
      index += 1
      continue
    }
    const escape = source[index + 1] ?? ""
    if (escape === "u") {
      const point = Number.parseInt(source.slice(index + 2, index + 6), 16)
      // A lone surrogate is a code POINT here, not a character: a pair
      // arrives as two escapes and concatenates back into one.
      out += Number.isNaN(point)
        ? source.slice(index, index + 6)
        : String.fromCodePoint(point)
      index += 6
      continue
    }
    const named: Record<string, string> = {
      b: "\b",
      f: "\f",
      n: "\n",
      r: "\r",
      t: "\t",
    }
    out += named[escape] ?? escape
    index += 2
  }
  return out
}

const duplicateReferenceKey = (text: string): string | undefined => {
  /** A container the scan is inside: the key path that reached it, and
   * — for objects — the keys seen in it so far. An array frame has no
   * key set. */
  interface Frame {
    readonly path: ReadonlyArray<string>
    readonly keys: Set<string> | undefined
  }
  const frames: Array<Frame> = []
  /** The last string literal read. */
  let pending: string | undefined
  /** The key the next container sits under. */
  let key: string | undefined
  let index = 0
  while (index < text.length) {
    const char = text[index]
    if (char === "\"") {
      let end = index + 1
      while (end < text.length && text[end] !== "\"") {
        end += text[end] === "\\" ? 2 : 1
      }
      pending = stringLiteral(text.slice(index, end + 1))
      index = end + 1
      continue
    }
    if (char === "{" || char === "[") {
      const parent = frames.at(-1)
      frames.push({
        path: parent === undefined ? [] : [...parent.path, key ?? ""],
        keys: char === "{" ? new Set<string>() : undefined,
      })
      pending = undefined
      key = undefined
      index += 1
      continue
    }
    if (char === "}" || char === "]") {
      frames.pop()
      pending = undefined
      key = undefined
      index += 1
      continue
    }
    if (char === ":") {
      const frame = frames.at(-1)
      if (frame?.keys !== undefined && pending !== undefined) {
        const inTable = frame.path.length === 2
          && frame.path[0] === "value"
          && frame.path[1] === "references"
        if (inTable && frame.keys.has(pending)) return pending
        frame.keys.add(pending)
        key = pending
      }
      pending = undefined
      index += 1
      continue
    }
    if (char === ",") {
      pending = undefined
      key = undefined
    }
    index += 1
  }
  return undefined
}

/** The BYTES gate: refuse a references table that names one entry
 * twice, before any parser has thrown one of the pairs away. Every
 * other door on this plane takes a value that has already been parsed,
 * so this is the one check that has to see the payload itself. */
export const admitPayloadSpelling = (payload: Uint8Array): void => {
  const repeated = duplicateReferenceKey(utf8Decoder.decode(payload))
  if (repeated !== undefined) {
    refuseBy("duplicateReferenceKey", "document.references", repeated)
  }
}

const nativeDocument = (schema: Schema.Top): SchemaRepresentation.Document =>
  snapshotDocument(SchemaRepresentation.toRepresentation(schema.ast))

const documentOf = (
  identity: Schema.Top | SchemaRepresentation.Document,
): SchemaRepresentation.Document =>
  Schema.isSchema(identity) ? representationOf(identity) : snapshotDocument(identity)

/** The frozen native representation carried by a runtime schema.
 *
 * The pin is read through `resolveAnnotation`, not off `ast.annotations`:
 * `annotate` lands on the last check when the carrier has checks, and
 * Effect's own resolution reads that slot, so a carrier pinned after a
 * `.check(...)` would otherwise lose its identity in silence and fall
 * back to its native representation. */
export const representationOf = (
  schema: Schema.Top,
): SchemaRepresentation.Document => {
  const carried = resolveAnnotation(schema.ast, AnnotationKey)
  if (carried === undefined) return nativeDocument(schema)
  const json = Schema.decodeUnknownSync(Schema.Json, strictOptions)(carried)
  return documentFromJson(json)
}

/** The check revivers: built-in ids reused VERBATIM, nothing minted.
 * `isInt` is the one check the admitted subset carries; `isBetween` and
 * `isPattern` serve the legacy revision-0 projection and the estate's
 * own native lowerings, which do not travel through the door's gate. */
export const CheckRevivers: ReadonlyArray<SchemaRepresentation.AnyReviver> = [
  Schema.isIntReviver,
  Schema.isBetweenReviver,
  Schema.isPatternReviver,
]

/** The estate's reviver registry: every declaration and check identity a
 * persisted canonical schema may carry.
 *
 * The declaration arm is DERIVED from `DeclarationRegistry` — one row,
 * one reviver, no second list to keep in step. That is the allowlist
 * reconciliation the survey's B8 asked for: the set the door admits and
 * the set revival can rebuild are the same rows by construction, so an
 * id can no longer be admitted with no reviver behind it (or revived
 * without being admitted). */
export const Revivers: ReadonlyArray<SchemaRepresentation.AnyReviver> = [
  ...CheckRevivers,
  ...DeclarationRegistry.map((row) => row.reviver),
]

/** Reconstruct a runtime Effect Schema from a persisted identity. */
export const fromRepresentation = (
  document: SchemaRepresentation.Document,
): Schema.Top => {
  const snapshot = snapshotDocument(document)
  return SchemaRepresentation.fromRepresentation(snapshot, {
    revivers: Revivers,
  }).annotate({
    [AnnotationKey]: deepFreeze(SchemaRepresentation.toJson(snapshot)),
  })
}

/** Construct a carrier from Effect's own AST, snapshotting through Effect's
 * persistent representation so later caller mutation cannot alter identity. */
export const fromAst = (ast: SchemaAST.AST): Schema.Top => {
  const document = snapshotDocument(SchemaRepresentation.toRepresentation(ast))
  return fromRepresentation(document)
}

/** Strictly decode a persisted native representation document. */
export const fromJson = (input: Schema.Json): SchemaRepresentation.Document =>
  documentFromJson(input)

/** Project one decoded `{revision, value}` schema envelope into the
 * canonical document. This is the SINGLE revision switch behind every
 * door on the schema plane — `get` reads it from a loaded node and
 * `Materialize` reads it from payload bytes in hand, so the two cannot
 * come to disagree about what a stored revision means. Throws, and is
 * therefore always called inside the caller's own failure channel. */
export const fromEnvelope = (
  envelope: DecodedEnvelope,
): SchemaRepresentation.Document => {
  switch (envelope.revision) {
    case Revision:
      return documentFromJson(envelope.value)
    case LegacyRevision:
      return nativeDocument(legacySchema(envelope.value))
    default:
      return refuseBy("wrongRevision", "envelope", envelope.revision)
  }
}

/** A typed-reference declaration pinned to its expected resident kind tag. */
export const ref = (tag: number) => referenceRepresentation(Byte.make(tag))

/** Pin a runtime carrier to a canonical native representation snapshot. */
export const annotate = (
  identity: Schema.Top | SchemaRepresentation.Document,
) => <S extends Schema.Top>(schema: S) => {
  const document = documentOf(identity)
  const encoded = deepFreeze(SchemaRepresentation.toJson(document))
  return schema.annotate({ [AnnotationKey]: encoded })
}

/** Direct access to the native Effect AST denoted by the carrier's canonical
 * representation. A malformed carried snapshot fails closed as `None`. */
export const astOf = (schema: Schema.Top): Option.Option<SchemaAST.AST> =>
  Result.getSuccess(Result.try(() =>
    deepFreeze(fromRepresentation(representationOf(schema)).ast)
  ))

/** The envelope payload of a schema node. */
export const payloadOf = (
  identity: Schema.Top | SchemaRepresentation.Document,
): Uint8Array =>
  utf8Encoder.encode(canonicalJson({
    revision: Revision,
    value: SchemaRepresentation.toJson(documentOf(identity)),
  }))

/** The schema node itself: reserved kind, envelope payload, no references. */
export const nodeOf = (
  identity: Schema.Top | SchemaRepresentation.Document,
): CasNodeInput =>
  CasNodeInput.make({
    kind: { version: CasSchemeVersion, tag: KindTag },
    payload: payloadOf(identity),
    refs: [],
  })

/** The scheme-0 digest pre-image of a canonical schema. */
export const bytesOf = (
  identity: Schema.Top | SchemaRepresentation.Document,
): Uint8Array => encodeCasNode(nodeOf(identity))

/** The content address under an explicit address implementation. */
export const addressWith = (address: CasAddress) => (
  identity: Schema.Top | SchemaRepresentation.Document,
): Effect.Effect<ContentId, StoreFailure> =>
  address.digest(bytesOf(identity))

/** The canonical bytes declared by a carrying schema. Malformed annotations
 * fail closed as `None`. */
export const bytesFor = (schema: Schema.Top): Option.Option<Uint8Array> =>
  Result.getSuccess(Result.try(() => bytesOf(representationOf(schema))))

/** Admit a canonical schema into the store; its address is its name. */
export const put = (
  identity: Schema.Top | SchemaRepresentation.Document,
): Effect.Effect<ContentId, CasError, CasStore> =>
  CasStore.use((store) => store.put(nodeOf(identity)))

const projectionFailure = (
  id: ContentId,
  issue: unknown,
): ProjectionCodecFailure =>
  new ProjectionCodecFailure({
    direction: "decode",
    id,
    issue: String(issue),
  })

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Predicate.isObject(value) && !Array.isArray(value)

const exactRecord = (
  value: unknown,
  keys: ReadonlyArray<string>,
  context: string,
): Record<string, unknown> => {
  if (!isRecord(value)) throw new TypeError(`${context} must be an object`)
  const actual = Object.keys(value).toSorted()
  const expected = [...keys].toSorted()
  if (
    actual.length !== expected.length
    || actual.some((key, index) => key !== expected[index])
  ) {
    throw new TypeError(`${context} has unsupported or excess properties`)
  }
  return value
}

/** Strict revision-0 compatibility decoder. It maps legacy data directly to
 * Effect Schema and deliberately exposes no replacement public AST. */
const legacySchema = (value: unknown): Schema.Top => {
  if (!isRecord(value) || typeof value._tag !== "string") {
    throw new TypeError("legacy canonical schema must be a tagged object")
  }
  switch (value._tag) {
    case "Null":
      exactRecord(value, ["_tag"], "Null schema")
      return Schema.Null
    case "Boolean":
      exactRecord(value, ["_tag"], "Boolean schema")
      return Schema.Boolean
    case "Integer":
      exactRecord(value, ["_tag"], "Integer schema")
      return Schema.Int.check(Schema.isBetween({
        minimum: Number.MIN_SAFE_INTEGER,
        maximum: Number.MAX_SAFE_INTEGER,
      }))
    case "String":
      exactRecord(value, ["_tag"], "String schema")
      return Schema.String
    case "Literal": {
      const literal = exactRecord(value, ["_tag", "value"], "Literal schema")
      const item = literal.value
      if (
        item !== null
        && typeof item !== "boolean"
        && typeof item !== "string"
        && !(typeof item === "number" && Number.isSafeInteger(item))
      ) {
        throw new TypeError("legacy literal must be a canonical JSON scalar")
      }
      return item === null ? Schema.Null : Schema.Literal(item)
    }
    case "Array": {
      const array = exactRecord(value, ["_tag", "item"], "Array schema")
      return Schema.Array(legacySchema(array.item))
    }
    case "Struct": {
      const struct = exactRecord(value, ["_tag", "fields"], "Struct schema")
      if (!isRecord(struct.fields)) {
        throw new TypeError("Struct fields must be an object")
      }
      const fields: Record<string, Schema.Top | Schema.optionalKey<Schema.Top>> = {}
      for (const [name, rawField] of Object.entries(struct.fields)) {
        const field = exactRecord(
          rawField,
          ["optional", "schema"],
          `Struct field ${canonicalJson(name)}`,
        )
        if (typeof field.optional !== "boolean") {
          throw new TypeError(`Struct field ${canonicalJson(name)} optional must be boolean`)
        }
        const member = legacySchema(field.schema)
        fields[name] = field.optional ? Schema.optionalKey(member) : member
      }
      return Schema.Struct(fields)
    }
    case "Ref": {
      const reference = exactRecord(value, ["_tag", "tag"], "Ref schema")
      return ref(Schema.decodeUnknownSync(Byte)(reference.tag))
    }
    default:
      throw new TypeError(`unknown legacy canonical schema tag ${value._tag}`)
  }
}

/** THE ADDRESS DISCIPLINE: when is a reference name an EDGE?
 *
 * Exactly when it is a `ContentId` spelling, decided by `ContentId`'s
 * own decoder rather than by a second regular expression — one spelling
 * of an address on the host, and this reads it.
 *
 * The ruling that grew the carrier put the address discipline outside
 * `Ast.wf` deliberately: whether a table key RESOLVES is the door's and
 * the materializer's question, not the code's (PDD-3 packet, §The claim
 * scope). This is the materializer's half of that answer.
 *
 * Every other name is a plain table key — Effect allocates them from
 * `identifier` annotations and from its own `Objects_` counter, neither
 * of which can wander into 64 lowercase hex by accident. A name that
 * does is resolved as an address, and the estate claims nothing finer:
 * the spelling IS the discipline. */
export const referenceAddress = (name: string): Option.Option<ContentId> =>
  Result.getSuccess(
    Result.try(() => Schema.decodeSync(ContentId, strictOptions)(name)),
  )

/** Assemble a document's references table FROM STORE WORDS.
 *
 * PDD-3 taught both doors to admit a table; this is what resolves one.
 * Every address-named reference reachable from the document — through
 * the table as it grows, and through suspensions, because a delayed
 * reference is still reached — is loaded from the store, and the schema
 * node found there is bound under its own address name.
 *
 * Three things it is, each a law of `contracts/PDD-13.contract.md`:
 *
 * - **A TYPED EDGE, not an address.** A name that resolves to a node of
 *   another kind is `WrongKindReference`, carrying both tags — never
 *   `UnknownKind`, which is the name for a caller-supplied ROOT this
 *   runtime does not read. The precedent is the store's own admission
 *   law over annotation values (`Cas/Schema/Annotation.lean:76-80`).
 * - **An EXTENSION.** Bindings the presented document already carries
 *   are never rebound or dropped, and a name bound twice must be bound
 *   to the same code: two independently stored documents can each
 *   allocate `Objects_` for a different shape, and keeping one silently
 *   is a wrong answer with no error.
 * - **A READ.** Nothing is put, no address is minted, and the answer is
 *   a value in hand.
 *
 * The assembled document goes back through the DOOR before it is
 * answered, so guardedness is re-decided over the WHOLE table — a
 * strictly stronger question than the one each half answered alone, and
 * the reason two documents that are each guarded can fail to assemble.
 *
 * Termination is the visited set, not a fuel constant: each round
 * resolves at least one address and records it, the set of reachable
 * addresses is finite because the store is, and content addressing is
 * acyclic — a node's bytes cannot name the digest of themselves. There
 * is no honest constant here, and inventing one would refuse a
 * legitimate deep document. */
export const assemble: (
  document: SchemaRepresentation.Document,
) => Effect.Effect<SchemaRepresentation.Document, ProjectionError, CasLoader> =
  Effect.fn("CanonicalSchema.assemble")(
    function* (document: SchemaRepresentation.Document) {
      const json = SchemaRepresentation.toJson(document) as unknown as {
        readonly references: Record<string, Schema.Json>
        readonly representation: Schema.Json
      }
      const table: Record<string, Schema.Json> = { ...json.references }
      // Seeded with what the document already binds: those names are
      // the caller's, and extension means they are never re-read.
      const resolved = new Set<string>(Object.keys(json.references))
      const loader = yield* CasLoader

      const unresolved = (): ReadonlyArray<string> => {
        const reachable = new Set<string>(allRefs(json.representation))
        for (const code of Object.values(table)) {
          for (const name of allRefs(code)) reachable.add(name)
        }
        return [...reachable].filter((name) =>
          !resolved.has(name) && Option.isSome(referenceAddress(name))
        )
      }

      for (;;) {
        const round = unresolved()
        if (round.length === 0) break
        for (const name of round) {
          resolved.add(name)
          const id = Option.getOrThrow(referenceAddress(name))
          const node = yield* loader.load(id)
          if (node.kind.tag !== KindTag) {
            return yield* new WrongKindReference({
              ref: id,
              expectedTag: KindTag,
              actualTag: node.kind.tag,
            })
          }
          // The BYTES gate, ahead of the parser, exactly as `get` runs
          // it: assembly is a THIRD byte entry point, and a door that
          // skips this one would resolve a spelling the other two refuse
          // by name.
          yield* Effect.try({
            try: () => admitPayloadSpelling(node.payload),
            catch: (issue) => projectionFailure(id, issue),
          })
          const envelope = yield* decodedVersionedEnvelope(node.payload, id)
          const target = yield* Effect.try({
            try: () => fromEnvelope(envelope),
            catch: (issue) => projectionFailure(id, issue),
          })
          const targetJson = SchemaRepresentation.toJson(target) as unknown as {
            readonly references: Record<string, Schema.Json>
            readonly representation: Schema.Json
          }
          const bindings: ReadonlyArray<readonly [string, Schema.Json]> = [
            [name, targetJson.representation],
            ...Object.entries(targetJson.references),
          ]
          for (const [key, code] of bindings) {
            const seated = table[key]
            if (
              seated !== undefined
              && canonicalJson(seated) !== canonicalJson(code)
            ) {
              return yield* projectionFailure(
                id,
                `the assembled references table binds ${
                  canonicalJson(key)
                } to two different codes`,
              )
            }
            table[key] = code
          }
        }
      }

      // Back through the door: the table grew, so `WF` and guardedness
      // are decided again over what it grew into.
      return yield* Effect.try({
        try: () =>
          documentFromJson(
            { references: table, representation: json.representation } as
              Schema.Json,
          ),
        catch: (issue) =>
          new ProjectionCodecFailure({ direction: "decode", issue: String(issue) }),
      })
    },
  )

/** Load a canonical schema identity. Revision 1 returns Effect's persistent
 * representation; revision 0 is accepted and projected into that same form. */
export const get: (
  id: ContentId,
) => Effect.Effect<SchemaRepresentation.Document, ProjectionError, CasLoader> =
  Effect.fn("CanonicalSchema.get")(
    function* (id: ContentId) {
      const loader = yield* CasLoader
      const node = yield* loader.load(id)
      if (node.kind.tag !== KindTag) {
        return yield* new UnknownKind(node.kind)
      }
      if (node.refs.length > 0) {
        return yield* projectionFailure(id, "a schema node carries no references")
      }
      // The BYTES gate, ahead of the parser, so the load path and
      // `Materialize.fromPayload` refuse the same spellings by the same
      // names rather than being two doors.
      yield* Effect.try({
        try: () => admitPayloadSpelling(node.payload),
        catch: (issue) => projectionFailure(id, issue),
      })
      const envelope = yield* decodedVersionedEnvelope(node.payload, id)
      return yield* Effect.try({
        try: () => fromEnvelope(envelope),
        catch: (issue) => projectionFailure(id, issue),
      })
    },
  )
