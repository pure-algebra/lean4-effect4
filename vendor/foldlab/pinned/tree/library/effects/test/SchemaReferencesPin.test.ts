/**
 * The references-and-recursion spelling pin — PDD-3 slice 1.
 *
 * Packet: `library/cas/contracts/PDD-3.contract.md`.
 *
 * The plan marks the revision-1 spellings for `Suspend`, `Reference`
 * and the `references` table PENDING-VERIFICATION
 * (CORE-ABSTRACTIONS-PLAN.md:127-134) and rules that nothing is written
 * in Lean until they are pinned. This suite is that pin.
 *
 * It EXECUTES the pinned dependency rather than transcribing its
 * source, so every row below is an observation of
 * `effect@4.0.0-rc.112` (provenance row `effect-runtime`,
 * `.reference/provenance/sources.lock.json`) and moves the day the
 * dependency moves. That is the point: a hand-copied key list is a
 * claim, and this file is evidence.
 *
 * Two families of fact are pinned:
 *
 *   1. WHAT EFFECT WRITES — the exact key sets of the two recursion
 *      nodes and the document envelope, taken off real schemas.
 *   2. WHAT EFFECT DOES NOT CHECK — dangling names, alias cycles,
 *      unguarded cycles and dead table entries all survive Effect's
 *      own codec, so each is the estate door's question and not
 *      somebody else's.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Schema, SchemaRepresentation } from "effect"

/** One schema, lowered to the revision-1 JSON document. */
const documentOf = (schema: Schema.Top): {
  readonly representation: Record<string, unknown>
  readonly references: Record<string, Record<string, unknown>>
} =>
  SchemaRepresentation.toJson(
    SchemaRepresentation.toRepresentation(schema.ast),
  ) as never

/** A node's key set, sorted — the estate compares key SETS, never order. */
const keysOf = (node: unknown): ReadonlyArray<string> =>
  Object.keys(node as Record<string, unknown>).sort()

/** Every node in a document, depth first, including table entries. */
const nodesOf = (value: unknown): ReadonlyArray<Record<string, unknown>> => {
  const out: Array<Record<string, unknown>> = []
  const walk = (v: unknown): void => {
    if (Array.isArray(v)) {
      for (const item of v) walk(item)
      return
    }
    if (typeof v !== "object" || v === null) return
    const node = v as Record<string, unknown>
    if (typeof node["_tag"] === "string") out.push(node)
    for (const child of Object.values(node)) walk(child)
  }
  walk(value)
  return out
}

/** The nodes of a document carrying one `_tag`. */
const taggedNodes = (
  document: unknown,
  tag: string,
): ReadonlyArray<Record<string, unknown>> =>
  nodesOf(document).filter((node) => node["_tag"] === tag)

/** Does Effect's own codec read this document back? */
const readsBack = (json: unknown): boolean => {
  try {
    SchemaRepresentation.fromJson(json as never)
    return true
  } catch {
    return false
  }
}

/**
 * A directly recursive struct with no identifier annotation — the
 * linked-list shape the plan's slice-5 fixture calls for.
 */
interface AnonymousNode {
  readonly value: string
  readonly next: AnonymousNode | null
}
const AnonymousNode = Schema.Struct({
  value: Schema.String,
  next: Schema.suspend((): Schema.Codec<AnonymousNode | null> =>
    Schema.NullOr(AnonymousNode) as unknown as Schema.Codec<AnonymousNode | null>
  ),
})

/** The same shape, named — the annotated-name half of the ruling. */
const NamedNode = AnonymousNode.annotate({ identifier: "Node" })

/** A shared NON-recursive named schema, used twice. */
const SharedName = Schema.String.annotate({ identifier: "Name" })
const PairOfNames = Schema.Struct({ l: SharedName, r: SharedName })

/** A `Suspend` with nothing recursive under it. */
const LazyString = Schema.suspend((): Schema.Codec<string> => Schema.String)

const stringNode = { _tag: "String", checks: [] }

it.effect("a Reference is exactly _tag and $ref — no checks, no annotations", () =>
  Effect.sync(() => {
    const document = documentOf(AnonymousNode)
    const references = taggedNodes(document, "Reference")
    expect(references.length).toBeGreaterThan(0)
    for (const node of references) {
      expect(keysOf(node)).toEqual(["$ref", "_tag"])
      expect(typeof node["$ref"]).toBe("string")
      expect(node["$ref"]).not.toBe("")
    }
  }))

it.effect("a Suspend is _tag, an always-empty checks, and an INLINE thunk", () =>
  Effect.sync(() => {
    const document = documentOf(AnonymousNode)
    const suspends = taggedNodes(document, "Suspend")
    expect(suspends.length).toBeGreaterThan(0)
    for (const node of suspends) {
      expect(keysOf(node)).toEqual(["_tag", "checks", "thunk"])
      // `checks` is typed `Schema.Tuple([])`: a Suspend can never
      // carry a check, so the estate's checksNotEmpty clause is
      // structurally satisfied on this node.
      expect(node["checks"]).toEqual([])
      // The thunk is a NESTED REPRESENTATION, not a name. This is the
      // fact the packet's Block turns on.
      expect(typeof (node["thunk"] as Record<string, unknown>)["_tag"])
        .toBe("string")
    }
  }))

it.effect("a Suspend carrying a check is refused by Effect itself", () =>
  Effect.sync(() => {
    expect(readsBack({
      representation: {
        _tag: "Suspend",
        checks: [{ _tag: "Filter", aborted: false }],
        thunk: stringNode,
      },
      references: {},
    })).toBe(false)
  }))

it.effect("the document is exactly representation and references", () =>
  Effect.sync(() => {
    expect(keysOf(documentOf(AnonymousNode))).toEqual([
      "references",
      "representation",
    ])
  }))

it.effect("a recursive schema's document carries BOTH node families", () =>
  Effect.sync(() => {
    // The load-bearing observation: recursion is not spelled by one
    // node. The edge is a Reference; the guard is a Suspend; a real
    // recursive document contains both, so a carrier with one
    // constructor cannot decode it.
    for (const schema of [AnonymousNode, NamedNode]) {
      const document = documentOf(schema)
      expect(taggedNodes(document, "Reference").length).toBeGreaterThan(0)
      expect(taggedNodes(document, "Suspend").length).toBeGreaterThan(0)
    }
  }))

it.effect("the anonymous linked list is Reference at the root, Suspend at the knot", () =>
  Effect.sync(() => {
    const document = documentOf(AnonymousNode)
    expect(document.representation["_tag"]).toBe("Reference")
    const name = document.representation["$ref"] as string
    expect(Object.keys(document.references)).toEqual([name])
    // The recursive knot is a Suspend whose thunk reaches the table
    // entry again — the cycle passes THROUGH the guard.
    const entry = document.references[name]!
    const suspends = taggedNodes(entry, "Suspend")
    expect(suspends.length).toBe(1)
    expect(taggedNodes(suspends[0]!["thunk"], "Reference")
      .map((node) => node["$ref"])).toEqual([name])
  }))

it.effect("a Suspend with nothing recursive under it needs no table at all", () =>
  Effect.sync(() => {
    const document = documentOf(LazyString)
    expect(document.representation["_tag"]).toBe("Suspend")
    expect(document.references).toEqual({})
  }))

it.effect("a NON-recursive shared name allocates a table entry", () =>
  Effect.sync(() => {
    // So "the references table is non-empty" does NOT mean "the schema
    // is recursive". The door cannot read one off the other.
    const document = documentOf(PairOfNames)
    expect(Object.keys(document.references)).toEqual(["Name"])
    expect(taggedNodes(document, "Suspend")).toEqual([])
    expect(taggedNodes(document, "Reference").map((node) => node["$ref"]))
      .toEqual(["Name", "Name"])
  }))

it.effect("a named recursive entry carries an annotations bag", () =>
  Effect.sync(() => {
    // The divergence already recorded at Admission.lean:52-62 and owned
    // by SM-21, met here: a recursive fixture with an identifier will
    // arrive with a bag the Lean spelling does not carry.
    const entry = documentOf(NamedNode).references["Node"]!
    expect(entry["annotations"]).toEqual({ identifier: "Node" })
  }))

it.effect("Effect checks none of the four cycle hazards", () =>
  Effect.sync(() => {
    const reference = (name: string) => ({ _tag: "Reference", $ref: name })
    const fieldOf = (type: unknown) => ({
      _tag: "Objects",
      checks: [],
      indexSignatures: [],
      propertySignatures: [{
        name: { type: "string", value: "next" },
        type,
        isOptional: false,
        isMutable: false,
      }],
    })

    // A name with no table entry.
    expect(readsBack({ representation: reference("Nope"), references: {} }))
      .toBe(true)
    // A self alias: resolving it never reaches a node.
    expect(readsBack({
      representation: reference("A"),
      references: { A: reference("A") },
    })).toBe(true)
    // A two-step alias cycle, likewise.
    expect(readsBack({
      representation: reference("A"),
      references: { A: reference("B"), B: reference("A") },
    })).toBe(true)
    // A structural cycle with NO Suspend on the path.
    expect(readsBack({
      representation: reference("A"),
      references: { A: fieldOf(reference("A")) },
    })).toBe(true)
    // A dead table entry nothing points at.
    expect(readsBack({ representation: stringNode, references: { Dead: stringNode } }))
      .toBe(true)
  }))

it.effect("an empty $ref is refused by Effect itself", () =>
  Effect.sync(() => {
    // `$ref` is NonEmptyString while the table KEY type is plain
    // String, so the nonemptiness the plan asks of the carrier is
    // Effect's own constraint on the pointer, not on the key.
    expect(readsBack({
      representation: { _tag: "Reference", $ref: "" },
      references: { "": stringNode },
    })).toBe(false)
  }))

it.effect("the recursive document survives Effect's own round trip", () =>
  Effect.sync(() => {
    for (const schema of [AnonymousNode, NamedNode, PairOfNames, LazyString]) {
      const json = documentOf(schema)
      const back = SchemaRepresentation.toJson(
        SchemaRepresentation.fromJson(json as never),
      )
      expect(JSON.stringify(back)).toBe(JSON.stringify(json))
    }
  }))
