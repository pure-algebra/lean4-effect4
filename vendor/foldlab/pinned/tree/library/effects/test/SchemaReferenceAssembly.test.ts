/**
 * The references table, assembled from store words — PDD-13 slice 4.
 *
 * Packet: `library/cas/contracts/PDD-13.contract.md`.
 *
 * PDD-3 taught both doors to ADMIT a document with a references table.
 * Nothing yet RESOLVES one: a reference whose name is a content address
 * arrives at the host and stops there. This suite is the battery for the
 * step that resolves it — `CanonicalSchema.assemble` — and for the two
 * printed consequences, the faithful `Suspend` and a source register
 * that no longer refuses a table.
 *
 * Every law it executes is stated in the packet; the test names below
 * are the packet's BATTERY lines verbatim, so a red test names the law
 * it kills rather than a symptom.
 *
 * The addressing is the DETERMINISTIC test address (content-keyed
 * sequential ids), because what is under test is the resolution of an
 * address, never the digest that produced it. Its ids are 64-hex, which
 * is exactly the spelling the address discipline reads.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Option, Schema, SchemaRepresentation } from "effect"
import { Cas } from "../src/index.ts"
import { CasStore, layerMemoryWith } from "../src/cas/Store.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const CS = Cas.CanonicalSchema
const M = Cas.Materialize
const layer = layerMemoryWith(deterministicAddress())

const utf8 = new TextEncoder()

/** One representation-JSON document, through the door. Written as JSON
 * rather than built from a live schema on purpose: a reference naming an
 * ADDRESS is not a shape any Effect schema constructs, so the only
 * honest way to present one is the spelling itself. */
const document = (
  references: Record<string, unknown>,
  representation: unknown,
): SchemaRepresentation.Document =>
  CS.fromJson({ references, representation } as Schema.Json)

/** The reference node, by name. */
const reference = (name: string) => ({ _tag: "Reference", $ref: name })

/** A struct with one required property of the given type. */
const struct = (property: string, type: unknown) => ({
  _tag: "Objects",
  checks: [],
  propertySignatures: [{
    name: { type: "string", value: property },
    type,
    isOptional: false,
    isMutable: false,
  }],
  indexSignatures: [],
})

const stringNode = { _tag: "String", checks: [] }

/** The anonymous linked list, exactly as Effect writes it — the shape
 * PDD-3 slice 1 pinned, and the fixture slice 5 registers. */
const linkedList = {
  references: {
    Objects_: struct("next", {
      _tag: "Suspend",
      checks: [],
      thunk: {
        _tag: "Union",
        checks: [],
        types: [reference("Objects_"), { _tag: "Null", checks: [] }],
        mode: "anyOf",
      },
    }),
  },
  representation: reference("Objects_"),
}

/** Admit one document as a schema node and answer its address. */
const putDocument = (
  references: Record<string, unknown>,
  representation: unknown,
) => CS.put(document(references, representation))

/** Admit raw envelope bytes under the schema kind, bypassing the
 * host door — the only way to put content the door would refuse, which
 * is what L4's witness needs. */
const putBytes = (json: string) =>
  Effect.gen(function* () {
    const store = yield* CasStore
    return yield* store.put({
      kind: { version: Cas.SchemeVersion, tag: CS.KindTag },
      payload: utf8.encode(json),
      refs: [],
    })
  })

/** The assembled table, as plain JSON. */
const tableOf = (
  assembled: SchemaRepresentation.Document,
): Record<string, unknown> =>
  (SchemaRepresentation.toJson(assembled) as unknown as {
    references: Record<string, unknown>
  }).references

// ---------------------------------------------------------------- L1

it("the address discipline is ContentId's own spelling and nothing else", () => {
  const address = "a".repeat(64)
  expect(Option.getOrThrow(CS.referenceAddress(address))).toBe(address)

  // Everything that is not exactly 64 lowercase hex is a plain table
  // name. Effect allocates `Objects_` and identifier annotations; none
  // of them can wander into the address spelling by accident.
  for (
    const name of [
      "Objects_",
      "Node",
      "",
      "a".repeat(63),
      "a".repeat(65),
      "A".repeat(64),
      `${"a".repeat(63)}g`,
      ` ${"a".repeat(64)}`,
    ]
  ) {
    expect(Option.isNone(CS.referenceAddress(name))).toBe(true)
  }
})

// ---------------------------------------------------------------- L2

it.effect("assembly closes over a chain of addresses, not just the first hop", () =>
  Effect.gen(function* () {
    // leaf <- mid <- root: a one-pass implementation binds `mid` and
    // stops, leaving `leaf` dangling. That is the witness.
    const leaf = yield* putDocument({}, struct("value", stringNode))
    const mid = yield* putDocument({}, struct("head", reference(leaf)))
    const assembled = yield* CS.assemble(document({}, reference(mid)))

    const table = tableOf(assembled)
    expect(Object.keys(table).toSorted()).toEqual([leaf, mid].toSorted())
    expect(table[leaf]).toEqual(struct("value", stringNode))
  }).pipe(Effect.provide(layer)))

it.effect("assembly leaves an existing table entry alone", () =>
  Effect.gen(function* () {
    const leaf = yield* putDocument({}, stringNode)
    const before = { Objects_: struct("next", reference("Objects_")) }
    // `Objects_` names itself under no Suspend, so it must ride under a
    // guard to be admitted at all — this one is guarded by the Suspend
    // the linked list carries.
    const guarded = { Objects_: linkedList.references.Objects_ }
    const assembled = yield* CS.assemble(
      document(guarded, struct("a", reference(leaf))),
    )
    const table = tableOf(assembled)
    expect(table["Objects_"]).toEqual(guarded.Objects_)
    expect(table["Objects_"]).not.toEqual(before.Objects_)
    expect(Object.hasOwn(table, leaf)).toBe(true)
  }).pipe(Effect.provide(layer)))

// ---------------------------------------------------------------- L3

it.effect("an address that resolves to another plane is WrongKindReference, with both tags", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const alien = yield* store.put({
      kind: { version: Cas.SchemeVersion, tag: 0x21 },
      payload: utf8.encode('{"revision":0,"value":null}'),
      refs: [],
    })
    const failure = yield* CS.assemble(document({}, reference(alien))).pipe(
      Effect.flip,
    )
    expect(failure._tag).toBe("CasError/WrongKindReference")
    expect(failure).toMatchObject({
      ref: alien,
      expectedTag: CS.KindTag,
      actualTag: 0x21,
    })
  }).pipe(Effect.provide(layer)))

// ---------------------------------------------------------------- L4

it.effect("a target the door refuses refuses the assembly", () =>
  Effect.gen(function* () {
    // An unguarded alias cycle, admitted to the store as bytes because
    // the host door would never let it in through `put`.
    const rotten = yield* putBytes(
      '{"revision":1,"value":{"references":{"A":{"$ref":"B","_tag":"Reference"},'
        + '"B":{"$ref":"A","_tag":"Reference"}},'
        + '"representation":{"$ref":"A","_tag":"Reference"}}}',
    )
    const failure = yield* CS.assemble(document({}, reference(rotten))).pipe(
      Effect.flip,
    )
    expect(failure._tag).toBe("ProjectionCodecFailure")
    expect(String((failure as { issue?: string }).issue))
      .toContain("unguardedCycle")
  }).pipe(Effect.provide(layer)))

it.effect("assembly re-decides guardedness over the whole table", () =>
  Effect.gen(function* () {
    // Each half is GUARDED alone: `A` names `B`, which is dangling, so
    // `A` has no outgoing edge inside its own document, and likewise for
    // `B`. Assembled, the two halves close an unguarded cycle. An
    // implementation that trusts the door's earlier answers instead of
    // re-deciding over the assembled table admits it.
    const left = yield* putDocument({ A: reference("B") }, reference("A"))
    const right = yield* putDocument({ B: reference("A") }, reference("B"))
    const failure = yield* CS.assemble(
      document(
        {},
        {
          _tag: "Union",
          checks: [],
          types: [reference(left), reference(right)],
          mode: "anyOf",
        },
      ),
    ).pipe(Effect.flip)
    expect(failure._tag).toBe("ProjectionCodecFailure")
    expect(String((failure as { issue?: string }).issue))
      .toContain("unguardedCycle")
  }).pipe(Effect.provide(layer)))

// ---------------------------------------------------------------- L5

it.effect("one name, two codes, no answer", () =>
  Effect.gen(function* () {
    // Two independently stored documents, each allocating `Objects_` for
    // a different shape. Last-writer-wins is a wrong answer with no
    // error, which is precisely what this law refuses.
    const left = yield* putDocument(
      { Objects_: struct("l", stringNode) },
      reference("Objects_"),
    )
    const right = yield* putDocument(
      { Objects_: struct("r", stringNode) },
      reference("Objects_"),
    )
    const failure = yield* CS.assemble(
      document(
        {},
        {
          _tag: "Union",
          checks: [],
          types: [reference(left), reference(right)],
          mode: "anyOf",
        },
      ),
    ).pipe(Effect.flip)
    expect(failure._tag).toBe("ProjectionCodecFailure")
    expect(String((failure as { issue?: string }).issue)).toContain("Objects_")
  }).pipe(Effect.provide(layer)))

// ---------------------------------------------------------------- L7

it.effect("a target that names an address already resolved halts", () =>
  Effect.gen(function* () {
    // The diamond: root reaches `shared` twice, once directly and once
    // through `mid`. A resolver with no visited set re-resolves it; one
    // that re-resolves and re-binds trips L5's collision check on a name
    // that is bound to itself. Both are defects this witness catches.
    const shared = yield* putDocument({}, stringNode)
    const mid = yield* putDocument({}, struct("s", reference(shared)))
    const assembled = yield* CS.assemble(
      document(
        {},
        {
          _tag: "Union",
          checks: [],
          types: [reference(mid), reference(shared)],
          mode: "anyOf",
        },
      ),
    )
    expect(Object.keys(tableOf(assembled)).toSorted())
      .toEqual([mid, shared].toSorted())
  }).pipe(Effect.provide(layer)))

// ---------------------------------------------------------------- L8

it.effect("a recursive binding declares its table above the export", () =>
  Effect.gen(function* () {
    const address = yield* CS.put(
      document(linkedList.references, linkedList.representation),
    )
    const materialized = yield* M.fromStore(address)
    const text = M.source([{ ...materialized, name: "anonymousList" }])

    const declaration = text.indexOf("const Objects_ =")
    const exported = text.indexOf("export const anonymousList =")
    expect(declaration).toBeGreaterThan(-1)
    expect(exported).toBeGreaterThan(declaration)
    expect(text).toContain("export const anonymousList = Objects_")
  }).pipe(Effect.provide(layer)))

it.effect("the table's own eager reads are declared before them", () =>
  Effect.gen(function* () {
    // The break this law was restated under. Revived and re-lowered —
    // which is the path `source` actually takes — the linked list has a
    // THREE-entry table, and the PLAIN entry `Objects_` reads the CYCLIC
    // entry `Suspend_` eagerly:
    //   const Objects_ = Schema.Struct({ "next": Suspend_ })
    // Effect's topological sort skips that edge (it sorts only among the
    // plain entries), so an emitter that declares the plain entries
    // first prints a module that throws a temporal-dead-zone
    // ReferenceError on load. Every entry the table reads eagerly must
    // stand above the entry that reads it.
    const address = yield* CS.put(
      document(linkedList.references, linkedList.representation),
    )
    const materialized = yield* M.fromStore(address)
    const text = M.source([{ ...materialized, name: "anonymousList" }])

    const eager = text.indexOf("const Objects_ = ")
    const read = text.indexOf("const Suspend_ = ")
    expect(read).toBeGreaterThan(-1)
    expect(eager).toBeGreaterThan(-1)
    expect(text).toContain(`{ "next": Suspend_ }`)
    expect(read).toBeLessThan(eager)
  }).pipe(Effect.provide(layer)))

it.effect("the printed table carries Effect's own Schema.suspend", () =>
  Effect.gen(function* () {
    const address = yield* CS.put(
      document(linkedList.references, linkedList.representation),
    )
    const materialized = yield* M.fromStore(address)
    const text = M.source([{ ...materialized, name: "anonymousList" }])
    expect(text).toContain("Schema.suspend(")
  }).pipe(Effect.provide(layer)))
