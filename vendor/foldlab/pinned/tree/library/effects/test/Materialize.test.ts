/**
 * The materializer door — both registers, on the committed fixtures.
 *
 * Every materialization here starts from the Lean-emitted bytes in
 * `library/cas/schemas/`, either fetched from a store they were admitted
 * to or handed over as payload bytes; nothing constructs a schema by
 * hand and calls it materialized. The suite holds three things:
 *
 * - the SOURCE register renders a stable module — frame, stamp,
 *   imports, and declarations — and the stamp is DERIVED, so the
 *   addresses it prints are the ones `addresses.json` pins;
 * - the VALIDATOR register decides real instances of the union pin and
 *   the annotation kind, accepting the conforming one and refusing the
 *   non-conforming one;
 * - the two doors (`fromStore`, `fromPayload`) answer one
 *   materialization for one node.
 *
 * The addressing here is the live scheme-0 SHA-256 (`layerMemoryLive`),
 * not the deterministic test address, because the address stamp is
 * exactly what is under test.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, Schema, SchemaRepresentation } from "effect"
import { Cas } from "../src/index.ts"
import { CasStore } from "../src/cas/Store.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureBytes, readFixtureString } from "./fixtures/read.ts"
import { registry } from "./fixtures/schemaRegistry.ts"

const CS = Cas.CanonicalSchema
const M = Cas.Materialize
const layer = Layer.mergeAll(Cas.layerMemoryLive, layerDiskFs)

/** The fixture name as a TypeScript binding name. */
const binding = (name: string): string =>
  name.split("-").map((word, index) =>
    index === 0 ? word : `${word[0]!.toUpperCase()}${word.slice(1)}`
  ).join("")

/** Admit one committed fixture as a schema node and materialize it back
 * out through the store — storage, not a constructor. */
const materializeFixture = (name: string) =>
  Effect.gen(function* () {
    const payload = yield* readFixtureBytes(`../cas/schemas/${name}.json`).pipe(
      Effect.orDie,
    )
    const store = yield* CasStore
    const address = yield* store.put({
      kind: { tag: CS.KindTag, version: Cas.SchemeVersion },
      payload,
      refs: [],
    })
    return yield* M.fromStore(address)
  })

const committedAddresses = readFixtureString("../cas/schemas/addresses.json").pipe(
  Effect.orDie,
  Effect.map((text) =>
    (JSON.parse(text) as {
      schemas: ReadonlyArray<{ name: string; address: string }>
    }).schemas
  ),
)

it.effect("materialized source is a stable snapshot, frame and stamp included", () =>
  Effect.gen(function* () {
    const literalPin = yield* materializeFixture("literal-pin")
    const unionPin = yield* materializeFixture("union-pin")
    const text = M.source([
      { ...literalPin, name: "literalPin" },
      { ...unionPin, name: "unionPin" },
    ])
    expect(text).toBe(`/**
 * GENERATED — do not edit. Materialized from canonical schema nodes
 * by \`Cas.Materialize.source\`: every binding below is what Effect's
 * own \`SchemaRepresentation.toCodeDocument\` prints for the schema
 * revived out of the addressed node. The addresses are the stamp
 * that makes this file a projection of store content and parity a
 * digest check (R7, the served-equals-derived wall) — regenerate,
 * never edit.
 *
 * Materialized from schema nodes (kind tag 0x53):
 *   - literalPin — 5461f66ed3a0eeade4cd058d438d24c86c32b28ce1756b4af8297434103f0c04
 *   - unionPin — 98e36f2243f0269fc3165110660f7b8f08a43aaffc450be7b87ca1f4f6005819
 */
import { Schema } from "effect"

export const literalPin = Schema.Struct({ "a": Schema.Null, "b": Schema.Literal(true), "c": Schema.optionalKey(Schema.Literal(-7)), "d": Schema.Literal("pinned") })

export type literalPin = { readonly "a": null, readonly "b": true, readonly "c"?: -7, readonly "d": "pinned" }

export const unionPin = Schema.Struct({ "choice": Schema.Union([Schema.String, Schema.Boolean, Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" }))]), "exact": Schema.Literals(["zebra", "alpha"]), "nested": Schema.optionalKey(Schema.Union([Schema.Null, Schema.Union([Schema.Array(Schema.String), Schema.Boolean], { mode: "oneOf" })])) })

export type unionPin = { readonly "choice": string | boolean | number, readonly "exact": "zebra" | "alpha", readonly "nested"?: null | ReadonlyArray<string> | boolean }
`)
  }).pipe(Effect.provide(layer)))

it.effect("every committed fixture's stamp is the address addresses.json pins", () =>
  Effect.gen(function* () {
    const committed = yield* committedAddresses
    const bindings = yield* Effect.forEach(registry, ([name]) =>
      materializeFixture(name).pipe(Effect.map((materialized) => ({
        ...materialized,
        name: binding(name),
      }))))

    for (const [index, [name]] of registry.entries()) {
      const pinned = committed.find((entry) => entry.name === name)
      expect(`${name} ${bindings[index]!.address}`)
        .toBe(`${name} ${pinned?.address}`)
    }

    // The stamp in the rendered header is the same address, spelled
    // where a reader of the generated file will find it.
    const text = M.source(bindings)
    for (const [index, [name]] of registry.entries()) {
      expect(text).toContain(
        ` *   - ${binding(name)} — ${committed.find((e) => e.name === name)!.address}`,
      )
      expect(text).toContain(`export const ${binding(name)} = Schema.`)
      expect(text).toContain(`export type ${binding(name)} = `)
      expect(bindings[index]!.name).toBe(binding(name))
    }

    // The declaration's own import rides along exactly once, alongside
    // the one import every generated module needs.
    expect(text.split("\n").filter((line) => line.startsWith("import "))).toEqual([
      `import { Schema } from "effect"`,
      `import { Cas } from "@foldlab/cas"`,
    ])
    // Deterministic: the same materializations render the same bytes.
    expect(M.source(bindings)).toBe(text)
  }).pipe(Effect.provide(layer)))

it.effect("the validator register accepts a conforming union-pin instance and refuses a non-conforming one", () =>
  Effect.gen(function* () {
    const validate = M.validator(yield* materializeFixture("union-pin"))

    expect(yield* validate({ choice: 3, exact: "alpha", nested: ["a", "b"] }))
      .toEqual({ choice: 3, exact: "alpha", nested: ["a", "b"] })
    // `nested` is optionalKey: absent is conforming.
    expect(yield* validate({ choice: true, exact: "zebra" }))
      .toEqual({ choice: true, exact: "zebra" })

    // Not a member of `exact`'s literal union.
    expect(yield* Effect.exit(validate({ choice: "x", exact: "gamma" })))
      .toMatchObject({ _tag: "Failure" })
    // Not a member of `choice`'s union.
    expect(yield* Effect.exit(validate({ choice: {}, exact: "zebra" })))
      .toMatchObject({ _tag: "Failure" })
    // Excess property: strict by default on the CAS plane.
    expect(yield* Effect.exit(
      validate({ choice: "x", exact: "zebra", surplus: 1 }),
    )).toMatchObject({ _tag: "Failure" })
  }).pipe(Effect.provide(layer)))

it.effect("the validator register decides the annotation kind's typed reference", () =>
  Effect.gen(function* () {
    const validate = M.validator(yield* materializeFixture("annotation"))
    const subject = "7f".repeat(32)

    // The subject is a union over the addressable planes now, so an arm
    // carries the reference and the arm's tag is what the edge admits.
    // The schema arm admits 0x53.
    expect(yield* validate({
      key: "title",
      subject: { _tag: "schema", address: { $link: { id: subject, tag: 0x53 } } },
      value: { _tag: "text", text: "the union pin" },
    })).toEqual({
      key: "title",
      subject: { _tag: "schema", address: subject },
      value: { _tag: "text", text: "the union pin" },
    })

    // The system arm admits 0x54 — the plane the NAME SEAT rides, and
    // the one the monomorphic subject could not spell at all.
    expect(yield* validate({
      key: "foldlab/name",
      subject: { _tag: "system", address: { $link: { id: subject, tag: 0x54 } } },
      value: { _tag: "text", text: "casSystem" },
    })).toEqual({
      key: "foldlab/name",
      subject: { _tag: "system", address: subject },
      value: { _tag: "text", text: "casSystem" },
    })

    // The value's `ref` arm is a typed reference too — where hex text
    // used to sit, and refused on the same law.
    expect(yield* validate({
      key: "foldlab/view",
      subject: { _tag: "program", address: { $link: { id: subject, tag: 0x0f } } },
      value: {
        _tag: "ref",
        address: { _tag: "system", address: { $link: { id: subject, tag: 0x54 } } },
      },
    })).toEqual({
      key: "foldlab/view",
      subject: { _tag: "program", address: subject },
      value: { _tag: "ref", address: { _tag: "system", address: subject } },
    })

    // A reference to some other kind is refused by the codec itself:
    // widening the union added planes, it did not weaken the edge.
    expect(yield* Effect.exit(validate({
      key: "title",
      subject: { _tag: "schema", address: { $link: { id: subject, tag: 9 } } },
      value: { _tag: "text", text: "the union pin" },
    }))).toMatchObject({ _tag: "Failure" })
    // An arm's tag belongs to the arm: 0x54 under the schema arm is not
    // the same edge as 0x54 under the system arm.
    expect(yield* Effect.exit(validate({
      key: "title",
      subject: { _tag: "schema", address: { $link: { id: subject, tag: 0x54 } } },
      value: { _tag: "text", text: "the union pin" },
    }))).toMatchObject({ _tag: "Failure" })
    // A plane the estate does not have is not an arm.
    expect(yield* Effect.exit(validate({
      key: "title",
      subject: {
        _tag: "projection",
        address: { $link: { id: subject, tag: 0x53 } },
      },
      value: { _tag: "text", text: "the union pin" },
    }))).toMatchObject({ _tag: "Failure" })
    // A bare address is not a reference, and an untagged subject is not
    // an arm — both spellings of the shape this ruling replaced.
    expect(yield* Effect.exit(validate({
      key: "title",
      subject,
      value: { _tag: "text", text: "the union pin" },
    }))).toMatchObject({ _tag: "Failure" })
    // A bare string is no longer a value: that is the whole promotion.
    expect(yield* Effect.exit(validate({
      key: "title",
      subject: { _tag: "schema", address: { $link: { id: subject, tag: 0x53 } } },
      value: "the union pin",
    }))).toMatchObject({ _tag: "Failure" })
  }).pipe(Effect.provide(layer)))

it.effect("the payload door and the store door answer one materialization", () =>
  Effect.gen(function* () {
    for (const [name] of registry) {
      const payload = yield* readFixtureBytes(`../cas/schemas/${name}.json`).pipe(
        Effect.orDie,
      )
      const fromPayload = yield* M.fromPayload(payload)
      const fromStore = yield* materializeFixture(name)
      // The derived address and the store's verified id agree, and both
      // revive to one identity.
      expect(`${name} ${fromPayload.address}`).toBe(`${name} ${fromStore.address}`)
      expect(`${name} ${M.source([{ ...fromPayload, name: binding(name) }])}`)
        .toBe(`${name} ${M.source([{ ...fromStore, name: binding(name) }])}`)
    }
  }).pipe(Effect.provide(layer)))

it.effect("the source register fails closed on a name it cannot export", () =>
  Effect.gen(function* () {
    const materialized = yield* materializeFixture("literal-pin")
    expect(() => M.source([{ ...materialized, name: "literal-pin" }]))
      .toThrow(/is not a TypeScript identifier/)
    expect(() =>
      M.source([
        { ...materialized, name: "same" },
        { ...materialized, name: "same" },
      ])
    ).toThrow(/is declared twice/)
    expect(M.source([])).toContain("Materialized from schema nodes")
  }).pipe(Effect.provide(layer)))

it.effect("both registers run on a revived schema, which is why they run at all", () =>
  Effect.gen(function* () {
    // The Slice A constraint, stated where it bites: `toCode` is a
    // function-valued annotation and does not survive persistence, so
    // generation off the stored document throws — and every door here
    // hands back a REVIVED schema, which is why the same generation
    // succeeds one line later.
    const payload = yield* readFixtureBytes("../cas/schemas/pin-sample.json").pipe(
      Effect.orDie,
    )
    const stored = CS.fromJson(
      (JSON.parse(new TextDecoder().decode(payload)) as { value: Schema.Json })
        .value,
    )
    expect(() =>
      SchemaRepresentation.toCodeDocument({
        references: stored.references,
        representations: [stored.representation],
      })
    ).toThrow(/Missing toCode callback/)

    // Same bytes, through the door: the materialization is a live
    // schema, and generation succeeds on it.
    const materialized = yield* M.fromPayload(payload)
    expect(Schema.isSchema(materialized.schema)).toBe(true)
    expect(M.source([{ ...materialized, name: "pinSample" }]))
      .toContain("export const pinSample = Schema.Struct(")
    // And the validator register runs off the same materialization.
    expect(yield* M.validator(materialized)({
      count: 1,
      flag: true,
      items: ["a"],
      label: "l",
      root: { $link: { id: "ab".repeat(32), tag: 9 } },
      unit: null,
    })).toMatchObject({ label: "l" })
  }).pipe(Effect.provide(layer)))
