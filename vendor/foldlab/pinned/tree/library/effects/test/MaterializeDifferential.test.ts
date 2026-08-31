/**
 * P6's differential: two independent generators, one denotation.
 *
 * Every registered canonical-schema fixture is materialized twice, from
 * the same committed Lean-emitted payload bytes, by two printers that
 * share no code:
 *
 * - the ESTATE register — `lake exe materialize` reads the payload back
 *   through the ingestion door (`Cas.Schema.ingestBytes`) and prints the
 *   recovered code with the estate's own lowering
 *   (`Cas/Backend/EmitAst.lean`) under
 *   `test/generated/materialized/estate/`;
 * - the EFFECT register — `Cas.Materialize.source` revives the same
 *   bytes and prints them with Effect's own
 *   `SchemaRepresentation.toCodeDocument`, committed by
 *   `bun scripts/gen-materialized.ts` under
 *   `test/generated/materialized/effect/`.
 *
 * **The comparison is never on source text.** The two printers
 * legitimately differ in spelling — the estate always writes a union's
 * mode and never collapses, Effect elides its default and collapses bare
 * literals; one writes `Schema.Int`, the other writes the checked
 * `Schema.Number` that `Schema.Int` is. Both modules are IMPORTED, and
 * the schemas they evaluate to are compared structurally, closures
 * quotiented (`fixtures/astEquality.ts`). The denotation is the
 * identity.
 *
 * The identity is then held at the address, which is stronger than AST
 * equality and is the estate's own currency: each evaluated schema is
 * re-lowered to canonical payload bytes and admitted to a store, and the
 * answer must be the address `schemas/addresses.json` pins. The estate
 * register closes that loop for every fixture. The Effect register does
 * not, and the one place it fails is the KNOWN DISAGREEMENT below.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, type Schema } from "effect"
import { Cas } from "../src/index.ts"
import { astDifferences } from "./fixtures/astEquality.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"
import {
  bindingName,
  effectRegisterIndex,
  effectRegisterModule,
  registeredNames,
} from "./fixtures/materialized.ts"
import { registry } from "./fixtures/schemaRegistry.ts"
import * as EstateRegister from "./generated/materialized/estate/index.ts"
import * as EffectRegister from "./generated/materialized/effect/index.ts"

const CS = Cas.CanonicalSchema
const layer = Layer.mergeAll(Cas.layerMemoryLive, layerDiskFs)

/** The two barrels, read as what they are: a binding name to the schema
 * that binding evaluates to. */
const estate = EstateRegister as unknown as Record<string, Schema.Top>
const effect = EffectRegister as unknown as Record<string, Schema.Top>

/**
 * THE KNOWN DISAGREEMENT, pinned rather than worked around — the live
 * consequence of ruling-queue item 13.
 *
 * `union-pin`'s `exact` field is a `oneOf` union of two bare string
 * literals. Effect's `toCodeDocument` collapses an all-bare-literal
 * union to `Schema.Literals([…])` (`toCodeDocument.ts:559-566`), and
 * `Literals` has no mode slot, so the generated source means `anyOf`.
 * The estate's printer spells every mode and collapses nothing, so its
 * module means `oneOf` — which is what the stored bytes say.
 *
 * The two registers therefore differ at exactly one datum, and it is a
 * datum the estate treats as identity: `exact`'s mode. Nothing else in
 * the corpus disagrees.
 */
const knownDisagreements: Readonly<Record<string, ReadonlyArray<string>>> = {
  "union-pin": [
    "union-pin.propertySignatures.1.type.mode: oneOf vs anyOf",
  ],
}

/** The committed store addresses, name for name. */
const committedAddresses = readFixtureString("../cas/schemas/addresses.json")
  .pipe(
    Effect.orDie,
    Effect.map((text) =>
      new Map(
        (JSON.parse(text) as {
          schemas: ReadonlyArray<{ name: string; address: string }>
        }).schemas.map((row) => [row.name, row.address] as const),
      )
    ),
  )

/** The address a live schema lands at: re-lowered to canonical payload
 * bytes and admitted through the store's own door. */
const addressOf = (schema: Schema.Top) => CS.put(schema)

it.effect("both registers export exactly the registered fixtures", () =>
  Effect.gen(function* () {
    const names = yield* registeredNames
    const expected = names.map(bindingName)

    // The Lean registry, the committed manifest, and the hand-written
    // TypeScript mirror registry are one list — which is what makes
    // "every fixture" below mean every fixture.
    expect(names).toEqual(registry.map(([name]) => name))
    expect(Object.keys(estate).toSorted()).toEqual(expected.toSorted())
    expect(Object.keys(effect).toSorted()).toEqual(expected.toSorted())
  }).pipe(Effect.provide(layer)))

it.effect("the two registers evaluate to one schema, the known disagreement aside", () =>
  Effect.gen(function* () {
    const names = yield* registeredNames
    const found = new Map<string, ReadonlyArray<string>>()
    for (const name of names) {
      const binding = bindingName(name)
      const differences = astDifferences(
        estate[binding]!.ast,
        effect[binding]!.ast,
        name,
      )
      if (differences.length > 0) found.set(name, differences)
    }
    expect(Object.fromEntries(found)).toEqual(knownDisagreements)
  }).pipe(Effect.provide(layer)))

it.effect("the estate register round-trips to the pinned address, every fixture", () =>
  Effect.gen(function* () {
    const committed = yield* committedAddresses
    const names = yield* registeredNames
    for (const name of names) {
      // bytes → ingest → estate source → evaluated schema → bytes: the
      // loop closes on the address the store answers, so the estate
      // printer loses nothing the identity depends on.
      const address = yield* addressOf(estate[bindingName(name)]!)
      expect(`${name} ${address}`).toBe(`${name} ${committed.get(name)}`)
    }
  }).pipe(Effect.provide(layer)))

it.effect("the Effect register round-trips to the pinned address everywhere the literal collapse does not fire", () =>
  Effect.gen(function* () {
    const committed = yield* committedAddresses
    const names = yield* registeredNames
    const drifted: Array<string> = []
    for (const name of names) {
      const address = yield* addressOf(effect[bindingName(name)]!)
      if (address !== committed.get(name)) drifted.push(name)
    }
    // The loss of item 13, weighed in the estate's own currency: the
    // module Effect's printer generates for `union-pin` is a schema at a
    // DIFFERENT ADDRESS than the node it was materialized from. Every
    // other fixture regenerates faithfully.
    expect(drifted).toEqual(["union-pin"])
  }).pipe(Effect.provide(layer)))

it.effect("the committed Effect-register snapshots are what Materialize.source prints", () =>
  Effect.gen(function* () {
    const names = yield* registeredNames
    for (const name of names) {
      const rendered = yield* effectRegisterModule(name)
      const committed = yield* readFixtureString(
        `test/generated/materialized/effect/${name}.ts`,
      ).pipe(Effect.orDie)
      expect(`${name}\n${committed}`).toBe(`${name}\n${rendered}`)
    }
    const barrel = yield* readFixtureString(
      "test/generated/materialized/effect/index.ts",
    ).pipe(Effect.orDie)
    expect(barrel).toBe(effectRegisterIndex(names))
  }).pipe(Effect.provide(layer)))

it.effect("both registers decide the same values, mode collapse included", () =>
  Effect.gen(function* () {
    // The disagreement is one of IDENTITY, not of decision: `exact`'s
    // members are disjoint literals, so no candidate can match more than
    // one and `oneOf` and `anyOf` accept the same set. Stated here so
    // the pin above is not misread as a validator defect.
    const candidates: ReadonlyArray<unknown> = [
      { choice: 3, exact: "alpha", nested: ["a", "b"] },
      { choice: true, exact: "zebra" },
      { choice: "x", exact: "gamma" },
      { choice: {}, exact: "zebra" },
      { choice: "x", exact: "zebra", surplus: 1 },
    ]
    const decide = (schema: Schema.Top) => (input: unknown) =>
      Effect.exit(Cas.Materialize.validator({
        address: Cas.ContentId.make("00".repeat(32)),
        schema,
      })(input)).pipe(Effect.map((exit) => exit._tag))

    for (const candidate of candidates) {
      expect(yield* decide(estate.unionPin!)(candidate))
        .toBe(yield* decide(effect.unionPin!)(candidate))
    }
  }).pipe(Effect.provide(layer)))
