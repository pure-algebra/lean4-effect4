/**
 * The Context-key-set differential — G6-a's acceptance.
 *
 * `library/cas/tools/EmitLayers.lean` carries an authored service
 * topology as content at the system kind; `Cas/Backend/EmitLayer.lean`
 * folds it into a key set and a requirement set and prints
 * `test/generated/EmittedLayers.ts`. This suite BUILDS each emitted
 * layer through Effect and asserts the Context it actually produces
 * holds exactly the keys the topology declared.
 *
 * The two sides are independent: one is the Lean fold over the stored
 * description, the other is Effect running the emitted wiring. Nothing
 * here compares source text.
 *
 * This gate certifies the KEY SET and nothing more — not acquisition
 * order, not residuals below the surface, not how many instances of a
 * shared child exist. That is stated in the generated module's own
 * header too, and it is the first acceptance in this package weaker
 * than byte identity.
 */
import { describe, expect, it } from "@effect/vitest"
import { Context, Effect, Layer } from "effect"
import { topology } from "./generated/EmittedLayers.ts"

/**
 * `Layer.buildWithMemoMap` adds its own memo map to every context it
 * answers (`Context.add(CurrentMemoMap, memoMap)`), so this key is
 * present in every build regardless of what the topology wires. It is
 * Effect's build machinery, not a service the description names, and
 * the assertion below both removes it AND requires it — so the day
 * Effect stops adding it, this suite says so instead of quietly
 * widening.
 */
const buildMachineryKey = "effect/Layer/CurrentMemoMap"

/**
 * `Layer.Layer<in ROut, out E, out RIn>` is CONTRAVARIANT in what it
 * provides, so `Layer.Layer<never>` is the top of the family: every
 * emitted layer is assignable to it, and the table's heterogeneous
 * union passes through one parameter without a cast. Requiring
 * `RIn = never` is what restricts the gate to the layers that can be
 * built with nothing provided.
 */
const builtKeys = (
  layer: Layer.Layer<never, never, never>,
): Effect.Effect<ReadonlyArray<string>> =>
  Effect.scoped(
    Layer.build(layer).pipe(
      Effect.map((context: Context.Context<never>) =>
        [...context.mapUnsafe.keys()].toSorted()
      ),
    ),
  )

describe("the emitted topology", () => {
  it("declares at least one layer", () => {
    expect(topology.length).toBeGreaterThan(0)
  })

  it("names every layer exactly once", () => {
    const names = topology.map((entry) => entry.name)
    expect(new Set(names).size).toBe(names.length)
  })

  for (const entry of topology) {
    it.effect(
      `${entry.name} builds a Context with exactly the declared keys`,
      () =>
        Effect.gen(function* () {
          const keys = yield* builtKeys(entry.layer)
          expect(keys).toContain(buildMachineryKey)
          expect(keys.filter((key) => key !== buildMachineryKey)).toEqual(
            entry.keys.toSorted(),
          )
        }),
    )
  }
})
