/**
 * The cross-host run gate — the store language's hello world.
 *
 * `test/generated/VectorPrograms.ts` holds straight-line Effect
 * programs lowered from the SAME grammar terms the conformance
 * vectors are seeded from (`lake exe emitprograms`). Each program
 * re-performs its term's puts against the real store, computing every
 * address through THIS host's digest — nothing is replayed from given
 * addresses. The gate: the answered addresses equal the Lean-computed
 * word's addresses, binding for binding, duplicates included. Same
 * program, both hosts, identical words or red (EFFECTS-BACKEND R5).
 */
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { Cas } from "../src/index.ts"
import { loadVectors } from "./fixtures/vectors.ts"
import { programs } from "./generated/VectorPrograms.ts"

const { Store, layerMemoryLive } = Cas

it.effect("every generated program reproduces its vector's word live", () =>
  Effect.gen(function* () {
    const { vectors } = yield* loadVectors
    expect(programs.length).toBe(vectors.length)
    for (const program of programs) {
      const vector = vectors.find((v) => v.name === program.name)
      expect(`${program.name} registered`).toBe(
        vector === undefined ? `${program.name} missing` : `${program.name} registered`,
      )
      if (vector === undefined) continue
      const store = yield* Store
      const answered = yield* program.run(store)
      expect(`${program.name} ${answered.length}`).toBe(
        `${program.name} ${vector.word.length}`,
      )
      for (const [position, binding] of vector.word.entries()) {
        expect(`${program.name}[${position}] ${answered[position]}`)
          .toBe(`${program.name}[${position}] ${binding.address}`)
      }
    }
  }).pipe(Effect.provide(layerMemoryLive)))
