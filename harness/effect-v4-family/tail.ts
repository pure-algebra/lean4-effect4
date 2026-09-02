import { Effect, Layer, Ref } from "effect"
import { Cell, incr } from "./fixture.ts"

/** `Cell.Service (StateT number Id)` as a layer owning a `Ref`; the Lean receipt is `cellLive`. */
const CellLive = (initial: number): Layer.Layer<Cell> =>
  Layer.effect(Cell, Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    return { get: Ref.get(ref), put: (n: number) => Ref.set(ref, n) }
  }))

const result = await Effect.runPromise(incr(0).pipe(Effect.provide(CellLive(41))))
if (result !== 42) throw new Error(`expected 42, got ${result}`)
console.log(`incr(0) from cell 41 gives ${result}, matching the Lean receipt (42, 42)`)
