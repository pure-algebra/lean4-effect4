import { Effect, Ref } from "effect"

// The prelude's own declarations of the two atoms (src/Effect4/Machine/Term.lean, `NativeAtom.row`).
const inProfile = (n: number): number => n
export const succ = (n: number): number => inProfile(n + 1)
export const minus = (a: number, b: number): number => inProfile(a - b)

// cell = Ref.make(succ(4)); Ref.set(cell, minus(0, 1)); Ref.get(cell)
export const program = Effect.gen(function* () {
  const cell = yield* Ref.make(succ(4))
  yield* Ref.set(cell, minus(0, 1))
  return yield* Ref.get(cell)
})
