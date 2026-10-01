import { Effect, Exit, Ref } from '/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js'
import { incr, eq } from '/Users/pooks/Dev/lean4-effect4/harness/truth/prelude.ts'

import { ProfileRefusal } from '/Users/pooks/Dev/lean4-effect4/harness/truth/session/clock.ts'
const checkedAdd = (a: number, b: number): number => {
  const result = a + b
  if (!Number.isSafeInteger(result)) throw new ProfileRefusal('outside profile')
  return result
}
const M = Number.MAX_SAFE_INTEGER
const body = Effect.flatMap(Effect.succeed(M), a => Effect.succeed(checkedAdd(a, 1)))
const report = (label: string, program: Effect.Effect<unknown, unknown>) => {
  const exit = Effect.runSyncExit(program)
  console.log(label, JSON.stringify(exit))
}
report('red: uncaught profile defect', body)
report('catchCause hides profile refusal', Effect.catchCause(body, _ => Effect.succeed(7)))
report('exit then discard hides profile refusal', Effect.flatMap(Effect.exit(body), _ => Effect.succeed(7)))
report('Ref updates bypass atoms and return safe bool', Effect.flatMap(Ref.make(M), r =>
  Effect.flatMap(Ref.updateAndGet(r, incr), a =>
    Effect.flatMap(Ref.updateAndGet(r, incr), b => Effect.succeed(eq(a, b))))))
console.log('exact Ref comparison', (BigInt(M) + 1n) === (BigInt(M) + 2n))

// These expressions are copied byte for byte from Lean printer output in ref-updates.log.
const add = checkedAdd
const printedRefProgram = Effect.flatMap(Ref.make(9007199254740991), (a0) => Effect.flatMap(Ref.updateAndGet(a0, incr), (a1) => Effect.flatMap(Ref.updateAndGet(a0, incr), (a2) => Effect.succeed(eq(a1, a2)))))
const printedCatchProgram = Effect.catchCause(Effect.flatMap(Effect.succeed(9007199254740991), (a0) => Effect.succeed(add(a0, 1))), (a0) => Effect.succeed(7))
report('exact printer Ref expression', printedRefProgram)
report('exact printer catchCause expression with T1 add', printedCatchProgram)
