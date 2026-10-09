/** Independent finite helper observations on Effect 4.0.1.
 * These controls establish no general source-to-target simulation. */
import { expect, test } from "bun:test"
import { Cause, Effect, Exit, Ref } from "effect"
import { ifCase } from "./control.ts"

test("condition, selected construction and selected effect wait for execution", () => {
  for (const selected of [true, false]) {
    const calls = { condition: 0, trueConstruct: 0, falseConstruct: 0, trueRun: 0, falseRun: 0 }
    const program = ifCase(
      () => { calls.condition++; return selected },
      () => { calls.trueConstruct++; return Effect.sync(() => { calls.trueRun++; return 11 }) },
      () => { calls.falseConstruct++; return Effect.sync(() => { calls.falseRun++; return 22 }) },
    )
    expect(calls).toEqual({ condition: 0, trueConstruct: 0, falseConstruct: 0, trueRun: 0, falseRun: 0 })
    expect(Effect.runSync(program)).toBe(selected ? 11 : 22)
    expect(calls).toEqual({ condition: 1, trueConstruct: selected ? 1 : 0,
      falseConstruct: selected ? 0 : 1, trueRun: selected ? 1 : 0, falseRun: selected ? 0 : 1 })
  }
})

test("each run reevaluates the condition and constructs only that run's selected arm", () => {
  let selected = true
  const calls: string[] = []
  const program = ifCase(
    () => { calls.push("condition"); return selected },
    () => { calls.push("true"); return Effect.succeed(11) },
    () => { calls.push("false"); return Effect.succeed(22) },
  )
  expect(calls).toEqual([])
  expect(Effect.runSync(program)).toBe(11)
  selected = false
  expect(Effect.runSync(program)).toBe(22)
  expect(calls).toEqual(["condition", "true", "condition", "false"])
})

test("an unselected poisoned constructor never runs", () => {
  for (const selected of [true, false]) {
    const poison = (): Effect.Effect<number> => { throw new Error("unselected constructor") }
    const good = () => Effect.succeed(7)
    const program = ifCase(() => selected, selected ? good : poison, selected ? poison : good)
    expect(Effect.runSync(program)).toBe(7)
  }
})

test("selected combined failures retain the selected writes and the entire cause", () => {
  const cause = Cause.combine(Cause.fail("selected"), Cause.die("defect"))
  for (const selected of [true, false]) {
    const observed = Effect.runSync(Effect.gen(function* () {
      const cell = yield* Ref.make(0)
      const failing = () => Effect.andThen(Ref.set(cell, 7), Effect.failCause(cause))
      const unselected = () => Effect.andThen(Ref.set(cell, 99), Effect.succeed(99))
      const exit = yield* Effect.exit(ifCase(() => selected,
        selected ? failing : unselected, selected ? unselected : failing))
      const state = yield* Ref.get(cell)
      return { exit, state }
    }))
    expect(observed.exit).toEqual(Exit.failCause(cause))
    expect(observed.state).toBe(7)
  }
})
