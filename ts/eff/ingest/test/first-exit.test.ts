import { expect, test } from "bun:test"
import { readPrintedSource as ck } from "../ck.ts"
import { readPrintedSource as oxc } from "../oxc.ts"
import { effJson } from "../../json.gen.ts"

for (const read of [ck, oxc]) {
  test("first-exit source reader keeps a separate action and entrant order", () => {
    const two = { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 2 } } }
    expect(effJson(read('Effect.raceAllFirst([Effect.fail("first"), Effect.succeed(2)])'))).toEqual({
      _tag: "withFiber", action: { _tag: "raceAllFirst", entrants: [
        { _tag: "fail", error: { _tag: "lit", value: { _tag: "str", value: "first" } } }, two] } })
    expect(effJson(read("Effect.raceAll([Effect.succeed(2)])"))).toEqual(
      { _tag: "withFiber", action: { _tag: "raceAll", entrants: [two] } })
  })
  test("first-exit source reader refuses a non-array or wrong arity", () => {
    expect(() => read("Effect.raceAllFirst(Effect.succeed(2))")).toThrow()
    expect(() => read("Effect.raceAllFirst([], [])")).toThrow()
  })
}
