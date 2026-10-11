import { expect, test } from "bun:test"
import { readPrintedSource as ck } from "../ck.ts"
import { readPrintedSource as oxc } from "../oxc.ts"
import { effJson } from "../../json.gen.ts"

for (const read of [ck, oxc]) {
  test("first-exit source reader keeps a separate action and entrant order", () => {
    expect(effJson(read('Effect.raceAllFirst([Effect.fail("first"), Effect.succeed(2)])'))).toEqual(
      ["withFiber", ["raceAllFirst", ["cons", ["fail", ["lit", ["str", "first"]]], ["cons", ["succeed", ["lit", ["nat", 2]]], ["nil"]]]]])
    expect(effJson(read("Effect.raceAll([Effect.succeed(2)])"))).toEqual(
      ["withFiber", ["raceAll", ["cons", ["succeed", ["lit", ["nat", 2]]], ["nil"]]]])
  })
  test("first-exit source reader refuses a non-array or wrong arity", () => {
    expect(() => read("Effect.raceAllFirst(Effect.succeed(2))")).toThrow()
    expect(() => read("Effect.raceAllFirst([], [])")).toThrow()
  })
}
