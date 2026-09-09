import { expect, test } from "bun:test"
import { readPrintedSource } from "../ck.ts"

test("the compiler reader recovers the original printed program", () => {
  expect(readPrintedSource("Effect.succeed(12)")).toEqual({ _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 12 } } })
})

test("printed service identifiers are preserved by the separate printer entrypoint", () => {
  expect(readPrintedSource('Effect.service(Context.Service<number>("k10_4"))')).toEqual({ _tag: "service", key: { name: { value: 10 }, service: { value: 4 } } })
})
