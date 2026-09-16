import { expect, test } from "bun:test"
import { resolve } from "node:path"
import * as Effect from "../../ts/eff/node_modules/effect/dist/Effect.js"
import { pair, tagIs } from "../../harness/truth/prelude.ts"
import { query, type Query } from "./oracle.ts"

type AssertFalse<T extends false> = T
// A user-declared refinement must not choose catchIf's narrower overload.
export type TagIsIsBoolean = AssertFalse<typeof tagIs extends
  (tag: string, value: unknown) => value is readonly [string, unknown] ? true : false>

type Tagged = readonly ["A", "m"] | readonly ["B", "m"]
const body: Effect.Effect<number, Tagged> = Effect.fail(pair("A", "m"))
export const caught = Effect.catchIf(body, value => tagIs("A", value), () => Effect.succeed(1), undefined)
export const ordinaryData = Effect.succeed(tagIs("A", pair("A", 7)))

test("Boolean tag tests retain the host error bound and work as ordinary data", () => {
  const repo = resolve(import.meta.dir, "../.."), source = "tools/target/prelude.test.ts"
  const imports = [`import type * as C from ${JSON.stringify(resolve(repo, source))}`]
  const queries: Query[] = [
    { id: "tag/catch", source, imports, subject: "typeof C.caught", kind: "program",
      expected: { A: "number", E: 'readonly ["A", "m"] | readonly ["B", "m"]', R: "never" } },
    { id: "tag/data", source, imports, subject: "typeof C.ordinaryData", kind: "program",
      expected: { A: "boolean", E: "never", R: "never" } },
  ]
  const report = query(repo, queries)
  expect(report.conforms).toBe(true)
  expect(report.observations[0]?.columns.E?.agreement).toBe("exact")
  expect(Effect.runSync(caught)).toBe(1)
  expect(Effect.runSync(ordinaryData)).toBe(true)
  for (const [value, expected] of [[["A", 7], true], [["B", 7], false], ["A", false],
    [7, false], [["A"], false], [["A", 7, 8], false]] as const) {
    expect(tagIs("A", value)).toBe(expected)
  }
}, 30_000)
