import { expect, test } from "bun:test"
import { resolve } from "node:path"
import * as Effect from "../../ts/eff/node_modules/effect/dist/Effect.js"
import * as Option from "../../ts/eff/node_modules/effect/dist/Option.js"
import { atomNames } from "../../ts/eff/profile.gen.ts"
import { getOrElse, isSome, pair, selfTestCases, tagIs } from "../../ts/prelude/prelude.ts"
import { query, type Query } from "./oracle.ts"

// The prelude's table of fixed cases (`selfTestCases`, `ts/prelude/prelude.ts`) runs here, in the
// target lane (owner, 2026-10-20). It refuses as the deleted truth runner's `selfTest` refused
// (`git:8e93a284f:harness/truth/run-truth.ts`): a case whose answer is not its expected value,
// and an atom of the profile (`atomNames`, `ts/eff/profile.gen.ts`) that no case exercises.
type Case = (typeof selfTestCases)[number]
const failures = (cases: ReadonlyArray<Case>): string[] => cases.flatMap(({ name, apply, expected }) => {
  const got = apply()
  return got === expected ? [] : [`${name}: got ${JSON.stringify(got)}, wanted ${JSON.stringify(expected)}`]
})
const uncovered = (atoms: Iterable<string>, cases: ReadonlyArray<{ readonly atom: string }>): string[] => {
  const covered = new Set(cases.map(c => c.atom))
  return [...atoms].filter(atom => !covered.has(atom))
}

test("every case of the prelude's self-test table holds, and every atom of the profile has one", () => {
  expect(selfTestCases.length).toBeGreaterThan(0)
  expect(failures(selfTestCases)).toEqual([])
  expect(uncovered(atomNames, selfTestCases)).toEqual([])
})

test("the self-test's controls: a wrong answer and an atom with no case are each refused by name", () => {
  // `succ` answering `n + 2`: its case is refused, and no other
  const at = selfTestCases.findIndex(c => c.name === "succ 41")
  expect(at).toBeGreaterThanOrEqual(0)
  const mutated = selfTestCases.map((c, i) => i === at ? { ...c, apply: () => 41 + 2 } : c)
  expect(failures(mutated)).toEqual(["succ 41: got 43, wanted 42"])
  // each atom without its cases is reported, alone
  for (const atom of atomNames) expect(uncovered(atomNames, selfTestCases.filter(c => c.atom !== atom))).toEqual([atom])
  // an unrelated case does not cover an atom the profile adds
  expect(uncovered([...atomNames, "omittedControl"], selfTestCases)).toEqual(["omittedControl"])
})

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

type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends
  (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type IsSomeIsBoolean = AssertFalse<typeof isSome extends
  (value: Option.Option<unknown>) => value is Option.Some<unknown> ? true : false>

// These calls are compiled but never executed. The answer of `getOrElse` is the join of the
// payload's type and the fallback's type (decisions row 303), and the first argument is an
// option. A refinement predicate makes a required negative diagnostic disappear, and the type
// check fails.
export function optionTypeControls(value: Option.Option<number | string>, empty: Option.Option<never>,
    count: number, text: string) {
  const result = getOrElse(value, 0)
  type SamePayload = Assert<Equal<typeof result, number | string>>
  const unit = getOrElse(Option.some(undefined), undefined)
  type Unit = Assert<Equal<typeof unit, undefined>>
  const joined = getOrElse(Option.some(count), text)
  type Joined = Assert<Equal<typeof joined, number | string>>
  const fromEmpty = getOrElse(empty, count)
  type FromEmpty = Assert<Equal<typeof fromEmpty, number>>
  // @ts-expect-error The first argument is an option.
  getOrElse(1, 0)
  if (isSome(value)) {
    // @ts-expect-error Presence testing is Boolean, not a payload-elimination rule.
    value.value
  }
  return { result, unit }
}

test("option defaults preserve nested payloads, unit, and object identity", () => {
  const absent = Option.none<number>()
  const nested = Option.some<Option.Option<number>>(absent)
  expect(getOrElse(nested, Option.some(9))).toBe(absent)
  expect(getOrElse(Option.some(undefined), undefined)).toBeUndefined()
  const handle = { resource: "allocated" }, fallback = { resource: "fallback" }
  expect(getOrElse(Option.some(handle), fallback)).toBe(handle)
  expect(getOrElse(Option.none<typeof handle>(), fallback)).toBe(fallback)
  expect(isSome(Option.some(undefined))).toBe(true)
  expect(isSome(absent)).toBe(false)
})
