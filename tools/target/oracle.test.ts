import { expect, test } from "bun:test"
import { resolve } from "node:path"
import { query, type Query } from "./oracle.ts"

const repo = resolve(import.meta.dir, "../..")
const source = "Test/fixtures/target/controls.ts"
const fixture = `import type * as C from ${JSON.stringify(resolve(repo, source))}`
const base: Query = { id: "control/positive", source, imports: [fixture], subject: "typeof C.program", kind: "effect",
  expected: { A: "number", E: '"E1"', R: "C.R1" } }

test("synthetic assignments compare all three independent Effect columns", () => {
  const report = query(repo, [base,
    { ...base, id: "control/answer", expected: { ...base.expected, A: "string" } },
    { ...base, id: "control/error", expected: { ...base.expected, E: '"E2"' } },
    { ...base, id: "control/requirement", expected: { ...base.expected, R: "C.R2" } },
    { ...base, id: "control/void-answer", subject: "typeof C.unitProgram", expected: { A: "number", E: "never", R: "never" } },
  ])
  expect(report.observations[0]?.status).toBe("agree")
  for (const [index, axis] of [[1, "A"], [2, "E"], [3, "R"], [4, "A"]] as const) {
    expect(report.observations[index]?.status).toBe("mismatch")
    expect(report.observations[index]?.columns[axis]?.actualToExpected).toBe(false)
  }
  expect(report.conforms).toBe(false)
})

test("request, receiver, optional and rest parameters are independently compared", () => {
  const method: Query = { ...base, id: "method/positive", subject: "typeof C.method", kind: "function", receiver: "C.Receiver1",
    expected: { ...base.expected, request: "[text: string, count?: number | undefined, ...rest: boolean[]]", receiver: "C.Receiver1" } }
  const report = query(repo, [method,
    { ...method, id: "method/request", expected: { ...method.expected, request: "[number, number?, ...boolean[]]" } },
    { ...method, id: "method/receiver", expected: { ...method.expected, receiver: "C.Receiver2" } },
    { ...method, id: "method/required", expected: { ...method.expected, request: "[string, number, ...boolean[]]" } },
    { ...method, id: "method/rest", expected: { ...method.expected, request: "[string, number?, ...string[]]" } },
  ])
  expect(report.observations[0]?.status).toBe("agree")
  expect(report.observations[0]?.signatures[0]?.parameters.map(p => [p.optional, p.rest])).toEqual([[false, false], [true, false], [false, true]])
  for (const [index, axis] of [[1, "request"], [2, "receiver"], [3, "request"], [4, "request"]] as const) {
    expect(report.observations[index]?.status).toBe("mismatch")
    expect(report.observations[index]?.columns[axis]?.actualToExpected).toBe(false)
    expect(report.observations[index]?.columns.A?.actualToExpected).toBe(true)
  }
})

test("unresolved types, absent metadata and unsupported signatures are refusals", () => {
  const report = query(repo, [
    { ...base, id: "missing/module", source: ["Test", "fixtures", "target", "absent.ts"].join("/"), imports: ['import type * as C from "./not-present.ts"'] },
    { ...base, id: "missing/symbol", expected: { ...base.expected, A: "Host.Resource" } },
    { ...base, id: "missing/metadata", expected: { A: "number", E: '"E1"' } },
    { ...base, id: "unsafe/any", subject: "typeof C.anyProgram", expected: { A: "number", E: "never", R: "never" } },
    { ...base, id: "unsafe/nested-any", subject: "typeof C.nestedAnyProgram", expected: { A: "{values: ReadonlyArray<number>}", E: "never", R: "never" } },
    { ...base, id: "unsafe/unknown", subject: "typeof C.unknownProgram", expected: { A: "unknown", E: "never", R: "never" } },
    { ...base, id: "explicit/unknown", subject: "typeof C.unknownProgram", expected: { A: "unknown", E: "never", R: "never" }, allowUnknown: ["A"] },
    { ...base, id: "method/overloaded", subject: "typeof C.overloaded", kind: "function", expected: { A: "number", E: "never", R: "never", request: "[number]" } },
    { ...base, id: "method/generic", subject: "typeof C.generic", kind: "function", expected: { A: "number", E: "never", R: "never", request: "[number]" } },
  ])
  for (const [index, code] of [[0, "missing-source"], [1, "query-diagnostic"], [2, "missing-type-metadata"], [3, "unresolved-any"], [4, "unresolved-any"], [5, "unresolved-unknown"], [7, "unsupported-overloads"], [8, "unsupported-generic-signature"]] as const) {
    expect(report.observations[index]?.status).toBe("refused")
    expect(report.observations[index]?.issues.some(i => i.code === code)).toBe(true)
  }
  expect(report.observations[6]?.status).toBe("agree")
  expect(report.observations[7]?.signatures).toHaveLength(2)
  expect(report.conforms).toBe(false)
  expect(report.expected).toHaveLength(9)
  expect(report.attempted).toEqual(report.expected)
})

test("all diagnostics count and repeated reports are stable", () => {
  const unboundImport: Query = { ...base, id: "missing/unrelated-import", imports: [...base.imports, 'import type * as Missing from "unavailable-package"'] }
  const first = query(repo, [base, unboundImport])
  expect(first.observations[0]?.status).toBe("agree")
  expect(first.observations[1]?.status).toBe("refused")
  expect(first.observations[1]?.diagnostics.some(d => d.code === 2307)).toBe(true)
  expect(query(repo, [base, unboundImport])).toEqual(first)
  expect(() => query(repo, [base, base])).toThrow("duplicate")
  expect(() => query(repo, [])).toThrow("empty")
})


test("non-Effect and never subjects cannot agree through never-valued extraction helpers", () => {
  const report = query(repo, ["notEffect", "neverSubject"].map(name => ({ ...base, id: `invalid/${name}`, subject: `typeof C.${name}`, expected: { A: "never", E: "never", R: "never" } })))
  expect(report.conforms).toBe(false)
  for (const observation of report.observations) {
    expect(observation.status).toBe("refused")
    expect(observation.issues.some(i => i.code === "query-diagnostic")).toBe(true)
  }
})

test("E4-CATCH-CE-001: an explicit absent fallback selects the data-first overload", () => {
  const input = (kind: "bad" | "good"): Query => {
    const source = `Test/fixtures/target/catch-if-predicate-${kind}.ts`
    return { id: `catch-if/${kind}`, source,
      imports: [`import type * as C from ${JSON.stringify(resolve(repo, source))}`],
      subject: "typeof C.program", kind: "effect", expected: { A: "number", E: "never", R: "never" } }
  }
  const bad = query(repo, [input("bad")])
  expect(bad.conforms).toBe(false)
  expect(bad.globalDiagnostics.some(d => d.code === 2769)).toBe(true)
  const good = query(repo, [input("good")])
  expect(good.conforms).toBe(true)
  expect(good.observations[0]?.status).toBe("agree")
})
