import { expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
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
}, 30_000)

test("program errors may be strictly contained while other contracts stay exact", () => {
  const program: Query = { ...base, kind: "program" }
  const wider = { ...base.expected, E: '"E1" | "E2"' }
  const report = query(repo, [
    { ...program, id: "program/exact" },
    { ...program, id: "program/contained", expected: wider },
    { ...program, id: "program/reversed", subject: 'Effect.Effect<number, "E1" | "E2", C.R1>' },
    { ...program, id: "program/answer", subject: 'Effect.Effect<1, "E1", C.R1>' },
    { ...program, id: "program/requirements", expected: { ...base.expected, R: "C.R1 | C.R2" } },
    { ...base, id: "primitive/effect", expected: wider },
    { ...base, id: "primitive/function", kind: "function", subject: "typeof C.method",
      expected: { ...wider, request: "[string, number?, ...boolean[]]" } },
    { ...program, id: "program/reply-payload", subject: 'Effect.Effect<{ readonly failed: "E1" }, never, never>',
      expected: { A: '{ readonly failed: "E1" | "E2" }', E: "never", R: "never" } },
  ])
  const [exact, contained, reversed] = report.observations
  expect(exact?.columns.E?.agreement).toBe("exact")
  expect(contained?.status).toBe("agree")
  expect(contained?.binding.kind).toBe("program")
  expect(contained?.columns.E).toMatchObject({ actualToExpected: true, expectedToActual: false, agreement: "strict-containment" })
  expect(contained?.diagnostics.map(d => d.code)).toEqual([2322])
  expect(reversed?.columns.E).toMatchObject({ actualToExpected: false, expectedToActual: true, agreement: "mismatch" })
  for (const observation of report.observations.slice(2)) expect(observation.status).toBe("mismatch")
  const positive = query(repo, [
    { ...program, expected: wider },
    { ...program, id: "program/no-errors", subject: "Effect.Effect<number, never, C.R1>" },
  ])
  expect(positive.conforms).toBe(true)
  expect(positive.observations[1]?.columns.E?.agreement).toBe("strict-containment")
  expect(report.conforms).toBe(false)
}, 30_000)

test("program containment cannot accept unresolved error bounds or failed extraction", () => {
  const program: Query = { ...base, kind: "program", expected: { ...base.expected, E: '"E1" | "E2"' } }
  const badSource = "Test/fixtures/target/catch-if-predicate-bad.ts"
  const report = query(repo, [
    { ...program, id: "program/missing-error", expected: { A: "number", R: "C.R1" } },
    { ...program, id: "program/any-actual", subject: "Effect.Effect<number, any, C.R1>" },
    { ...program, id: "program/any-bound", expected: { ...program.expected, E: "any" } },
    { ...program, id: "program/unknown-actual", subject: "Effect.Effect<number, unknown, C.R1>" },
    { ...program, id: "program/unknown-bound", expected: { ...program.expected, E: "unknown" } },
    { ...program, id: "program/missing-binding", expected: { ...program.expected, E: "Missing.Error" } },
    { ...program, id: "program/never-subject", subject: "typeof C.neverSubject", expected: { A: "never", E: "never", R: "never" } },
    { ...program, id: "program/non-effect", subject: "typeof C.notEffect", expected: { A: "never", E: "never", R: "never" } },
    { ...program, id: "program/compiler-diagnostic", source: badSource,
      imports: [`import type * as C from ${JSON.stringify(resolve(repo, badSource))}`],
      expected: { A: "number", E: "string", R: "never" } },
  ])
  const codes = ["missing-type-metadata", "unresolved-any", "unresolved-any", "unresolved-unknown",
    "unresolved-unknown", "query-diagnostic", "query-diagnostic", "query-diagnostic", "source-diagnostic"]
  report.observations.forEach((observation, index) => {
    expect(observation.status).toBe("refused")
    expect(observation.issues.some(issue => issue.code === codes[index])).toBe(true)
  })
  expect(report.conforms).toBe(false)
}, 30_000)

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
}, 30_000)

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
}, 30_000)

test("all diagnostics count and repeated reports are stable", () => {
  const unboundImport: Query = { ...base, id: "missing/unrelated-import", imports: [...base.imports, 'import type * as Missing from "unavailable-package"'] }
  const first = query(repo, [base, unboundImport])
  expect(first.observations[0]?.status).toBe("agree")
  expect(first.observations[1]?.status).toBe("refused")
  expect(first.observations[1]?.diagnostics.some(d => d.code === 2307)).toBe(true)
  expect(query(repo, [base, unboundImport])).toEqual(first)
  expect(() => query(repo, [base, base])).toThrow("duplicate")
  expect(() => query(repo, [])).toThrow("empty")
}, 30_000)


test("non-Effect and never subjects cannot agree through never-valued extraction helpers", () => {
  const report = query(repo, ["notEffect", "neverSubject"].map(name => ({ ...base, id: `invalid/${name}`, subject: `typeof C.${name}`, expected: { A: "never", E: "never", R: "never" } })))
  expect(report.conforms).toBe(false)
  for (const observation of report.observations) {
    expect(observation.status).toBe("refused")
    expect(observation.issues.some(i => i.code === "query-diagnostic")).toBe(true)
  }
}, 30_000)

test("one compiler: no second checker is constructed anywhere in the tree (row 57)", () => {
  // The ruling is about what answers a typing question, not about what parses. `typescript` is
  // pinned as a parser for the recognizer twin; the moment anything asks it for a program or a
  // checker there are two meanings of "assignable" again, and this control goes red.
  const constructors = ["createProgram", "getTypeChecker", "transpileModule",
    "createIncrementalProgram", "createWatchProgram", "createSemanticDiagnosticsBuilderProgram"]
  const found = spawnSync("git", ["grep", "-nE", `(${constructors.join("|")})[[:space:]]*\\(`,
    "--", "*.ts", "*.mts", "*.mjs", ":!vendor", ":!*/node_modules/*"], { cwd: repo, encoding: "utf8" })
  const hits = found.stdout.split("\n").filter(line => line.trim().length)
  expect(found.status === 0 || found.status === 1).toBe(true)
  expect(hits).toEqual([])
}, 30_000)

test("E4-CATCH-CE-001: an explicit absent fallback selects the data-first overload", () => {
  const input = (kind: "bad" | "good"): Query => {
    const source = `Test/fixtures/target/catch-if-predicate-${kind}.ts`
    return { id: `catch-if/${kind}`, source,
      imports: [`import type * as C from ${JSON.stringify(resolve(repo, source))}`],
      subject: "typeof C.program", kind: "effect", expected: { A: "number", E: "never", R: "never" } }
  }
  const report = query(repo, [input("bad"), input("good")])
  expect(report.conforms).toBe(false)
  // A diagnostic inside the queried source refuses that query by name (`source-diagnostic`),
  // and is not a global diagnostic: since the corpus lane, one module that does not type
  // must not refuse every other query of the same program.
  expect(report.globalDiagnostics).toHaveLength(0)
  expect(report.observations[0]?.status).toBe("refused")
  expect(report.observations[0]?.issues.some(i => i.code === "source-diagnostic" && i.message.includes("TS2769"))).toBe(true)
  expect(report.observations[1]?.status).toBe("agree")
}, 30_000)
