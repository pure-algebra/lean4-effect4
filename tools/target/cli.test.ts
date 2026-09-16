import { expect, test } from "bun:test"
import { mkdtempSync, readFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, resolve } from "node:path"
import { decodeQueries } from "./input.ts"

const repo = resolve(import.meta.dir, "../..")
for (const [fixture, expectedExit] of [["positive", 0], ["negative", 1]] as const) test(`real command ${fixture} exits ${expectedExit}`, () => {
  const directory = mkdtempSync(join(tmpdir(), "effect4-target-control-"))
  try {
    const output = join(directory, `${fixture}.json`)
    const result = Bun.spawnSync(["bun", "tools/target/cli.ts", "--repo", repo, "--queries", `Test/fixtures/target/${fixture}.json`, "--out", output], { cwd: repo })
    expect(result.exitCode).toBe(expectedExit)
    const report = JSON.parse(readFileSync(output, "utf8"))
    expect(report.conforms).toBe(expectedExit === 0)
    expect(report.expected).toEqual(report.attempted)
    if (fixture === "negative") expect(report.observations[0].columns.A.actualToExpected).toBe(false)
  } finally { rmSync(directory, { recursive: true, force: true }) }
}, 30_000)

test("real command refuses missing query input with exit 2", () => {
  const missing = Bun.spawnSync(["bun", "tools/target/cli.ts", "--repo", repo, "--queries", join("Test", "fixtures", "target", "not-present.json")], { cwd: repo })
  expect(missing.exitCode).toBe(2)
  expect(missing.stderr.toString()).toContain("REFUSED input")
}, 30_000)

test("declarative query input refuses malformed controls", () => {
  expect(() => decodeQueries([])).toThrow("nonempty")
  expect(() => decodeQueries([{}])).toThrow("kind")
  const valid = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/positive.json"), "utf8"))
  expect(decodeQueries(valid)).toHaveLength(1)
  expect(decodeQueries([{ ...valid[0], kind: "program" }])[0]?.kind).toBe("program")
  expect(() => decodeQueries([{ ...valid[0], kind: "unknown" }])).toThrow("kind")
  expect(() => decodeQueries([{ ...valid[0], allowUnknown: ["bogus"] }])).toThrow("allowUnknown")
  expect(() => decodeQueries([{ ...valid[0], expected: { ...valid[0].expected, bogus: "never" } }])).toThrow("axis")
})
