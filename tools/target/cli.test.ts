import { expect, test } from "bun:test"
import { mkdtempSync, readFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, resolve } from "node:path"
import { decodeQueries } from "./input.ts"

const repo = resolve(import.meta.dir, "../..")
test("real command passes independent positive and fails wrong-answer conformance", () => {
  const directory = mkdtempSync(join(tmpdir(), "effect4-target-control-"))
  try {
    for (const [fixture, expectedExit] of [["positive", 0], ["negative", 1]] as const) {
      const output = join(directory, `${fixture}.json`)
      const result = Bun.spawnSync(["python3", "scripts/check-target.py", "--queries", `Test/fixtures/target/${fixture}.json`, "--out", output], { cwd: repo })
      expect(result.exitCode).toBe(expectedExit)
      const report = JSON.parse(readFileSync(output, "utf8"))
      expect(report.conforms).toBe(expectedExit === 0)
      expect(report.expected).toEqual(report.attempted)
      if (fixture === "negative") expect(report.observations[0].columns.A.actualToExpected).toBe(false)
    }
    const missing = Bun.spawnSync(["python3", "scripts/check-target.py", "--queries", join("Test", "fixtures", "target", "not-present.json")], { cwd: repo })
    expect(missing.exitCode).toBe(2)
    expect(missing.stderr.toString()).toContain("REFUSED input")
  } finally { rmSync(directory, { recursive: true, force: true }) }
})

test("declarative query input refuses malformed controls", () => {
  expect(() => decodeQueries([])).toThrow("nonempty")
  expect(() => decodeQueries([{}])).toThrow("kind")
  const valid = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/positive.json"), "utf8"))
  expect(decodeQueries(valid)).toHaveLength(1)
  expect(() => decodeQueries([{ ...valid[0], allowUnknown: ["bogus"] }])).toThrow("allowUnknown")
  expect(() => decodeQueries([{ ...valid[0], expected: { ...valid[0].expected, bogus: "never" } }])).toThrow("axis")
})
