import { expect, test } from "bun:test"
import { mkdtemp, rm, writeFile } from "node:fs/promises"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { instrument } from "./instrument.ts"

async function run(program: string): Promise<number> {
  const folder = await mkdtemp(join(tmpdir(), "stream-instrument-"))
  try {
    const row = { id: "control", program, expected: [...program.matchAll(/\/\/ =>([^\n]*)/g)].map(m => m[1]!) }
    const output = instrument(row)
    const path = join(folder, "control.ts")
    await writeFile(path, output.code)
    const child = Bun.spawn([process.execPath, path], { stdout: "ignore", stderr: "ignore" })
    return await child.exited
  } finally { await rm(folder, { recursive: true, force: true }) }
}

test("literal oracle agrees and rejects a changed result", async () => {
  expect(await run("const value = [1, 2] // => [1, 2]")).toBe(0)
  expect(await run("const value = [1, 3] // => [1, 2]")).not.toBe(0)
})
test("an assertion inside an uncalled function cannot pass", async () => {
  expect(await run("function dormant() {\n  7 // => 7\n}\n")).not.toBe(0)
})
test("the source expression executes once", async () => {
  expect(await run("let n = 0\n++n // => 1\nn // => 1")).toBe(0)
})
test("a later failure does not disappear behind an earlier passing assertion", async () => {
  expect(await run("1 // => 1\nthrow Error('later failure')")).not.toBe(0)
})
test("missing observations and altered expectation counts refuse", () => {
  expect(() => instrument({ id: "missing", program: "const x = 1", expected: [] })).toThrow("no exact expectations")
  expect(() => instrument({ id: "omitted", program: "1 // => 1", expected: [] })).toThrow("no exact expectations")
})
