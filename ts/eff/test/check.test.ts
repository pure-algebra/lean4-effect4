// The corpus check's two answers (`check.ts`, the gate `make check-ts` runs over Lean's corpus):
// an oracle in the tagged print, the program's one public JSON (decisions row 418, D2), matches the
// reader's JSON byte for byte; an oracle in the retired positional spelling is a mismatch, and the
// run fails. The second test is the check's red control.

import { expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
import { mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { fileURLToPath } from "node:url"

const checker = fileURLToPath(new URL("../check.ts", import.meta.url))

/** Run the check over one program, `Effect.succeed(42)`, with the given oracle beside it. */
const run = (oracle: string) => {
  const directory = mkdtempSync(join(tmpdir(), "effect4-check-test-"))
  try {
    writeFileSync(join(directory, "sample.ts"), "Effect.succeed(42)\n")
    writeFileSync(join(directory, "sample.json"), oracle + "\n")
    return spawnSync(process.execPath, [checker, directory], { encoding: "utf8", timeout: 30_000 })
  } finally {
    rmSync(directory, { recursive: true })
  }
}

test("an oracle in the tagged print matches the reader's JSON", () => {
  const result = run('{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":42}}}')
  expect(result.status).toBe(0)
  expect(result.stdout).toContain("files 1: matched 1, mismatched 0")
})

test("the control: an oracle in the positional spelling is a mismatch, and the run fails", () => {
  const result = run('["succeed",["lit",["nat",42]]]')
  expect(result.status).toBe(1)
  expect(result.stdout).toContain("files 1: matched 0, mismatched 1")
})
