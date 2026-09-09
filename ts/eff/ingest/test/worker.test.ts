import { expect, test } from "bun:test"
import { recognize } from "../index.ts"
import { mkdtempSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"

test("bounded workers return ordered, validated reports", async () => {
  const dir = mkdtempSync(join(tmpdir(), "effect4-ingest-"))
  try {
    writeFileSync(join(dir, "b.ts"), 'import { Effect } from "effect"; const p = Effect.succeed(2);')
    writeFileSync(join(dir, "a.ts"), 'import { Effect } from "effect"; const p = Effect.succeed(1);')
    const reports = []
    for await (const row of recognize([dir], { root: dir, workers: 2, batchSize: 1 })) reports.push(row)
    expect(reports.map(r => [r.file, r.agreement])).toEqual([["a.ts", "agree"], ["b.ts", "agree"]])
    expect(reports.every(r => r.ckParsed && r.oxcParsed)).toBe(true)
  } finally { rmSync(dir, { recursive: true }) }
})

test("nested paths are globally sorted and overlapping input roots appear once", async () => {
  const { mkdirSync } = await import("node:fs")
  const dir = mkdtempSync(join(tmpdir(), "effect4-ingest-paths-"))
  try {
    mkdirSync(join(dir, "a"))
    for (const file of ["a.ts", "a/z.ts", "b.ts"]) writeFileSync(join(dir, file), 'import { Effect } from "effect"; const p = Effect.succeed(1);')
    const names = []
    for await (const row of recognize([join(dir, "a"), dir, join(dir, "a.ts")], { root: dir, workers: 2, batchSize: 2 })) names.push(row.file)
    expect(names).toEqual(["a.ts", "a/z.ts", "b.ts"])
  } finally { rmSync(dir, { recursive: true }) }
})
