import { test, expect } from "bun:test"
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs"
import { join } from "node:path"
import { tmpdir } from "node:os"
import { Generations, versionGeneration } from "../census/corpus.ts"
import { add, bucket, headSpelling, pairs } from "../census/tally.ts"
import { recognize } from "../index.ts"
import { recognizeSource } from "../ck.ts"

test("generation comes from the owning workspace and resolves pinned catalogs", () => {
  const root = mkdtempSync(join(tmpdir(), "ingest-generations-"))
  const put = (path: string, value: unknown) => { const dir = join(root, path); mkdirSync(dir, { recursive: true }); writeFileSync(join(dir, "package.json"), JSON.stringify(value)) }
  try {
    put("", { workspaces: { catalog: { effect: "4.0.0-rc.112" } } })
    put("v3", { dependencies: { effect: "^3.19.14" } })
    put("v4", { dependencies: { effect: "catalog:" } })
    const g = new Generations(root)
    expect(g.forFile("v3/examples/a.ts").generation).toBe("v3")
    expect(g.forFile("v4/examples/a.ts").generation).toBe("v4")
    expect(() => g.forFile("ambiguous.ts")).toThrow("no unambiguous")
    expect(versionGeneration(">=3.20.0 <4")).toBe("v3")
    expect(versionGeneration("latest")).toBeUndefined()
  } finally { rmSync(root, { recursive: true }) }
})

test("missing or different engine verdicts cannot become recognized units", () => {
  const [lift] = recognizeSource('import { Effect } from "effect"; const p = Effect.succeed(1)', "a.ts")
  const [refusal] = recognizeSource('import { Effect } from "effect"; const p = Effect.retry(1)', "a.ts")
  const b = bucket()
  add(b, lift!, null); add(b, lift!, refusal!); add(b, lift!, lift!)
  expect([b.candidates, b.lifted, b.disagree]).toEqual([3, 1, 2])
  expect(headSpelling(refusal!)).toBe("Effect.retry")
  expect(pairs({ file: "a.ts", pins: "x", contentDigest: "x", ck: [], oxc: [refusal!], ckParsed: false, oxcParsed: true, agreement: "disagree" })).toHaveLength(1)
})

test("census reuses the parse and a warm cache reads and parses no source", async () => {
  const root = mkdtempSync(join(tmpdir(), "ingest-census-cache-"))
  try {
    const source = join(root, "a.mts")
    writeFileSync(source, 'import { Effect } from "effect"; const p = Effect.succeed(1)')
    let reads = 0
    const options = { root, workers: 1, census: true, cacheDir: join(root, "cache"), onMetrics: (m: { reads: number }) => { reads += m.reads } }
    const cold = []
    for await (const r of recognize([source], options)) cold.push(r)
    expect(reads).toBe(1)
    expect(cold[0]!.ckDeclarations).toEqual(cold[0]!.oxcDeclarations)
    expect(cold[0]!.ckDeclarations?.[0]?.name).toBe("p")
    reads = 0
    const warm = []
    for await (const r of recognize([source], options)) warm.push(r)
    expect(reads).toBe(0); expect(warm).toEqual(cold)
  } finally { rmSync(root, { recursive: true }) }
})
