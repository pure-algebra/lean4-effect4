import { expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
import { mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { fileURLToPath } from "node:url"

test("Bun and Node emit byte-identical JSONL through their actual workers", () => {
  const dir = mkdtempSync(join(tmpdir(), "effect4-ingest-runtime-"))
  try {
    const file = join(dir, "sample.ts")
    writeFileSync(file, 'import { Effect, Context } from "effect"; const K = Context.Service<number>("K"); const p = Effect.provideService(Effect.service(K), K, 1);')
    const cli = fileURLToPath(new URL("../cli.ts", import.meta.url))
    const args = [cli, "recognize", file, "--root", dir, "--workers", "1"]
    const bun = spawnSync(process.execPath, args, { encoding: "utf8" })
    const node = spawnSync("node", ["--experimental-transform-types", "--disable-warning=ExperimentalWarning", ...args], { encoding: "utf8" })
    expect(bun.status).toBe(0)
    expect(node.stderr).toBe("")
    expect(node.status).toBe(0)
    expect(bun.stdout).toBe(node.stdout)
    expect(bun.stdout).toContain('"eff":["provideService"')
  } finally { rmSync(dir, { recursive: true }) }
})
