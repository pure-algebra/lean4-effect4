import { expect, test } from "bun:test"
import { taxonomy, activeCodes, reservedCodes } from "../taxonomy.gen.ts"
import { forms } from "../forms.gen.ts"
import { packages, packageOf } from "../packages.gen.ts"
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"

test("the generated taxonomy carries the owner's exact active/reserved partition", () => {
  expect(taxonomy.length).toBe(23)
  expect(activeCodes.length).toBe(22)
  expect(reservedCodes).toEqual(["E-HELPER-UNPINNED"])
  expect(new Set(taxonomy.map(r => r.code)).size).toBe(23)
})

// The host rows slice (2026-09-09): the two canonical package tables, rows in table order.
test("the generated package tables are the two of Program/Packages, with their codes and keys", () => {
  expect(packages.map(p => [p.name, p.service, p.key, p.target])).toEqual([
    ["SqliteBun", 8, "effect/sql/SqlClient", "SqlClient.SqlClient"],
    ["KeyValueStoreMemory", 9, "effect/persistence/KeyValueStore", "KeyValueStore.KeyValueStore"],
  ])
  expect(packages.map(p => p.rows.map(r => r.spelling))).toEqual([
    ["Sql.open", "unsafe", "Sql.close"],
    ["Kv.make", "get", "set", "remove", "has"],
  ])
  expect(packageOf(8)?.rows[1]?.shape).toBe("method")
  expect(packageOf(9)?.rows[1]?.answer).toEqual({ _tag: "option", inner: { _tag: "string" } })
  expect(packageOf(7)).toBeUndefined()
  for (const p of packages) for (const r of p.rows) {
    expect(r.registration).toBe("external")
    expect(r.cite.startsWith("vendor/effect-4.0.0-rc.112/src/")).toBe(true)
  }
})

test("the shared lambda shape names only incr and retains takeAndBump", () => {
  expect(forms.lambdas.find(r => r.atom === "incr")?.shape).toBe("addOne")
  expect(forms.lambdas.find(r => r.atom === "takeAndBump")?.shape).toBeNull()
  const shapes = forms.lambdas.map(r => r.shape).filter(s => s !== null)
  expect(new Set(shapes).size).toBe(4)
})

test("editing either generated payload fails its import-time stamp", async () => {
  const dir = mkdtempSync(join(tmpdir(), "effect4-table-stamp-"))
  try {
    const files: Array<{ control: string; mutant: string }> = []
    for (const [name, from, to] of [["taxonomy", "E-PARAM-SHAPE", "E-PARAM-OTHER"], ["forms", '"binder":0', '"binder":1']] as const) {
      const source = readFileSync(new URL(`../${name}.gen.ts`, import.meta.url), "utf8")
      expect(source.includes(from)).toBe(true)
      const control = join(dir, `${name}-control.ts`)
      const mutant = join(dir, `${name}-mutant.ts`)
      writeFileSync(control, source)
      writeFileSync(mutant, source.replace(from, to))
      files.push({ control, mutant })
    }
    for (const { control, mutant } of files) {
      expect(typeof await import(control)).toBe("object")
      await expect(import(mutant)).rejects.toThrow("stamp mismatch")
    }
  } finally { rmSync(dir, { recursive: true }) }
})
