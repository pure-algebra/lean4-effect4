import { expect, test } from "bun:test"
import { taxonomy, activeCodes, reservedCodes } from "../taxonomy.gen.ts"
import { forms } from "../forms.gen.ts"
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"

test("the generated taxonomy carries the owner's exact active/reserved partition", () => {
  expect(taxonomy.length).toBe(23)
  expect(activeCodes.length).toBe(22)
  expect(reservedCodes).toEqual(["E-HELPER-UNPINNED"])
  expect(new Set(taxonomy.map(r => r.code)).size).toBe(23)
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
