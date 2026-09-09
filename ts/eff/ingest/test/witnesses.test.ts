import { test, expect } from "bun:test"
import { readFileSync } from "node:fs"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { effJson } from "../../json.gen.ts"
const ledger: unknown = JSON.parse(readFileSync(new URL("../fixtures/witnesses/ledger.json", import.meta.url), "utf8"))
test("saved domain witnesses retain their approved foreign expectations", () => {
  if (!Array.isArray(ledger)) throw new Error("invalid witness ledger")
  for (const row of ledger) for (const engine of [ck, oxc]) {
    const [v] = engine(readFileSync(new URL(`../fixtures/witnesses/${row.file}`, import.meta.url), "utf8"), row.file)
    expect(v?.kind).toBe(row.kind)
    if (v?.kind === "refusal") { expect(v.code).toBe(row.code); expect(v.detail).toBe(row.detail) }
    if (v?.kind === "lifted") { expect(effJson(v.eff)).toEqual(row.eff); expect(v.keys).toEqual(row.keys) }
  }
})
