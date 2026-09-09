import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { taxonomy } from "../../taxonomy.gen.ts"
import { readFileSync } from "node:fs"
import { Schema } from "effect"
import { RefusalCode } from "../contract.ts"
const rows = Schema.decodeUnknownSync(Schema.Array(Schema.Struct({ code: RefusalCode, file: Schema.String, value: Schema.String })))(JSON.parse(readFileSync(new URL("../fixtures/ledger.json", import.meta.url), "utf8")))
for (const row of rows) test(row.code, () => {
  const source = readFileSync(new URL(`../fixtures/refusals/${row.file}`, import.meta.url), "utf8")
  const template = taxonomy.find(t => t.code === row.code)!
  for (const recognize of [ck, oxc]) {
    const verdict = recognize(source, row.file).find(v => v.unit.name === "p")
    expect(verdict?.kind).toBe("refusal")
    if (verdict?.kind === "refusal") {
      expect(verdict.code).toBe(row.code)
      expect(verdict.detail).toBe(template.detail.replace("{value}", row.value))
    }
  }
})
test("every active refusal is represented; no reserved refusal is emitted", () => {
  expect(rows.map(r => r.code).sort()).toEqual(taxonomy.filter(t => t.status === "active").map(t => t.code).sort())
})
