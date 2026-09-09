// Exact fixture gate. Parser children are bounded to 500 files by their parent.
import { readFileSync, readdirSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { join, basename } from "node:path"
import { isDeepStrictEqual } from "node:util"
import * as ck from "./ck.ts"
import * as oxc from "./oxc.ts"
import { effJson } from "../json.gen.ts"
import { encodeProgram } from "../wire.gen.ts"
import { compareVerdicts } from "./gate.ts"

const [mode, dir, offset = "0", count = "500"] = process.argv.slice(2)
if (!dir) throw new Error("check-corpus.ts printed|foreign|printed-batch|foreign-batch <directory> [offset] [count]")
const names = readdirSync(dir).filter(n => n.endsWith(".ts")).sort()
if (!names.length) throw new Error("empty required corpus")
if (mode === "printed-batch" || mode === "foreign-batch") {
  for (const file of names.slice(Number(offset), Number(offset) + Number(count))) {
    const base = join(dir, file.slice(0, -3)), source = readFileSync(base + ".ts", "utf8")
    const expected: unknown = JSON.parse(readFileSync(base + ".json", "utf8")), wire = readFileSync(base + ".eff").toString("hex")
    try {
      if (mode === "printed-batch") {
        for (const engine of [ck, oxc]) {
          const p = engine.readPrintedSource(source, file)
          if (!isDeepStrictEqual(effJson(p), expected) || Buffer.from(encodeProgram(p)).toString("hex") !== wire) throw new Error("printer oracle mismatch")
        }
      } else {
        const left = ck.recognizeSource(source, file), right = oxc.recognizeSource(source, file)
        const expectedKeys: unknown = JSON.parse(readFileSync(base + ".keys.json", "utf8"))
        if (compareVerdicts(left, right).status !== "agree") throw new Error(`engine disagreement: ${JSON.stringify({ left: left.map(v => v.kind === "refusal" ? v : { kind: v.kind, unit: v.unit, keys: v.keys }), right: right.map(v => v.kind === "refusal" ? v : { kind: v.kind, unit: v.unit, keys: v.keys }) })}`)
        if (left.length !== 1 || left[0]?.kind !== "lifted") throw new Error(`expected one lift: ${JSON.stringify(left)}`)
        for (const v of [left[0], right[0]]) {
          if (v?.kind !== "lifted" || !isDeepStrictEqual(effJson(v.eff), expected) || v.wireHex !== wire || !isDeepStrictEqual(v.keys, expectedKeys)) throw new Error(`foreign oracle mismatch: ${JSON.stringify(v)}`)
        }
      }
    } catch (e) { throw new Error(`${basename(base)}: ${String(e)}`, { cause: e }) }
  }
} else {
  if (mode !== "printed" && mode !== "foreign") throw new Error("unknown corpus mode")
  if (mode === "foreign") {
    const index = readFileSync(join(dir, "index.tsv"), "utf8").trimEnd().split("\n").slice(1)
    const indexed = index.map(r => r.split("\t")[0] + ".ts").sort()
    if (!isDeepStrictEqual(indexed, names)) throw new Error("foreign index differs from files")
    const counts = new Map<string, number>()
    for (const row of index) { const style = row.split("\t")[1]!; counts.set(style, (counts.get(style) ?? 0) + 1) }
    for (const row of readFileSync(join(dir, "counts.tsv"), "utf8").trimEnd().split("\n").slice(1)) {
      const [style, n] = row.split("\t")
      if (counts.get(style!) !== Number(n)) throw new Error(`style count mismatch: ${style}`)
    }
    if (counts.size !== 21 + 11520 || names.length !== 22986) throw new Error("foreign construction coverage/count changed")
  }
  for (let at = 0; at < names.length; at += 500) {
    const run = spawnSync(process.execPath, [import.meta.filename, mode + "-batch", dir, String(at), "500"], { encoding: "utf8", maxBuffer: 2 ** 24 })
    if (run.status !== 0) { process.stderr.write(run.stderr); throw new Error(`corpus batch ${at} failed: ${run.status} ${run.error ?? ""}`) }
  }
  console.log(`PASS ${mode}: ${names.length} exact JSON/wire comparisons on each independent reader${mode === "foreign" ? ", exact key tables and complete verdict agreement" : ""}; batch bound 500`)
}
