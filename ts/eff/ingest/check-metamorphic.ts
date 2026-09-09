import { readFileSync, readdirSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { join } from "node:path"
import * as ck from "./ck.ts"
import * as oxc from "./oxc.ts"
import { canonJson, sourceEditKey } from "./contract.ts"
import { compareVerdicts } from "./gate.ts"
import { effJson } from "../json.gen.ts"
const [mode, dir, offset = "0"] = process.argv.slice(2)
if (!dir) throw new Error("check-metamorphic.ts printed|foreign|negative[-batch] directory [offset]")
const files = readdirSync(dir).filter(n => n.endsWith(".ts")).sort()
if (!files.length) throw new Error("required source-edit corpus absent")
const kind = mode?.split("-")[0]
if (mode?.endsWith("-batch")) {
  for (const file of files.slice(Number(offset), Number(offset) + 50)) {
    const source = readFileSync(join(dir, file), "utf8")
    const extras = 'import { Context as UnusedContext } from "effect";\nconst __unusedKey = UnusedContext.Service<number>("unused");\nconst __unused = 7;\n'
    const variants = [
      "// comment\n" + source,
      source.replace(/;\r?\n/g, ";  \n\n"),
      source.replace(/\r?\n/g, "\r\n"),
      source.replace(/startImmediately: (true|false), uninterruptible: (true|false|"inherit")/g, "uninterruptible: $2, startImmediately: $1"),
      extras + source,
      source + "\n" + extras
    ]
    try {
      if (kind === "printed") {
        for (const engine of [ck, oxc]) {
          const expected = canonJson(effJson(engine.readPrintedSource(source, file)))
          for (const variant of variants) if (canonJson(effJson(engine.readPrintedSource(variant, file))) !== expected) throw new Error("printer source-edit drift")
        }
      } else {
        const before = [ck.recognizeSource(source, file), oxc.recognizeSource(source, file)]
        for (const variant of variants) {
          const after = [ck.recognizeSource(variant, file), oxc.recognizeSource(variant, file)]
          if (compareVerdicts(after[0], after[1]).status !== "agree") throw new Error("source-edit engine disagreement")
          for (const i of [0, 1]) for (const expected of before[i]!) {
            const actual = after[i]!.find(v => v.unit.name === expected.unit.name)
            if (!actual || canonJson(sourceEditKey(actual)) !== canonJson(sourceEditKey(expected))) throw new Error(`source-edit drift for ${expected.unit.name}: ${JSON.stringify(actual)}`)
          }
        }
      }
    } catch (e) { throw new Error(`${file}: ${String(e)}`) }
  }
} else {
  if (!["printed", "foreign", "negative"].includes(kind ?? "")) throw new Error("invalid source-edit mode")
  for (let offset = 0; offset < files.length; offset += 50) {
    const run = spawnSync(process.execPath, [import.meta.filename, `${kind}-batch`, dir, String(offset)], { encoding: "utf8" })
    if (run.status !== 0) { process.stderr.write(run.stderr); process.exit(run.status ?? 2) }
  }
  console.log(`PASS source edits: ${kind}, ${files.length} fixtures × 6 transformations × 2 engines; source locations alone excluded; workers limited to 350 source variants per engine`)
}
