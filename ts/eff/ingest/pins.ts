// Pin checking follows foldlab parser-census/src/pins.ts at 4005d34f.
import { createHash } from "node:crypto"
import { readFileSync, readdirSync } from "node:fs"
import { fileURLToPath } from "node:url"
import { Schema } from "effect"
import { stamp as profileStamp } from "../profile.gen.ts"
import { stamp as formsStamp } from "../forms.gen.ts"
import { stamp as taxonomyStamp } from "../taxonomy.gen.ts"
const Package = Schema.Struct({ version: Schema.String })
const decodePackage = Schema.decodeUnknownSync(Package)
export const pins = { typescript: "5.9.2", oxc: "0.147.0", effect: "4.0.0-rc.112", bun: "1.3.14", node: "22.23.2", bunTypes: "1.4.1", profileStamp, formsStamp, taxonomyStamp } as const
for (const [name, expected] of [["typescript", pins.typescript], ["oxc-parser", pins.oxc], ["effect", pins.effect], ["@types/bun", pins.bunTypes]]) {
  const actual = decodePackage(JSON.parse(readFileSync(new URL(`../node_modules/${name}/package.json`, import.meta.url), "utf8"))).version
  if (actual !== expected) throw new Error(`pin drift: ${name} expected ${expected}, found ${actual}`)
}
const Manifest = Schema.Struct({ dependencies: Schema.Record(Schema.String, Schema.String), devDependencies: Schema.Record(Schema.String, Schema.String) })
const manifest = Schema.decodeUnknownSync(Manifest)(JSON.parse(readFileSync(new URL("../package.json", import.meta.url), "utf8")))
for (const [name, expected] of [["typescript", pins.typescript], ["oxc-parser", pins.oxc], ["effect", pins.effect], ["@types/bun", pins.bunTypes]]) {
  if ((manifest.dependencies[name!] ?? manifest.devDependencies[name!]) !== expected) throw new Error(`manifest pin drift: ${name}`)
}
const root = fileURLToPath(new URL("./", import.meta.url))
const ownSources = readdirSync(root, { recursive: true }).filter((n): n is string => typeof n === "string" && /\.(?:ts|mjs|mts)$/.test(n) && !n.startsWith("test/") && !n.startsWith("fixtures/")).sort().map(n => readFileSync(root + n))
const projections = ["eff.gen.ts", "json.gen.ts", "wire.gen.ts", "profile.gen.ts", "forms.gen.ts", "taxonomy.gen.ts", "packages.gen.ts"].map(n => readFileSync(new URL("../" + n, import.meta.url)))
export const pinsDigest = createHash("sha256").update(JSON.stringify(pins)).update(readFileSync(new URL("../bun.lock", import.meta.url))).update(Buffer.concat([...ownSources, ...projections])).update(readFileSync(new URL("../read.ts", import.meta.url))).digest("hex")
export function checkRuntime(): void {
  const bun = process.versions.bun
  if (bun ? bun !== pins.bun : process.versions.node !== pins.node) throw new Error(`runtime pin drift: ${bun ? `bun ${bun}` : `node ${process.versions.node}`}`)
}
