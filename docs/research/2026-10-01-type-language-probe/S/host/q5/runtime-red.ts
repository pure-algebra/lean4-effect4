// Red twin of runtime.ts: claims the raw module's JSON object keeps one key per table entry (30),
// which is the claim under which (C) would change decoded behaviour. It must fail (exit 1): a
// JavaScript object literal keeps one entry per key, so the raw object holds 8 keys.
import * as Raw from "./meta-raw.ts"
const n = Object.keys((Raw.MetaSchemaJson as any).references).length
console.log(`raw JSON object keys: ${n}; the red claim expects 30`)
if (n !== 30) (globalThis as any).process.exit(1)
