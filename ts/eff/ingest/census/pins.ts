// Retargeted from foldlab experiments/parser-census/src/pins.ts at 4005d34f.
import { createHash } from "node:crypto"
import { readFileSync } from "node:fs"
import { pinsDigest, checkRuntime } from "../pins.ts"
export function censusPins(manifest: string, labels: string) {
  checkRuntime()
  return { recognizer: pinsDigest, corpus: createHash("sha256").update(readFileSync(manifest)).digest("hex"), labels: createHash("sha256").update(readFileSync(labels)).digest("hex"), instrumentSource: "foldlab@4005d34f" }
}
