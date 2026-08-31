/**
 * THE suite-structure seam — the one lawful synchronous read.
 *
 * `it.effect.each` lists and module-scope family bindings must exist
 * BEFORE any Effect can run, so no service realization can exist yet
 * to answer them. This module is the single named exception to the
 * no-node-fs law (operator ruling 2026-08-28), scoped to exactly the
 * data suite construction needs; every VALUE read goes through the
 * `FileSystem` service. Adding a second sync read anywhere is a
 * defect, not a precedent.
 */
// eslint-disable-next-line -- the one sanctioned sync suite-structure read
import { readFileSync } from "node:fs"

const manifestIndex: {
  readonly manifests: ReadonlyArray<string>
  readonly model: string
} = JSON.parse(readFileSync(
  new URL("../../archive/lean-model-0.3/conformance/manifest/INDEX.json", import.meta.url),
  "utf8",
))

export const ManifestModel: string = manifestIndex.model
export const manifestIndexNames: ReadonlyArray<string> = manifestIndex.manifests
