/**
 * The SERVING.md drift gate — the emitted-projection discipline
 * applied to the deployment doc, at the strength this lane can give
 * it without minting a Lean emitter (the doc's factual vocabularies
 * are RE-DERIVED from the live exported values and compared, so a
 * hand-typed fact that drifts from the estate is a red gate, not a
 * stale sentence; the judgment prose stays hand-written and
 * unjudged here).
 *
 * What is checked, and against which authority:
 *
 * - routes            ← `bin/mcp/http.ts` (mcpPath, metricsPath,
 *                        projectionsPath, historyPath) — every route
 *                        the daemon binds is NAMED here, because a
 *                        route this gate cannot see is one whose row
 *                        in SERVING.md and in PROFILE §14 goes stale
 *                        silently and forever after
 * - policy fields     ← `ServePolicy`'s own schema keys
 * - protocol ceiling  ← `offeredProtocols` (every offered revision named;
 *                        the ceiling stated as the newest)
 * - metric vocabulary ← the exported Metric instances' ids, BOTH ways:
 *                        every metric is documented, and every
 *                        `cas.`-prefixed token in the doc is a real id
 * - projections       ← `projectionSources` names
 * - log fields        ← the field names the front door and heartbeat
 *                        actually annotate
 * - the tool table    ← the emitted `cas-tools.json`: the COUNT and
 *                        every tool's name, because "the same five
 *                        tools" went stale against a manifest that
 *                        had grown to six and nothing caught it
 */
import { describe, expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer, Path } from "effect"
import { ServePolicy } from "../bin/cli/store.ts"
import {
  historyPath,
  mcpPath,
  metricsPath,
  projectionsPath,
  projectionSources,
  replicaAge,
  requestDuration,
  rssBytes,
  wireInflight,
} from "../bin/mcp/http.ts"
import { offeredProtocols } from "../bin/mcp/server.ts"
import * as Telemetry from "../bin/mcp/telemetry.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"

/** Disk, plus the path service `fromFileUrl` needs. */
const layerFiles: Layer.Layer<FileSystem.FileSystem | Path.Path> = Layer.merge(
  layerDiskFs,
  Path.layer,
)

/** A file beside this test, by path rather than by URL. `URL.pathname`
 * is PERCENT-ENCODED — a checkout under a directory with a space in
 * it hands the filesystem `%20` and the read fails — so the file URL
 * is decoded through `Path.fromFileUrl`, the same way
 * `bin/mcp/http.ts` resolves the projection sources. */
const fileAt = (relative: string): Effect.Effect<string, never, Path.Path> =>
  Path.Path.pipe(
    Effect.flatMap((path) => path.fromFileUrl(new URL(relative, import.meta.url))),
    Effect.orDie,
  )

/** The doc, read through the `FileSystem` service. Filesystem is an
 * effect (operator ruling 2026-08-28, gated by
 * `scripts/check-src-purity.ts`), so this gate reads its subject the
 * way `Cli.test.ts` reads VOCABULARY.md — not with `node:fs`.
 *
 * SERVING.md lives HERE, beside the profile it companions: decision
 * 32(b) promoted it to Category 1 and moved it out of
 * `docs/lab-core/`. */
const servingDoc = fileAt("../SERVING.md").pipe(
  Effect.flatMap((file) =>
    FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFileString(file)))
  ),
)

/** The emitted tool manifest — the authority for what the hosts serve,
 * and therefore for what this doc may claim they serve. */
const toolManifest = fileAt("../../cas/mcp/cas-tools.json").pipe(
  Effect.flatMap((file) =>
    FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFileString(file)))
  ),
  Effect.map((raw) =>
    JSON.parse(raw) as { readonly tools: ReadonlyArray<{ readonly name: string }> }
  ),
)

describe("SERVING.md — the factual vocabularies match the estate", () => {
  it.effect("names the routes the daemon actually binds", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      for (const route of [mcpPath, metricsPath, projectionsPath, historyPath]) {
        expect(doc).toContain(`\`${route}\``)
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("rules every ServePolicy field the schema actually has", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      for (const field of Object.keys(ServePolicy.fields)) {
        expect(doc, `ServePolicy.${field} is unruled in SERVING.md`)
          .toContain(field)
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("states the offered protocol revisions, all of them, newest as the ceiling", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      for (const protocol of offeredProtocols) {
        expect(doc).toContain(protocol.protocolVersion)
      }
      const ceiling = offeredProtocols[0].protocolVersion
      expect(doc).toContain(`**${ceiling}`)
    }).pipe(Effect.provide(layerFiles)))

  it.effect("documents every metric, and documents no metric that does not exist", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      const metricIds = [
        Telemetry.inflight.id,
        Telemetry.calls.id,
        Telemetry.refused.id,
        Telemetry.sqlWait.id,
        requestDuration.id,
        wireInflight.id,
        rssBytes.id,
        replicaAge.id,
      ]
      for (const id of metricIds) {
        expect(doc, `metric ${id} is undocumented`).toContain(`\`${id}\``)
      }
      // The reverse direction catches a renamed metric leaving its old
      // name behind in the doc.
      const documented = doc.match(/`cas\.[a-z0-9_.]+`/gu) ?? []
      for (const token of documented) {
        const id = token.slice(1, -1)
        expect(metricIds, `SERVING.md documents ${id}, which no metric carries`)
          .toContain(id)
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("lists every served projection by name", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      for (const projection of projectionSources) {
        expect(doc, `projection ${projection.name} is undocumented`)
          .toContain(projection.name)
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("states the tool table's size and names it, both from the emitted manifest", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      const manifest = yield* toolManifest
      // The COUNT, derived. This is the assertion that would have
      // caught "the same five tools" the day the manifest reached six.
      expect(doc, "SERVING.md misstates how many tools the hosts serve")
        .toContain(`the same ${manifest.tools.length} tools`)
      for (const tool of manifest.tools) {
        expect(doc, `tool ${tool.name} is undocumented`).toContain(`\`${tool.name}\``)
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("documents the hoover log-field vocabulary the hosts actually emit", () =>
    Effect.gen(function* () {
      const doc = yield* servingDoc
      for (
        const field of [
          "seq",
          "plane",
          "method",
          "path",
          "status",
          "ms",
          "elapsedMs",
          "lateMs",
          "refused=host|origin",
          "message=heartbeat",
          "message=request",
        ]
      ) {
        expect(doc, `log field ${field} is undocumented`).toContain(field)
      }
    }).pipe(Effect.provide(layerFiles)))
})
