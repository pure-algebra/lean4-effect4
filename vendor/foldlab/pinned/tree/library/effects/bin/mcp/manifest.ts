/**
 * The tool manifest as the CONTRACT — the host's boot-time gate.
 *
 * `library/cas/mcp/cas-tools.json` is emitted by `lake exe mcpspec`
 * from `Cas/Backend/Mcp.lean` and byte-gated in `check:cas`. Semantics
 * flow FROM the Lean estate, so the manifest — not this package — is
 * the authority on which tools exist, what each is called, what it
 * says about itself, and the canonical schema codes its params and
 * result take.
 *
 * This module does two things and nothing else: it READS that document
 * (a typed refusal when it is absent or undecodable, never a default),
 * and it COMPARES it against the tool table the host actually serves.
 * A served set that drifts from the manifest is a defect, so the
 * comparison is a boot gate: `cas serve` refuses to speak MCP at all
 * rather than answer `tools/list` with a table the estate did not
 * emit.
 *
 * The comparison is over the ratified canonical printer
 * (`canonicalJson`, CAS-004: compact, codepoint-sorted keys at every
 * depth). That makes it total over every code the `Ast` projection can
 * spell — a code this host has never seen still compares exactly —
 * and it makes key order in the emitted file immaterial, which is the
 * emitter's own claim (`SelfCodec.lean`: "Key order here is immaterial:
 * the canonical rendering sorts at render time").
 *
 * WHAT THE GATE NOW COMPARES. Both sides are generated: the JSON
 * document and the served table (`src/cas/generated/McpToolCodes.ts`)
 * are two renderings of the one `Cas.Backend.Mcp.tools` list, emitted
 * by the same run of `lake exe mcpspec`. The gate is therefore
 * trivially green, and it stays as defence in depth — a red one means
 * the two renderings in `tools/EmitMcp.lean` have forked, or the
 * committed artifacts came from different runs, both of which are
 * facts worth refusing a boot over.
 */
import { Effect, FileSystem, Path, Schema } from "effect"
import { canonicalJson } from "../../src/cas/Value.ts"
import type { McpToolCode, McpToolRow } from "../../src/cas/generated/McpToolCodes.ts"

/**
 * A canonical schema code in the revision-0 tagged projection, as far
 * as the emitted manifest currently spells one. This is a TYPE, not a
 * decoder: nothing here reads a code, so the type exists only to give
 * the served table a shape to be checked against. A manifest carrying
 * a code outside it still compares exactly, because the comparison is
 * over the canonical printer and not over this union.
 *
 * It is not written here. `lake exe mcpspec` emits it beside the rows
 * it types, from the same `Cas.Backend.Mcp` value the JSON manifest
 * comes from, so the fragment this host is written against widens when
 * the estate's codes do and never before.
 */
export type ToolCode = McpToolCode

/**
 * One manifest row. `params` and `result` are canonical schema codes —
 * the revision-0 tagged JSON projection of `Cas.Schema.Ast` — and they
 * are carried UNINTERPRETED. This host compares codes; it does not
 * read them, so it needs no second spelling of the schema language and
 * cannot fall behind one.
 */
export const ManifestTool = Schema.Struct({
  name: Schema.String,
  description: Schema.String,
  params: Schema.Unknown,
  result: Schema.Unknown,
})
export type ManifestTool = typeof ManifestTool.Type

/** The manifest document, exactly as `Cas.Backend.Mcp.manifest` renders it. */
export const ToolManifest = Schema.Struct({
  language: Schema.Literal("cas"),
  manifestVersion: Schema.Int,
  schemaRevision: Schema.Int,
  tools: Schema.Array(ManifestTool),
})
export type ToolManifest = typeof ToolManifest.Type

/**
 * The manifest revision this host implements. `Mcp.lean` says the
 * number is "bumped only by ruling", so a bump is a ruling this host
 * has not read yet — it refuses rather than serving a revision it was
 * not written against.
 *
 * Revision 1 (2026-08-29, the brain-stem package) is the first time
 * this constant has moved, and it moved exactly as the seam was
 * designed to move: `RunParams` grew literal-address operands and the
 * `load` instruction, `cas_run_ref` joined the table, Lean's
 * `manifestVersion` bumped, and this followed in the same change with
 * a carrier and a handler beside it. A host that had only the carriers
 * would now be refused at boot rather than at the first call, which is
 * the whole point of the gate.
 */
export const implementedManifestVersion = 1

/** The emitted manifest, relative to this file: `library/cas/mcp/`. */
const manifestFileUrl = new URL("../../../cas/mcp/cas-tools.json", import.meta.url)

/** The manifest could not be read: absent, unreadable, or undecodable. */
export class ManifestUnavailable extends Schema.TaggedError<ManifestUnavailable>()(
  "mcp/ManifestUnavailable",
  { path: Schema.String, reason: Schema.String },
) {
  override get message(): string {
    return [
      `the tool manifest could not be read at ${this.path}`,
      `  ${this.reason}`,
      "  it is generated: run `lake exe mcpspec` in library/cas",
    ].join("\n")
  }
}

/** The served table and the manifest do not say the same thing. */
export class ManifestDisagreement extends Schema.TaggedError<ManifestDisagreement>()(
  "mcp/ManifestDisagreement",
  { differences: Schema.Array(Schema.String) },
) {
  override get message(): string {
    return [
      "the served tools disagree with the emitted manifest",
      ...this.differences.map((line) => `  ${line}`),
      "  the manifest is the contract — regenerate it, or fix the host",
    ].join("\n")
  }
}

/** Where the manifest lives for this invocation: the emitted document
 * beside the Lean sources, or an explicitly named one. */
export const manifestPath: Effect.Effect<string, ManifestUnavailable, Path.Path> = Path
  .Path.pipe(
    Effect.flatMap((path) => path.fromFileUrl(manifestFileUrl)),
    Effect.mapError((error) =>
      new ManifestUnavailable({
        path: manifestFileUrl.href,
        reason: error.message,
      })
    ),
  )

/**
 * Read and decode the manifest. Every failure is one typed refusal
 * naming the path, because "the generated file is missing" and "the
 * generated file is not a manifest" are the same actionable fact for
 * whoever is starting the server: regenerate it.
 */
export const readManifest = (
  path: string,
): Effect.Effect<ToolManifest, ManifestUnavailable, FileSystem.FileSystem> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const raw = yield* fs.readFileString(path).pipe(
      Effect.mapError((error) =>
        new ManifestUnavailable({ path, reason: error.message })
      ),
    )
    return yield* Schema.decodeUnknownEffect(Schema.fromJsonString(ToolManifest))(raw)
      .pipe(
        Effect.mapError((error) =>
          new ManifestUnavailable({ path, reason: error.message })
        ),
      )
  })

/** One row of the table this host actually serves, in the manifest's
 * own vocabulary — a name, what the tool says about itself, and the
 * two canonical schema codes. This IS the emitted row type: the served
 * table is the generated one, so the shape it is checked against is
 * the shape the emitter declared. */
export type ServedTool = McpToolRow

/** A code as the bytes it is compared by. Both sides are plain JSON —
 * one side came out of `JSON.parse`, the other is a literal in the
 * generated `McpToolCodes.ts` — so the printer's own refusals (cycles, exotic
 * prototypes, symbol keys) are unreachable here by construction, and
 * nothing catches for them. */
const renderCode = (code: unknown): string => canonicalJson(code)

/**
 * THE BOOT GATE. Row by row, in the manifest's order: the same names,
 * the same self-description, the same params code, the same result
 * code. Order is part of the agreement — the manifest is a list, and a
 * host that reorders it is a host answering a document the estate did
 * not emit.
 *
 * Every difference is collected before refusing, so one boot names
 * every drift instead of one.
 */
export const assertAgreement = (
  manifest: ToolManifest,
  served: ReadonlyArray<ServedTool>,
): Effect.Effect<void, ManifestDisagreement> =>
  Effect.suspend(() => {
    const differences: Array<string> = []

    if (manifest.manifestVersion !== implementedManifestVersion) {
      differences.push(
        `manifest revision ${manifest.manifestVersion}, host implements ${implementedManifestVersion}`,
      )
    }

    const manifestNames = manifest.tools.map((tool) => tool.name)
    const servedNames = served.map((tool) => tool.name)
    if (manifestNames.join(",") !== servedNames.join(",")) {
      differences.push(
        `tools: manifest has [${manifestNames.join(", ")}], host serves [${servedNames.join(", ")}]`,
      )
    }

    for (const [index, expected] of manifest.tools.entries()) {
      const actual = served[index]
      if (actual === undefined || actual.name !== expected.name) continue
      if (actual.description !== expected.description) {
        differences.push(`${expected.name}: description differs from the manifest`)
      }
      if (renderCode(actual.params) !== renderCode(expected.params)) {
        differences.push(
          `${expected.name}: params code differs — manifest ${renderCode(expected.params)}, host ${renderCode(actual.params)}`,
        )
      }
      if (renderCode(actual.result) !== renderCode(expected.result)) {
        differences.push(
          `${expected.name}: result code differs — manifest ${renderCode(expected.result)}, host ${renderCode(actual.result)}`,
        )
      }
    }

    return differences.length === 0
      ? Effect.void
      : Effect.fail(new ManifestDisagreement({ differences }))
  })
