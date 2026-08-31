/**
 * The manifest-corpus invariants: INDEX.json is the authority for what
 * must be bound, and this suite makes the authority enforcing.
 *
 * - The index names exactly the committed family manifests — an orphan
 *   file or a missing named file is red.
 * - Every named family decodes through one closed envelope at the model
 *   version the index declares, with non-empty rows, unique case ids, in
 *   canonical ascending order.
 * - Every family is either BOUND (a suite consumes its rows) or declared
 *   LEADING (vectors precede the implementation, with the packet item
 *   that will bind them named). A family in neither state is red — a
 *   model-side addition can never be a silent gap.
 */
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem, Schema } from "effect"
import { layerDiskFs } from "../fixtures/diskFs.ts"
import { ManifestModel, ManifestReadError, manifestIndexNames } from "./harness.ts"

const manifestPath = "archive/lean-model-0.3/conformance/manifest"

const RowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Unknown,
  input: Schema.Unknown,
})

const FamilyDocSchema = Schema.Struct({
  family: Schema.String,
  meaning: Schema.String,
  model: Schema.Literal(ManifestModel),
  oracle: Schema.optionalKey(Schema.String),
  rows: Schema.Array(RowSchema),
})

type Binding =
  | { readonly status: "bound"; readonly by: string }
  | { readonly status: "leads"; readonly until: string }

/** Every consumable family, bound to its consuming suite or declared
 * leading with the packet item that will bind it. */
const REGISTRY: Record<string, Binding> = {
  "CAS-001": { status: "bound", by: "CasStore.test.ts" },
  "CAS-002": { status: "bound", by: "CasStore.test.ts" },
  "CAS-004": { status: "bound", by: "CasValueJson.test.ts" },
  "CMP-002": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "MRK-001": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-002": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-003": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-005": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-006": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-007": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-011": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-012": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-014": { status: "bound", by: "blob/Blob.test.ts" },
  "MRK-015": { status: "bound", by: "archive/remote-plane/test/merkle/Merkle.test.ts" },
  "MRK-018": { status: "bound", by: "blob/Blob.test.ts" },
  "MRK-020": {
    status: "leads",
    until: "optimization packet follow-up — bind the read planner's access set through a load-counting store after the shared read plan lands",
  },
  "RMT-001": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-002": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-003": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-004": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-005": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-006": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-007": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-008": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-014": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-015": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RMT-017": { status: "bound", by: "archive/remote-plane/test/remote/Machine.test.ts" },
  "RPL-002": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "RPL-003": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "RPL-004": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "RPL-005": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "SES-001": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "SES-002": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "SES-003": { status: "bound", by: "archive/replay-plane/test/ReplayReducer.test.ts" },
  "SRV-001": { status: "bound", by: "server/ServerConformance.test.ts" },
}

it.effect("the index names exactly the committed family manifests", () =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const entries = yield* fs.readDirectory(manifestPath).pipe(Effect.orDie)
    const committed = entries
      .filter((name) => name.endsWith(".json") && name !== "INDEX.json")
      .sort()
    expect([...manifestIndexNames]).toEqual(committed)
    // The index itself is canonically sorted.
    expect([...manifestIndexNames]).toEqual([...manifestIndexNames].sort())
  }).pipe(Effect.provide(layerDiskFs)))

it.effect.each([...manifestIndexNames])(
  "family %s decodes through the closed envelope at the declared model",
  (name) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const text = yield* fs.readFileString(`${manifestPath}/${name}`).pipe(Effect.orDie)
      const decoded = yield* Schema.decodeUnknownEffect(FamilyDocSchema)(
        JSON.parse(text),
        { onExcessProperty: "error" },
      ).pipe(Effect.mapError((issue) =>
        new ManifestReadError({ cause: `${name}: ${String(issue)}` })))
      expect({ name, family: decoded.family }).toEqual({
        name,
        family: name.replace(/\.json$/, ""),
      })
      expect({ name, rows: decoded.rows.length > 0 }).toEqual({
        name,
        rows: true,
      })
      const ids = decoded.rows.map((row) => row.case)
      const canonical = [...ids].sort()
      expect({ name, ids }).toEqual({ name, ids: canonical })
      expect({ name, unique: new Set(ids).size }).toEqual({
        name,
        unique: ids.length,
      })
    }).pipe(Effect.provide(layerDiskFs)),
)

it.effect("the binding registry covers the index exactly", () =>
  Effect.sync(() => {
    const families = manifestIndexNames.map((name) => name.replace(/\.json$/, ""))
    expect(Object.keys(REGISTRY).sort()).toEqual([...families].sort())
  }))

it.effect.each(manifestIndexNames.map((name) => name.replace(/\.json$/, "")))(
  "family %s is bound to a suite or declared leading — never a silent gap",
  (family) =>
    Effect.gen(function* () {
      const binding = REGISTRY[family]
      if (binding === undefined) {
        return yield* Effect.die(new Error(`${family}: no binding declared`))
      }
      if (binding.status === "leads") {
        expect({ family, until: binding.until.length > 0 }).toEqual({
          family,
          until: true,
        })
      }
    }),
)
