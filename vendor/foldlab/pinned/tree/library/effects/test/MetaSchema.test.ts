/**
 * THE INTERPRETER, exercised: `toEffectSchema` over the emitted AST.
 *
 * Three things are checked, and they are different claims.
 *
 * - GREEN over the real artifacts. Every document the plane describes
 *   decodes through the schema built from its own emitted term —
 *   against the files the emitters actually wrote, in THIS checkout,
 *   reached through the manifest's rows rather than through a list
 *   typed here. So this suite goes red when an emitter's output and
 *   the shape it claims to have stop agreeing, which is the whole
 *   point of the cutover.
 * - REFUSAL, one drill per shape family. A meta document that has
 *   drifted must REFUSE and name the path, never coerce: `"3"` is not
 *   a `nat`, `"true"` is not a `bool`, a spelling outside an `enum` is
 *   not in it, and an unknown key is a defect rather than a field to
 *   drop. `opt` gets its own drill because "may be absent" must not
 *   quietly mean "may be anything".
 * - EXHAUSTIVENESS. `oneOfEach` is a `satisfies` over the union's tag
 *   set: a constructor added in Lean makes it miss a key, which is a
 *   red build here — in the same build where `toEffectSchema`'s
 *   `absurd` arm goes red.
 */
import { describe, expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer, Option, Path, Schema, Scope } from "effect"
import { describedLedgers, findLabRoot, readLabLedgers, readLedger } from "../bin/cli/ledgers.ts"
import {
  closedDecoding,
  decodeMetaArtifact,
  decodeMetaManifest,
  describedShapes,
  shapeForSchemaRef,
  toEffectSchema,
  type MetaSchema,
} from "../src/cas/MetaSchema.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"

/** Disk, plus the path service the lab walk and the row joins need. */
const layerFiles: Layer.Layer<FileSystem.FileSystem | Path.Path> = Layer.merge(
  layerDiskFs,
  Path.layer,
)

/** THIS checkout, found the way `doctor` finds it. The suite runs with
 * cwd = `library/effects`, so the walk climbs one directory. */
const labRoot: Effect.Effect<string, never, FileSystem.FileSystem | Path.Path> = findLabRoot(
  ".",
).pipe(Effect.map(Option.getOrElse(() => "")))

/* ── green: every described artifact, through its own term ────────── */

describe("the described artifacts decode through their emitted shapes", () => {
  it.effect("every row the manifest describes reads as the shape it names", () =>
    Effect.gen(function* () {
      const root = yield* labRoot
      expect(root, "the suite must run inside a foldlab checkout").not.toBe("")
      const described = yield* describedLedgers(root)
      // The five described rows: the manifest itself, plus axioms,
      // debts, strata and trust. Stated as a count so a row that grows
      // a shape in Lean and no binding here is caught, not absorbed.
      expect(described.map((entry) => entry.stem).toSorted()).toEqual([
        "MANIFEST",
        "axioms",
        "debts",
        "strata",
        "trust",
      ])
      for (const entry of described) {
        const read = yield* readLedger(root, entry)
        expect(read._tag, `${entry.path} did not read as its emitted shape`).toBe("read")
      }
    }).pipe(Effect.provide(layerFiles)))

  it.effect("the grammar's names.json reads too, off the meta plane", () =>
    Effect.gen(function* () {
      // `names.json` is described by the same emitter but lands under
      // `src/cas/generated/grammar/`, outside the meta home — so the
      // manifest carries no row for it and it is named here.
      const text = yield* readFixtureString("src/cas/generated/grammar/names.json")
      const decoded = yield* decodeMetaArtifact(describedShapes.names, text)
      expect(decoded).not.toBe(null)
    }).pipe(Effect.provide(layerDiskFs)))

  it.effect("the manifest's own rows come back projected", () =>
    Effect.gen(function* () {
      const text = yield* readFixtureString("../cas/meta/MANIFEST.META.json")
      const manifest = yield* decodeMetaManifest(text)
      expect(manifest.outputs.length).toBe(9)
      const described = manifest.outputs.filter((row) => row.schema !== undefined)
      const awaiting = manifest.outputs.filter((row) => row.awaiting !== undefined)
      expect(described.length).toBe(5)
      expect(awaiting.length).toBe(4)
      // The two columns are exclusive: a row states a shape or states
      // that it is waiting for one, never both and never neither.
      for (const row of manifest.outputs) {
        expect(
          (row.schema === undefined) !== (row.awaiting === undefined),
          `${row.path} is neither described nor awaiting`,
        ).toBe(true)
      }
      // Every described row's reference places to a term this
      // interpreter holds — an unplaceable one would leave a described
      // artifact unchecked.
      for (const row of described) {
        expect(Option.isSome(shapeForSchemaRef(row.schema ?? "")), `${row.path}`).toBe(true)
      }
    }).pipe(Effect.provide(layerDiskFs)))
})

/* ── refusal: one drill per shape family ─────────────────────────── */

/** What the decode SAID when it refused — or a sentinel, so a drill
 * that decodes when it should have refused fails on its own message
 * rather than on a missing error. */
const refusalOf = (shape: MetaSchema, input: unknown): Effect.Effect<string> =>
  Schema.decodeUnknownEffect(toEffectSchema(shape), closedDecoding)(input).pipe(
    Effect.flip,
    Effect.map((error) => error.message),
    Effect.orElseSucceed(() => "DECODED — the drill was coerced, not refused"),
  )

/** A record of one field, so every leaf drill can assert a PATH. */
const fieldOf = (schema: MetaSchema): MetaSchema => ({
  _tag: "record",
  fields: [{ name: "leaf", schema }],
})

describe("a drifted document refuses, and names where", () => {
  it.effect("str: a number is not coerced to a string", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "str" }), { leaf: 7 }),
      (said) => {
        expect(said).toContain("Expected string")
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("nat: a negative integer is refused at its path", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "nat" }), { leaf: -1 }),
      (said) => {
        expect(said).toContain("greater than or equal to 0")
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("nat: a fraction is not an integer", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "nat" }), { leaf: 1.5 }),
      (said) => {
        expect(said).toContain("integer")
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("bool: the string \"true\" is not true", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "bool" }), { leaf: "true" }),
      (said) => {
        expect(said).toContain("Expected boolean")
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("enum: a spelling outside the set is not in it", () =>
    Effect.map(
      refusalOf(
        fieldOf({ _tag: "enum", values: ["owed", "parked"] }),
        { leaf: "settled" },
      ),
      (said) => {
        expect(said).toContain(`"owed"`)
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("array: a bad element is refused at its INDEX", () =>
    Effect.map(
      refusalOf(
        fieldOf({ _tag: "array", items: { _tag: "str" } }),
        { leaf: ["a", "b", 3] },
      ),
      (said) => {
        expect(said).toContain("Expected string")
        expect(said).toContain(`at ["leaf"][2]`)
      },
    ))

  it.effect("record: a required field that is gone is a missing key", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "str" }), {}),
      (said) => {
        expect(said).toContain("Missing key")
        expect(said).toContain(`at ["leaf"]`)
      },
    ))

  it.effect("record: an unknown key is a refusal, not a dropped field", () =>
    Effect.map(
      refusalOf(fieldOf({ _tag: "str" }), { leaf: "a", stowaway: 1 }),
      (said) => {
        expect(said).toContain("no excess property")
        expect(said).toContain(`at ["stowaway"]`)
      },
    ))

  it.effect("opt: absent is fine, and present-but-wrong is still refused", () =>
    Effect.gen(function* () {
      const shape: MetaSchema = {
        _tag: "record",
        fields: [{ name: "leaf", schema: { _tag: "opt", inner: { _tag: "nat" } } }],
      }
      const absent = yield* Schema.decodeUnknownEffect(toEffectSchema(shape), closedDecoding)({})
      expect(absent).toEqual({})
      const said = yield* refusalOf(shape, { leaf: "seven" })
      expect(said).toContain(`at ["leaf"]`)
    }))

  it.effect("nested: the path names every step down to the leaf", () =>
    Effect.map(
      refusalOf(
        {
          _tag: "record",
          fields: [{
            name: "rows",
            schema: { _tag: "array", items: fieldOf({ _tag: "nat" }) },
          }],
        },
        { rows: [{ leaf: 1 }, { leaf: "two" }] },
      ),
      (said) => {
        expect(said).toContain(`at ["rows"][1]["leaf"]`)
      },
    ))
})

/* ── refusal, on the real manifest ───────────────────────────────── */

describe("the real manifest refuses when it drifts", () => {
  it.effect("a renamed top-level field is a missing key AND an excess one", () =>
    Effect.gen(function* () {
      const text = yield* readFixtureString("../cas/meta/MANIFEST.META.json")
      // String surgery rather than a re-print: the drill is about the
      // decoder, and nothing in this estate hand-spells JSON.
      const drifted = text.replace(`"outputs": [`, `"outputz": [`)
      expect(drifted, "the surgery must actually change the document").not.toBe(text)
      const refusal = yield* Effect.flip(
        decodeMetaArtifact(describedShapes.manifest, drifted),
      )
      expect(refusal.artifact).toBe("MANIFEST.META.json")
      expect(refusal.reason).toContain(`at ["outputs"]`)
      expect(refusal.reason).toContain(`at ["outputz"]`)
      // The rendered words carry the artifact and the repair.
      expect(refusal.message).toContain("MANIFEST.META.json is not the shape")
      expect(refusal.message).toContain("lake exe emitmeta")
    }).pipe(Effect.provide(layerDiskFs)))

  it.effect("a nat that went negative is refused deep in the header", () =>
    Effect.gen(function* () {
      const text = yield* readFixtureString("../cas/meta/MANIFEST.META.json")
      const drifted = text.replace(`"schemaVersion": 1`, `"schemaVersion": -1`)
      expect(drifted).not.toBe(text)
      const refusal = yield* Effect.flip(
        decodeMetaArtifact(describedShapes.manifest, drifted),
      )
      expect(refusal.reason).toContain(`at ["emitted"]["schemaVersion"]`)
    }).pipe(Effect.provide(layerDiskFs)))

  it.effect("text that is not JSON refuses as the same clause", () =>
    Effect.map(
      Effect.flip(decodeMetaArtifact(describedShapes.manifest, "{ not json")),
      (refusal) => {
        expect(refusal.artifact).toBe("MANIFEST.META.json")
        expect(refusal.reason).toContain("JSON")
      },
    ))
})

/* ── the registry, when it will not answer ───────────────────────── */

describe("a lab whose registry will not answer", () => {
  /** A checkout-shaped directory: the lab marker, one real ledger, and
   * whatever manifest the case wants. */
  const fakeLab = (
    manifest: Option.Option<string>,
  ): Effect.Effect<string, unknown, FileSystem.FileSystem | Path.Path | Scope.Scope> =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const path = yield* Path.Path
      const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-meta-lab-" })
      yield* fs.makeDirectory(path.join(root, "library", "cas", "meta", "out"), {
        recursive: true,
      })
      yield* fs.writeFileString(
        path.join(root, "library", "cas", "meta", "out", "laws.META.json"),
        yield* readFixtureString("../cas/meta/out/laws.META.json"),
      )
      if (Option.isSome(manifest)) {
        yield* fs.writeFileString(
          path.join(root, "library", "cas", "meta", "MANIFEST.META.json"),
          manifest.value,
        )
      }
      return root
    })

  it.effect("no registry: every meta ledger is unreadable AT THE MANIFEST", () =>
    Effect.scoped(Effect.gen(function* () {
      const root = yield* fakeLab(Option.none())
      const read = yield* readLabLedgers(root)
      for (const ledger of [read.environment, read.laws, read.obligations]) {
        expect(ledger._tag).toBe("unreadable")
        if (ledger._tag === "unreadable") {
          expect(ledger.path).toContain("MANIFEST.META.json")
          expect(ledger.reason).toContain("is not there")
          // ONE LINE per ledger: `doctor` gives each a row, and a
          // reason with a newline in it would break the block.
          expect(ledger.reason).not.toContain("\n")
        }
      }
      // The admission map is on another plane and answers regardless.
      expect(read.admissionMap._tag).toBe("absent")
    })).pipe(Effect.provide(layerFiles)))

  it.effect("a drifted registry refuses, naming the paths, still on one line", () =>
    Effect.scoped(Effect.gen(function* () {
      const text = yield* readFixtureString("../cas/meta/MANIFEST.META.json")
      const root = yield* fakeLab(Option.some(text.replace(`"outputs": [`, `"outputz": [`)))
      const read = yield* readLabLedgers(root)
      expect(read.laws._tag).toBe("unreadable")
      if (read.laws._tag === "unreadable") {
        expect(read.laws.reason).toContain("does not decode")
        expect(read.laws.reason).toContain(`at ["outputs"]`)
        expect(read.laws.reason).not.toContain("\n")
      }
    })).pipe(Effect.provide(layerFiles)))

  it.effect("a registry that answers places the ledger it carries a row for", () =>
    Effect.scoped(Effect.gen(function* () {
      const text = yield* readFixtureString("../cas/meta/MANIFEST.META.json")
      const root = yield* fakeLab(Option.some(text))
      const read = yield* readLabLedgers(root)
      // The one ledger written into the fake lab reads; the two that
      // were not written are ABSENT, not unreadable — the registry
      // placed them and the emitter simply had not run.
      expect(read.laws._tag).toBe("read")
      expect(read.environment._tag).toBe("absent")
      expect(read.obligations._tag).toBe("absent")
    })).pipe(Effect.provide(layerFiles)))
})

/* ── the exhaustiveness canary ───────────────────────────────────── */

/**
 * ONE VALUE PER CONSTRUCTOR, keyed by the union's own tags.
 *
 * `satisfies Record<MetaSchema["_tag"], …>` is the canary: a
 * constructor added in Lean lands in the emitted union, this record
 * stops covering it, and the build goes red HERE — in the same build
 * where `toEffectSchema`'s `absurd` arm goes red. A tag removed in
 * Lean reds it from the other side.
 */
const oneOfEach = {
  array: { _tag: "array", items: { _tag: "str" } },
  bool: { _tag: "bool" },
  enum: { _tag: "enum", values: ["yes", "no"] },
  nat: { _tag: "nat" },
  opt: { _tag: "opt", inner: { _tag: "str" } },
  record: { _tag: "record", fields: [{ name: "leaf", schema: { _tag: "str" } }] },
  str: { _tag: "str" },
} satisfies Record<MetaSchema["_tag"], MetaSchema>

/** What each constructor admits, so the canary is a live check and
 * not only a type-level one. */
const admits: Record<MetaSchema["_tag"], unknown> = {
  array: ["a"],
  bool: true,
  enum: "yes",
  nat: 0,
  opt: undefined,
  record: { leaf: "a" },
  str: "a",
}

describe("the interpreter covers the whole union", () => {
  it.effect("every constructor builds a schema that decodes its own value", () =>
    Effect.forEach(
      Object.entries(oneOfEach),
      ([tag, shape]) =>
        Schema.decodeUnknownEffect(toEffectSchema(shape), closedDecoding)(
          admits[tag as MetaSchema["_tag"]],
        ).pipe(
          Effect.map((decoded) => {
            expect(decoded, `${tag} did not decode the value it admits`).toEqual(
              admits[tag as MetaSchema["_tag"]],
            )
          }),
        ),
    ))

  it.effect("the union has exactly the seven constructors the plane emitted", () =>
    Effect.sync(() => {
      expect(Object.keys(oneOfEach).toSorted()).toEqual([
        "array",
        "bool",
        "enum",
        "nat",
        "opt",
        "record",
        "str",
      ])
    }))
})
