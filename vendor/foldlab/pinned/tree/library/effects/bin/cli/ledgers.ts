/**
 * The emitted ledgers, read at runtime.
 *
 * Four documents land in this estate from Lean emitters, and until now
 * every one of them was reachable only through a `mise` or `lake` gate:
 * agent-readable JSON with no runtime reader (CLI audit §1). This
 * module is that reader, and `cas doctor` is its consumer.
 *
 * ## Where a ledger LIVES is not this file's opinion
 *
 * The meta plane keeps its own registry — `MANIFEST.META.json`, one row
 * per emitted artifact — and since the D2 cutover this reader takes
 * every meta-plane path from it rather than repeating the strings. The
 * manifest is itself a described artifact, so it is decoded through
 * `toEffectSchema` of its emitted AST value: the plane says where its
 * documents are, in a document whose own shape the plane states.
 *
 * A row that the registry does not carry is a REFUSAL naming the
 * manifest, not a guess at a path.
 *
 * ## What is read, and what is NOT
 *
 * Only counters and headline facts — the numbers each emitter already
 * computed and wrote down. Nothing here re-derives a count, re-judges a
 * row, or restates a proof: a ledger says what it says, and this verb's
 * job is to say it out loud.
 *
 * An artifact whose SHAPE the plane states is read through that shape
 * and nothing else — `describedLedgers` builds the schema by
 * interpreting the emitted AST value, so no hand-written schema for a
 * described artifact can exist here. Every ledger `doctor` reports is
 * one the plane has NOT yet described (its manifest row says
 * `awaiting`) or one that is not on the plane at all, so each keeps the
 * hand reader below with its awaiting row named.
 *
 * Those hand structs are open, so an emitter is free to grow a field
 * without this reader noticing, and every field this reader does want
 * is optional, so an emitter is free to drop one without the whole
 * checkup refusing — `doctor` prints a dash for a counter that was not
 * there. What a schema still catches is a field that has changed
 * SHAPE, and that is exactly the drift worth hearing about: it comes
 * back as `unreadable`, naming the file.
 *
 * ## Where they live
 *
 * In the REPOSITORY, not in the store. A store is a directory of bytes
 * and can sit anywhere; the ledgers are the lab's paperwork about the
 * language the store speaks. So they are found by walking up for the
 * repository layout, and a store outside a checkout simply has none —
 * which `doctor` says, rather than reporting zeros.
 */
import { Effect, FileSystem, Option, Path, PlatformError, Predicate, Schema } from "effect"
import {
  decodeMetaManifest,
  MetaArtifactRefused,
  shapeForRow,
  toEffectSchema,
  type MetaCodec,
  type MetaOutputRow,
} from "../../src/cas/MetaSchema.ts"

/** A counter an emitter may or may not have written. Absent is a real
 * answer here and is kept distinct from zero all the way to the
 * rendering — a ledger that did not say must never read as a ledger
 * that said none. */
const count = Schema.optionalKey(Schema.Finite)

/** A list of names an emitter may or may not have written. */
const names = Schema.optionalKey(Schema.Array(Schema.String))

/** A list whose LENGTH is the fact, not its contents. The members are
 * left undescribed on purpose: this reader counts rows, and describing
 * their shape would be this package taking on an emitter's schema it
 * has no use for. */
const rows = Schema.optionalKey(Schema.Array(Schema.Unknown))

/**
 * `environment.META.json` — which Lean toolchains this estate pins, how
 * many gates are held out of the gate set, and how big the task and
 * executable tables are.
 *
 * HAND-READ because the plane does not describe it: its manifest row
 * is `awaiting` — "the configuration-plane ledger; no MetaSchema
 * declared yet". When that row grows a `schema`, this struct goes and
 * `toEffectSchema` of the emitted term takes its place.
 */
export const EnvironmentLedger = Schema.Struct({
  distinctPins: names,
  excludedGates: names,
  leanExes: rows,
  tasks: rows,
})

/**
 * `laws.META.json` — how many rulings the library states, and how many
 * are bound to an enforcing declaration rather than owed.
 *
 * HAND-READ because the plane does not describe it: its manifest row
 * is `awaiting` — "the ruling/LAW-line join; no MetaSchema declared
 * yet".
 */
export const LawLedger = Schema.Struct({
  counters: Schema.optionalKey(Schema.Struct({
    bound: count,
    owed: count,
    rulings: count,
    superseded: count,
  })),
})

/**
 * `obligations.META.json` — what the proof effort has discharged, and
 * what it still owes.
 *
 * HAND-READ because the plane does not describe it: its manifest row
 * is `awaiting` — "the named-obligation ledger; no MetaSchema declared
 * yet".
 *
 * The plane's fourth awaiting row, `surface.META.json` ("the
 * per-declaration signature ledger; no MetaSchema declared yet"), has
 * no reader here at all — `bin/mcp/http.ts` serves its bytes and
 * `doctor` does not report it.
 */
export const ObligationLedger = Schema.Struct({
  counters: Schema.optionalKey(Schema.Struct({
    discharged: count,
    owed: count,
    parked: count,
    pinPending: count,
  })),
})

/**
 * `library/cas/conformance/admission-map.json` — of the carrier's rows,
 * how many this estate admits, defers, and rejects.
 *
 * NOT A META-PLANE ARTIFACT: it lives under `library/cas/conformance`,
 * outside the manifest's home, so the plane's registry has no row for
 * it and its path below stays written out. Hand-read for the same
 * reason — there is no emitted shape to interpret.
 */
export const AdmissionLedger = Schema.Struct({
  counts: Schema.optionalKey(Schema.Struct({
    admitted: count,
    deferred: count,
    rejected: count,
    rows: count,
  })),
})

export type EnvironmentLedger = typeof EnvironmentLedger.Type
export type LawLedger = typeof LawLedger.Type
export type ObligationLedger = typeof ObligationLedger.Type
export type AdmissionLedger = typeof AdmissionLedger.Type

/** The one ledger the meta plane's registry does not carry: it belongs
 * to the conformance plane, so its path is written here because there
 * is nowhere else it could come from. */
export const admissionMap = {
  path: "library/cas/conformance/admission-map.json",
  schema: AdmissionLedger,
}

/** The directory a ledger path is resolved against — how the lab is
 * recognized from inside it. `library/cas/meta/out` is the marker
 * because it is the directory the ledger emitters write into, so a
 * checkout that has it is a checkout that can have ledgers at all. */
const labMarker = "library/cas/meta/out"

/** Find the repository the ledgers live in: the nearest ancestor of a
 * starting directory that carries the lab's layout. Answers none when
 * there is no such ancestor — a store outside a checkout. */
export const findLabRoot = (
  start: string,
): Effect.Effect<Option.Option<string>, never, FileSystem.FileSystem | Path.Path> => {
  const walkUp = (
    fs: FileSystem.FileSystem,
    path: Path.Path,
    current: string,
  ): Effect.Effect<Option.Option<string>> =>
    fs.exists(path.join(current, labMarker)).pipe(
      Effect.orElseSucceed(() => false),
      Effect.flatMap((marked) => {
        if (marked) return Effect.succeedSome(current)
        const parent = path.dirname(current)
        return parent === current
          ? Effect.succeedNone
          : walkUp(fs, path, parent)
      }),
    )
  return Effect.flatMap(FileSystem.FileSystem, (fs) =>
    Effect.flatMap(Path.Path, (path) => walkUp(fs, path, path.resolve(start))))
}

/**
 * How a ledger answered.
 *
 * The three states stay apart because they call for different repairs:
 * an emitter that has not run is `absent`, one whose output no longer
 * decodes is `unreadable` and names why, and one that answered is
 * `read` and carries its facts. A checkup that blurred them into a
 * missing number would be no use to the person holding it.
 */
export type LedgerRead<A> =
  | { readonly _tag: "read"; readonly path: string; readonly facts: A }
  | { readonly _tag: "absent"; readonly path: string }
  | { readonly _tag: "unreadable"; readonly path: string; readonly reason: string }

/** The three answers, as constructors — so each is built once, by
 * name, and the union's tags are never spelled inline. */
const wasRead = <A>(path: string, facts: A): LedgerRead<A> => ({ _tag: "read", facts, path })
const wasAbsent = <A>(path: string): LedgerRead<A> => ({ _tag: "absent", path })
const wasUnreadable = <A>(path: string, reason: string): LedgerRead<A> => ({
  _tag: "unreadable",
  path,
  reason,
})

/** Read one ledger under a lab root, through its own schema. Never
 * fails: an unreadable ledger is a finding to report, not a reason to
 * refuse the checkup. */
export const readLedger = <A>(
  labRoot: string,
  ledger: { readonly path: string; readonly schema: Schema.Codec<A, unknown, never, never> },
): Effect.Effect<LedgerRead<A>, never, FileSystem.FileSystem | Path.Path> =>
  Effect.flatMap(FileSystem.FileSystem, (fs) =>
    Effect.flatMap(Path.Path, (path) => {
      const full = path.join(labRoot, ledger.path)
      // The described JSON codec, not the global parser: nothing in
      // this estate spells JSON itself, and the schema is what turns
      // the text into the handful of fields this reader reports. The
      // two rescues are ordered so each names its own state: a decode
      // that fails is `unreadable`, and only a read that fails —
      // caught last, around everything — is `absent`.
      return fs.readFileString(full).pipe(
        Effect.flatMap((raw) =>
          Schema.decodeUnknownEffect(Schema.fromJsonString(ledger.schema))(raw).pipe(
            Effect.map((facts) => wasRead(full, facts)),
            Effect.orElseSucceed(() =>
              wasUnreadable<A>(full, "the file no longer reads as the ledger this build expects")
            ),
          )
        ),
        Effect.orElseSucceed(() => wasAbsent<A>(full)),
      )
    }))

/* ── the plane's registry, read ──────────────────────────────────── */

/** `MANIFEST.META.json` relative to a lab root. The one meta-plane path
 * still written out, and it has to be: it is the document that says
 * where the others are, and a registry cannot look up its own address.
 * (It carries a row for itself all the same, which is how it stays a
 * citizen of the plane it registers.) */
export const metaManifestPath = "library/cas/meta/MANIFEST.META.json"

/** The artifact a manifest row names: the basename up to its first
 * dot, so `library/cas/meta/out/laws.META.json` is `laws` and the
 * `.META.` infix that marks self-description falls away with the
 * extension. The manifest keys its rows by PATH — where a document
 * lives — and a reader asks for one by what it IS. */
const stemOf = (path: string): string => {
  const file = path.slice(path.lastIndexOf("/") + 1)
  const dot = file.indexOf(".")
  return dot === -1 ? file : file.slice(0, dot)
}

/**
 * THE PLANE'S REGISTRY, read under a lab root: every artifact the meta
 * plane emits, by stem.
 *
 * Decoded through the interpreter, so the manifest is held to the same
 * emitted shape it holds everything else to — and a manifest that has
 * drifted refuses HERE, naming the offending path, rather than
 * silently handing back a registry of `undefined`. A registry that is
 * not there at all fails in its own clause, because it is a different
 * finding and calls for a different repair.
 */
export const metaRegistry = (
  labRoot: string,
): Effect.Effect<
  ReadonlyMap<string, MetaOutputRow>,
  MetaArtifactRefused | PlatformError.PlatformError,
  FileSystem.FileSystem | Path.Path
> =>
  Effect.flatMap(FileSystem.FileSystem, (fs) =>
    Effect.flatMap(Path.Path, (path) =>
      // A registry that is NOT THERE and one that no longer DECODES
      // stay apart in the error channel, because they are different
      // findings: the first is an emitter that has not run, the second
      // is a document and its emitted shape disagreeing.
      fs.readFileString(path.join(labRoot, metaManifestPath)).pipe(
        Effect.flatMap(decodeMetaManifest),
        Effect.map((manifest) =>
          new Map(manifest.outputs.map((row) => [stemOf(row.path), row]))),
      )))

/** One described artifact as a reader takes it: where it lives, and
 * the schema INTERPRETED FROM ITS EMITTED AST VALUE. */
export interface DescribedLedger {
  readonly stem: string
  readonly path: string
  readonly schema: MetaCodec
}

/**
 * Every artifact whose SHAPE the plane states, with that shape built.
 *
 * This is the cutover's law in one function: a described artifact is
 * reachable only through `toEffectSchema` of the term the emitter
 * wrote, so there is no seam here where a hand-written schema for a
 * described document could be introduced. A row the registry calls
 * `awaiting` is absent from this list by construction, and so is one
 * whose schema reference the interpreter cannot place — the latter
 * being how a shape Lean describes but this build does not know stays
 * visibly unread instead of quietly unchecked.
 */
export const describedLedgers = (
  labRoot: string,
): Effect.Effect<
  ReadonlyArray<DescribedLedger>,
  MetaArtifactRefused | PlatformError.PlatformError,
  FileSystem.FileSystem | Path.Path
> =>
  Effect.map(metaRegistry(labRoot), (registry) =>
    [...registry].flatMap(([stem, row]) =>
      Option.match(shapeForRow(row), {
        onNone: (): ReadonlyArray<DescribedLedger> => [],
        onSome: (shape) => [{ path: row.path, schema: toEffectSchema(shape.ast), stem }],
      })))

/** The ledgers `doctor` reports, each in whichever of the three states
 * it answered in. */
export interface LabLedgers {
  readonly admissionMap: LedgerRead<AdmissionLedger>
  readonly environment: LedgerRead<EnvironmentLedger>
  readonly laws: LedgerRead<LawLedger>
  readonly obligations: LedgerRead<ObligationLedger>
}

/** Read a meta-plane ledger whose PATH comes from the registry. A stem
 * the registry does not carry is `unreadable` AT THE MANIFEST, because
 * that is the document that is wrong — the ledger itself may be
 * perfectly fine and simply unregistered. */
const readRegistered = <A>(
  labRoot: string,
  manifest: string,
  registry: ReadonlyMap<string, MetaOutputRow>,
  stem: string,
  schema: Schema.Codec<A, unknown, never, never>,
): Effect.Effect<LedgerRead<A>, never, FileSystem.FileSystem | Path.Path> => {
  const row = registry.get(stem)
  return row === undefined
    ? Effect.succeed(
      wasUnreadable<A>(manifest, `the plane's registry carries no row for ${stem}`),
    )
    : readLedger(labRoot, { path: row.path, schema })
}

/** Why the registry could not place a ledger, as ONE line — `doctor`
 * gives each ledger a line, and a decode refusal names as many paths
 * as have drifted. Absent and undecodable stay apart in the words for
 * the same reason they stay apart everywhere else here: they call for
 * different repairs. */
const registryReason = (
  error: MetaArtifactRefused | PlatformError.PlatformError,
): string =>
  Predicate.isTagged(error, "meta/ArtifactRefused")
    ? `the plane's registry does not decode — ${
      error.reason.split("\n").map((line) => line.trim()).join(" · ")
    }`
    : "the plane's registry is not there, so nothing says where this ledger lives"

/**
 * THE CHECKUP'S READ: all four ledgers, the meta-plane three placed by
 * the registry and the admission map by the conformance plane's own
 * path.
 *
 * Never fails. The admission map is read whatever the registry says —
 * it is not on that plane — and a registry that will not answer turns
 * the three meta-plane ledgers `unreadable` AT THE MANIFEST, which
 * keeps `doctor`'s three states doing the work they already do rather
 * than adding a fourth.
 */
export const readLabLedgers = (
  labRoot: string,
): Effect.Effect<LabLedgers, never, FileSystem.FileSystem | Path.Path> =>
  Effect.flatMap(Path.Path, (path) => {
    const manifest = path.join(labRoot, metaManifestPath)
    return Effect.map(
      Effect.all({
        admissionMap: readLedger(labRoot, admissionMap),
        meta: metaRegistry(labRoot).pipe(
          Effect.flatMap((registry) =>
            Effect.all({
              environment: readRegistered(
                labRoot,
                manifest,
                registry,
                "environment",
                EnvironmentLedger,
              ),
              laws: readRegistered(labRoot, manifest, registry, "laws", LawLedger),
              obligations: readRegistered(
                labRoot,
                manifest,
                registry,
                "obligations",
                ObligationLedger,
              ),
            })
          ),
          Effect.catch((error) => {
            const said = registryReason(error)
            return Effect.succeed({
              environment: wasUnreadable<EnvironmentLedger>(manifest, said),
              laws: wasUnreadable<LawLedger>(manifest, said),
              obligations: wasUnreadable<ObligationLedger>(manifest, said),
            })
          }),
        ),
      }),
      ({ admissionMap: admission, meta }) => ({ admissionMap: admission, ...meta }),
    )
  })

/** A counter as `doctor` states it: the number an emitter wrote, or
 * absent. `undefined` is turned into `null` here rather than at every
 * rendering, so the machine register never carries a missing key where
 * a stated absence belongs. */
export const stated = (value: number | undefined): number | null => value ?? null
