/**
 * The file backend: the byte-plane seams over one store root, written
 * entirely against Effect's `FileSystem` service — no platform reach
 * anywhere. The composition chooses the realization by providing a
 * `FileSystem` layer; this module only speaks the service.
 *
 * On-disk contract:
 *
 *     store-root/
 *       objects/<first 2 hex>/<remaining 62 hex>   canonical bytes
 *       roots/<64 hex>                             empty file; presence
 *                                                  is the publication
 *
 * The address is the path, so presence is an existence check and the
 * filesystem is the map — no index file, no manifest. Writes publish by
 * temp-file-then-hard-link: a crashed write leaves only a temp file, never
 * a half object, and the link creates the final path atomically without
 * overwriting a concurrent winner. The winner's bytes are compared before
 * a racing or repeated put succeeds. The backend stays dumb: it never
 * verifies bytes on read; the
 * store law above the seam recomputes the digest and re-decodes, so
 * disk corruption surfaces as a typed refusal there. Durability is the
 * host filesystem's default (no fsync); a power cut may lose the newest
 * objects but cannot corrupt admitted ones.
 */
import {
  Context,
  Effect,
  FileSystem,
  Layer,
  Option,
  Path,
  PlatformError,
  Schema,
} from "effect"
import {
  BackendFailure,
  ByteReader,
  ByteWriter,
  objectRelativePath,
  RootStore,
  type ByteReaderShape,
  type ByteWriterShape,
  type PresenceStatus,
  type RootStoreShape,
} from "./Backend.ts"
import { ContentId } from "./Node.ts"
import { bytesEqual } from "../internal/bytes.ts"

/** A store root: the non-empty base path the backend joins with `/`.
 * Validated at every public constructor, branded past validation. */
export const StoreRoot = Schema.String.check(Schema.isMinLength(1)).pipe(
  Schema.brand("StoreRoot"),
)
export type StoreRoot = typeof StoreRoot.Type

const rootHex = /^[0-9a-f]{64}$/u

const isNotFound = (error: PlatformError.PlatformError): boolean =>
  error.reason._tag === "NotFound"

const isAlreadyExists = (error: PlatformError.PlatformError): boolean =>
  error.reason._tag === "AlreadyExists"

const failure = (error: PlatformError.PlatformError): BackendFailure =>
  new BackendFailure({ reason: error.message, cause: error })

/** Normalize caller-supplied roots to one separator vocabulary before any
 * CAS-relative path is appended. Preserve POSIX root and UNC prefixes while
 * removing redundant separators and trailing separators everywhere else. */
export const normalizeStoreRoot = (input: string): StoreRoot => {
  const portable = input.replaceAll("\\", "/")
  const prefix = portable.startsWith("//") ? "//" : portable.startsWith("/") ? "/" : ""
  const body = portable.slice(prefix.length).replaceAll(/\/{2,}/gu, "/")
  const normalized = `${prefix}${body}`
  return StoreRoot.make(normalized === "/" || normalized === "//"
    ? normalized
    : normalized.replace(/\/+$/u, ""))
}

/** Normalize a host path using the supplied Effect Path implementation. */
export const normalizeStoreRootWith = (
  path: Path.Path,
  input: string,
): StoreRoot => {
  const nonEmpty = StoreRoot.make(input)
  let normalized = path.normalize(nonEmpty)
  const filesystemRoot = path.parse(normalized).root
  while (normalized !== filesystemRoot && normalized.endsWith(path.sep)) {
    normalized = normalized.slice(0, -path.sep.length)
  }
  return StoreRoot.make(normalized)
}

/** Resolve a file URL through the host's Effect Path implementation. */
export const storeRootFromFileUrl = (
  url: URL,
): Effect.Effect<StoreRoot, BackendFailure, Path.Path> =>
  Path.Path.pipe(
    Effect.flatMap((path) => path.fromFileUrl(url).pipe(
      Effect.map((root) => normalizeStoreRootWith(path, root)),
    )),
    Effect.mapError((error) => new BackendFailure({
      reason: error.message,
      cause: error,
    })),
  )

/** The scaffold directory a temp file lives in. `makeTempFile` answers
 * `<directory>/<prefix><random>/<file>` — a fresh directory with the
 * file inside — and spells it with the host's separator whatever the
 * caller passed, so both are cut. */
const scaffoldOf = (temp: string): string =>
  temp.slice(0, Math.max(temp.lastIndexOf("/"), temp.lastIndexOf("\\")))

/** Build the three seam shapes over one store root. */
export const makeFileBackend = (
  fs: FileSystem.FileSystem,
  storeRoot: string,
  path?: Path.Path,
) => {
  const root = path === undefined
    ? normalizeStoreRoot(storeRoot)
    : normalizeStoreRootWith(path, storeRoot)
  const underRoot = (relative: string): string =>
    path === undefined
      ? `${root}${root.endsWith("/") ? "" : "/"}${relative}`
      : path.join(root, ...relative.split("/"))
  const objectPath = (id: ContentId): string =>
    underRoot(objectRelativePath(id))
  const fanoutDir = (id: ContentId): string =>
    path === undefined
      ? objectPath(id).slice(0, objectPath(id).lastIndexOf("/"))
      : path.dirname(objectPath(id))
  const rootsDir = underRoot("roots")
  const rootPath = (id: ContentId): string =>
    path === undefined ? `${rootsDir}/${id}` : path.join(rootsDir, id)

  const loadBytes: ByteReaderShape["loadBytes"] = Effect.fn(
    "FileBackend.loadBytes",
  )(function* (id) {
    return yield* fs.readFile(objectPath(id)).pipe(
      Effect.asSome,
      Effect.catchTag("PlatformError", (error) => isNotFound(error)
        ? Effect.succeed(Option.none<Uint8Array>())
        : Effect.fail(failure(error))),
    )
  })

  const presenceOf = (id: ContentId): Effect.Effect<PresenceStatus> =>
    fs.exists(objectPath(id)).pipe(
      Effect.map((resident): PresenceStatus => resident ? "present" : "missing"),
      Effect.catchTag("PlatformError", () =>
        Effect.succeed<PresenceStatus>("failed")),
    )

  const presence: ByteReaderShape["presence"] = Effect.fn(
    "FileBackend.presence",
  )(function* (ids) {
    return yield* Effect.forEach(ids, presenceOf)
  })

  const compareResident = (
    id: ContentId,
    target: string,
    bytes: Uint8Array,
  ): Effect.Effect<void, PlatformError.PlatformError | BackendFailure> =>
    fs.readFile(target).pipe(
      Effect.flatMap((resident) => bytesEqual(resident, bytes)
        ? Effect.void
        : Effect.fail(new BackendFailure({
            reason: `Content identifier collision at ${id}`,
          }))),
    )

  const writeFresh = (id: ContentId, target: string, bytes: Uint8Array) => {
    const directory = fanoutDir(id)
    return fs.makeDirectory(directory, { recursive: true }).pipe(
      Effect.andThen(Effect.acquireUseRelease(
        fs.makeTempFile({ directory, prefix: "put-" }),
        (temp) => fs.writeFile(temp, bytes.slice()).pipe(
          Effect.andThen(fs.link(temp, target).pipe(
            Effect.catchTag("PlatformError", (error) => isAlreadyExists(error)
              ? compareResident(id, target, bytes)
              : Effect.fail(error)),
          )),
        ),
        // The release removes the whole SCAFFOLD, not just the file the
        // platform handed back: a temp file is realized as a fresh
        // directory with the file inside, so removing the file alone
        // leaves one empty directory in the fanout per fresh write. A
        // release that cannot clean up still fails the put rather than
        // reporting a success it did not finish.
        (temp) => fs.remove(scaffoldOf(temp), { recursive: true, force: true }),
      )),
    )
  }

  const putBytes: ByteWriterShape["putBytes"] = Effect.fn(
    "FileBackend.putBytes",
  )(function* (id, bytes) {
    const target = objectPath(id)
    return yield* fs.exists(target).pipe(
      Effect.flatMap((resident) => resident
        ? compareResident(id, target, bytes)
        : writeFresh(id, target, bytes)),
      Effect.catchTag("PlatformError", (error) => Effect.fail(failure(error))),
    )
  })

  const publish: RootStoreShape["publish"] = Effect.fn(
    "FileBackend.publish",
  )(function* (rootId) {
    return yield* fs.makeDirectory(rootsDir, { recursive: true }).pipe(
      Effect.andThen(fs.writeFile(rootPath(rootId), new Uint8Array(0))),
      Effect.catchTag("PlatformError", (error) => Effect.fail(failure(error))),
    )
  })

  const list: RootStoreShape["list"] = fs.readDirectory(rootsDir).pipe(
    Effect.map((entries) => entries
      .filter((entry) => rootHex.test(entry))
      .map((entry) => ContentId.make(entry))),
    Effect.catchTag("PlatformError", (error) => isNotFound(error)
      ? Effect.succeed<ReadonlyArray<ContentId>>([])
      : Effect.fail(failure(error))),
  )

  return {
    reader: { loadBytes, presence },
    writer: { putBytes },
    roots: { publish, list },
  }
}

/** Build a file backend using the host's Effect Path semantics. */
export const makeFileBackendWithPath = (
  fs: FileSystem.FileSystem,
  path: Path.Path,
  storeRoot: string,
) => makeFileBackend(fs, storeRoot, path)

/** Build a file backend from a file URL without ambient URL/path conversion. */
export const makeFileBackendFromFileUrl = (
  fs: FileSystem.FileSystem,
  url: URL,
) => storeRootFromFileUrl(url).pipe(
  Effect.flatMap((root) => Path.Path.pipe(
    Effect.map((path) => makeFileBackendWithPath(fs, path, root)),
  )),
)

/** Provide the three seams from one store root. The `FileSystem`
 * realization is the composition's choice and stays a visible layer
 * requirement. */
export const layerFileBackend = (
  storeRoot: string,
): Layer.Layer<
  ByteReader | ByteWriter | RootStore,
  never,
  FileSystem.FileSystem
> =>
  Layer.effectContext(Effect.map(FileSystem.FileSystem, (fs) => {
    const backend = makeFileBackend(fs, storeRoot)
    return Context.make(ByteReader, backend.reader).pipe(
      Context.add(ByteWriter, backend.writer),
      Context.add(RootStore, backend.roots),
    )
  }))

/** File backend using the host-provided Effect Path implementation. */
export const layerFileBackendWithPath = (
  storeRoot: string,
): Layer.Layer<
  ByteReader | ByteWriter | RootStore,
  never,
  FileSystem.FileSystem | Path.Path
> =>
  Layer.effectContext(Effect.map(
    Effect.all([FileSystem.FileSystem, Path.Path]),
    ([fs, path]) => {
      const backend = makeFileBackendWithPath(fs, path, storeRoot)
      return Context.make(ByteReader, backend.reader).pipe(
        Context.add(ByteWriter, backend.writer),
        Context.add(RootStore, backend.roots),
      )
    },
  ))

/** File backend rooted at a file URL through `Path.fromFileUrl`. */
export const layerFileBackendFromFileUrl = (
  url: URL,
): Layer.Layer<
  ByteReader | ByteWriter | RootStore,
  BackendFailure,
  FileSystem.FileSystem | Path.Path
> => Layer.effectContext(Effect.gen(function* () {
  const fs = yield* FileSystem.FileSystem
  const path = yield* Path.Path
  const root = yield* path.fromFileUrl(url).pipe(
    Effect.mapError((error) => new BackendFailure({
      reason: error.message,
      cause: error,
    })),
  )
  const backend = makeFileBackendWithPath(fs, path, root)
  return Context.make(ByteReader, backend.reader).pipe(
    Context.add(ByteWriter, backend.writer),
    Context.add(RootStore, backend.roots),
  )
}))
