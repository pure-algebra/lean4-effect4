/**
 * The path-reader backend: a read-only byte plane over any host that
 * serves bytes at a path — a git server's raw endpoint, an object
 * store, a static file host, another process's store root. The caller
 * supplies the one capability the backend needs, `ReadPath`; nothing
 * here knows what a URL is.
 *
 * It reads the same store-root layout the file backend writes
 * (`objects/<2 hex>/<62 hex>`), so publishing a CAS is committing a
 * directory. The host is untrusted by construction: the store law
 * above the seam recomputes the digest and re-decodes canonically on
 * every read, so a hostile or corrupted host surfaces as a typed
 * refusal, never as silently served bytes.
 *
 * Read-only is a type-level fact: this module provides `ByteReader`
 * and nothing else — writing over a path-reader composition is a
 * compile error, not a runtime refusal.
 */
import { Effect, Layer, Option, Schema } from "effect"
import {
  BackendFailure,
  ByteReader,
  objectRelativePath,
  type ByteReaderShape,
  type PresenceStatus,
} from "./Backend.ts"
import type { ContentId } from "./Node.ts"

/** A host that could not serve a path. `reason` is transport-shaped
 * prose; absence is NOT an error — an absent path answers `None`. */
export class PathReadError extends Schema.TaggedError<PathReadError>()(
  "CasPathReadError",
  { path: Schema.String, reason: Schema.String },
) {}

/** The supplied capability: bytes at a store-root-relative path.
 * Absent paths answer `None`; only a host that cannot answer fails. */
export type ReadPath = (
  relativePath: string,
) => Effect.Effect<Option.Option<Uint8Array>, PathReadError>

/** Build the reader shape over one supplied `ReadPath`. */
export const makePathReader = (readPath: ReadPath): ByteReaderShape => {
  const loadBytes: ByteReaderShape["loadBytes"] = Effect.fn(
    "PathReader.loadBytes",
  )(function* (id) {
    return yield* readPath(objectRelativePath(id)).pipe(
      Effect.mapError((error) => new BackendFailure({
        reason: `path read failed at ${error.path}: ${error.reason}`,
        cause: error,
      })),
    )
  })

  const presenceOf = (id: ContentId): Effect.Effect<PresenceStatus> =>
    readPath(objectRelativePath(id)).pipe(
      Effect.map((resident): PresenceStatus =>
        Option.isSome(resident) ? "present" : "missing"),
      Effect.catchTag("CasPathReadError", () =>
        Effect.succeed<PresenceStatus>("failed")),
    )

  const presence: ByteReaderShape["presence"] = Effect.fn(
    "PathReader.presence",
  )(function* (ids) {
    return yield* Effect.forEach(ids, presenceOf)
  })

  return { loadBytes, presence }
}

/** Provide the read seam from one supplied `ReadPath`. */
export const layerPathReader = (readPath: ReadPath): Layer.Layer<ByteReader> =>
  Layer.succeed(ByteReader, makePathReader(readPath))
