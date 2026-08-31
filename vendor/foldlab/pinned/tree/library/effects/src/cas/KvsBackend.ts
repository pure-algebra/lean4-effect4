/**
 * The key-value backend: the byte plane over any Effect
 * `KeyValueStore` — memory, a directory, or SQL, which is the SQLite
 * and therefore the Litestream route. The caller supplies the store;
 * nothing here knows what a database is.
 *
 * Keys are the store-root layout every path-shaped backend shares
 * (`objects/<2 hex>/<62 hex>`), so the address is still the key.
 *
 * What it provides, and why not more: `ByteReader` and `ByteWriter`,
 * never `RootStore`. `KeyValueStore` carries no key enumeration — no
 * listing, no scan, no prefix walk — so `RootStore.list` cannot be
 * written over it at all. Publishing over a key-value store is a
 * compare-and-set question of its own and is not answered here;
 * declaring a capability this backend cannot serve is exactly the lie
 * the seam split exists to prevent. Serving this backend is therefore
 * a compile error until that decision is made, which is the intended
 * outcome, not a gap.
 *
 * `putBytes` is an unconditional `set`. The seam's algebra says
 * re-insertion of identical bytes IS the identity, so an upsert is
 * its faithful realization at one round trip rather than a
 * read-then-write. Soundness rests where it already rested: callers
 * admit first, and the store law derives the address from the bytes
 * in hand before this seam is reached. Deployment consequence: an
 * upsert of resident content still writes a row, so a re-put costs
 * replication traffic that a presence check would have avoided.
 *
 * `presence` reads through `getUint8Array`, never `has`. `has` is
 * derived from the string `get`, and the SQL store's string `get`
 * base64-encodes a binary value before the derived predicate discards
 * it — so `has` would cost a row read plus an encode of every blob it
 * was asked about. Presence over a key-value store consequently reads
 * bytes: unlike the file backend's existence check it is not free,
 * and a store answering membership without materializing the value is
 * the named improvement.
 *
 * Bytes are copied in both directions. The memory key-value store
 * retains and returns the caller's array by reference, so without the
 * copies a caller mutating its own buffer would mutate admitted
 * content — the same defence `makeMemoryBackend` already keeps.
 */
import { Context, Effect, Layer, Option } from "effect"
import * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import {
  BackendFailure,
  ByteReader,
  ByteWriter,
  objectRelativePath,
  type ByteReaderShape,
  type ByteWriterShape,
  type PresenceStatus,
} from "./Backend.ts"
import type { ContentId } from "./Node.ts"

/** The two seam shapes over one key-value store: the byte plane, and
 * nothing else. */
export interface KvsBackend {
  readonly reader: ByteReaderShape
  readonly writer: ByteWriterShape
}

const failure = (error: KeyValueStore.KeyValueStoreError): BackendFailure =>
  new BackendFailure({
    reason: `key-value store failed in ${error.method}: ${error.message}`,
  })

/** Build the byte-plane seams over one supplied key-value store. */
export const makeKvsBackend = (
  kvs: KeyValueStore.KeyValueStore,
): KvsBackend => {
  const loadBytes: ByteReaderShape["loadBytes"] = Effect.fn(
    "KvsBackend.loadBytes",
  )(function* (id) {
    return yield* kvs.getUint8Array(objectRelativePath(id)).pipe(
      Effect.map((resident) => Option.fromNullishOr(resident?.slice())),
      Effect.mapError(failure),
    )
  })

  const presenceOf = (id: ContentId): Effect.Effect<PresenceStatus> =>
    kvs.getUint8Array(objectRelativePath(id)).pipe(
      Effect.map((resident): PresenceStatus =>
        resident === undefined ? "missing" : "present"),
      Effect.catchTag("KeyValueStoreError", () =>
        Effect.succeed<PresenceStatus>("failed")),
    )

  const presence: ByteReaderShape["presence"] = Effect.fn(
    "KvsBackend.presence",
  )(function* (ids) {
    return yield* Effect.forEach(ids, presenceOf)
  })

  const putBytes: ByteWriterShape["putBytes"] = Effect.fn(
    "KvsBackend.putBytes",
  )(function* (id, bytes) {
    return yield* kvs.set(objectRelativePath(id), bytes.slice()).pipe(
      Effect.mapError(failure),
    )
  })

  return { reader: { loadBytes, presence }, writer: { putBytes } }
}

/** Provide the byte-plane seams from the `KeyValueStore` in context.
 * The realization — memory, directory, SQL — is the composition's
 * choice and stays a visible layer requirement. */
export const layerKvsBackend: Layer.Layer<
  ByteReader | ByteWriter,
  never,
  KeyValueStore.KeyValueStore
> = Layer.effectContext(
  Effect.map(KeyValueStore.KeyValueStore, (kvs) => {
    const backend = makeKvsBackend(kvs)
    return Context.make(ByteReader, backend.reader).pipe(
      Context.add(ByteWriter, backend.writer),
    )
  }),
)
