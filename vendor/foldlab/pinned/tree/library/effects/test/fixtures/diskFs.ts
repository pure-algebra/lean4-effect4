/**
 * The real-disk test scaffolding shared by every suite that composes
 * the library over an actual directory: the platform-bun `FileSystem`
 * realization (`@effect/platform-bun`, dev-only — the library itself
 * stays platform-agnostic and speaks nothing but the `FileSystem`
 * service), the on-disk store composition, and a scoped temp store
 * root. No hand-rolled filesystem code anywhere: the platform layer is
 * the one realization, and disk-side assertions go through the same
 * `FileSystem` service the backend uses.
 */
import { BunFileSystem } from "@effect/platform-bun"
import { Effect, FileSystem, Layer, PlatformError } from "effect"
import { Cas } from "../../src/index.ts"

/** The real filesystem: the platform-bun realization, once. */
export const layerDiskFs: Layer.Layer<FileSystem.FileSystem> =
  BunFileSystem.layer

/** The on-disk store composition over a store root: the file backend,
 * scheme-0 SHA-256 through WebCrypto. `provideMerge` keeps the
 * `FileSystem` and address seams visible for disk-side assertions. */
export const layerDisk = (storeRoot: string) =>
  Cas.layerFile(storeRoot).pipe(
    Layer.provideMerge(Layer.mergeAll(
      layerDiskFs,
      Cas.layerAddressSha256Live,
    )),
  )

/** Disk-side assertion read, through the `FileSystem` service. */
export const bytesOnDisk = (
  path: string,
): Effect.Effect<Uint8Array, PlatformError.PlatformError, FileSystem.FileSystem> =>
  FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFile(path)))

/** One fresh temp store root per test, removed with the scope. */
export const withStoreRoot = <A, E>(
  use: (storeRoot: string) => Effect.Effect<A, E, FileSystem.FileSystem>,
): Effect.Effect<A, E | PlatformError.PlatformError> =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const storeRoot = yield* fs.makeTempDirectoryScoped({
      prefix: "foldlab-cas-",
    })
    return yield* use(storeRoot)
  })).pipe(Effect.provide(layerDiskFs))
