/**
 * The architecture description is CHECKED, not prose: the capability
 * matrix derived from the value renders to the same canonical pin the
 * Lean model guards; the seam keys are the real service keys; and the
 * declared capabilities are the real layer types — asserted at the
 * type level, so the description cannot drift from the code it
 * describes.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer } from "effect"
import type { FileSystem } from "effect"
import type * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import {
  addressSchemeKey,
  capabilityMatrix,
  capabilityMatrixPin,
  layer,
  seamKeys,
  Service,
  value,
} from "../src/cas/Architecture.ts"
import {
  ByteReader,
  ByteWriter,
  RootStore,
  layerMemoryBackend,
} from "../src/cas/Backend.ts"
import { layerFileBackend } from "../src/cas/FileBackend.ts"
import { layerKvsBackend } from "../src/cas/KvsBackend.ts"
import { layerPathReader } from "../src/cas/PathReader.ts"
import {
  AddressScheme,
  CasLoader,
  CasStore,
  layerReadStore,
  makeCasStore,
} from "../src/cas/Store.ts"
import type { CasValue } from "../src/cas/Value.ts"
import { canonicalJson } from "../src/cas/Value.ts"

/** Exact type equality — the mutual-assignability trick. */
type Equals<A, B> =
  (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2)
    ? true
    : false

type ProvidedOf<L> = L extends Layer.Layer<infer A, infer _E, infer _R>
  ? A
  : never
type RequiredOf<L> = L extends Layer.Layer<infer _A, infer _E, infer R>
  ? R
  : never
type ContextOf<E> = E extends Effect.Effect<infer _A, infer _E2, infer R>
  ? R
  : never

// The declared backend capabilities ARE the real layer types.
const memoryProvides: Equals<
  ProvidedOf<typeof layerMemoryBackend>,
  ByteReader | ByteWriter | RootStore
> = true
const fileProvides: Equals<
  ProvidedOf<ReturnType<typeof layerFileBackend>>,
  ByteReader | ByteWriter | RootStore
> = true
const filePlatform: Equals<
  RequiredOf<ReturnType<typeof layerFileBackend>>,
  FileSystem.FileSystem
> = true
const pathReaderIsReadOnly: Equals<
  ProvidedOf<ReturnType<typeof layerPathReader>>,
  ByteReader
> = true
// The key-value backend provides the byte plane and no roots seam: a
// key-value store carries no enumeration, so publishing over it is a
// compile error rather than a runtime refusal.
const kvsProvidesBytesOnly: Equals<
  ProvidedOf<typeof layerKvsBackend>,
  ByteReader | ByteWriter
> = true
const kvsNeedsKeyValueStore: Equals<
  RequiredOf<typeof layerKvsBackend>,
  KeyValueStore.KeyValueStore
> = true

// The declared law capabilities ARE the real requirement channels; the
// address scheme rides every law as the digest dependency.
const storeNeedsReadWrite: Equals<
  ContextOf<typeof makeCasStore>,
  ByteReader | ByteWriter | AddressScheme
> = true
const readStoreNeedsReadOnly: Equals<
  RequiredOf<typeof layerReadStore>,
  ByteReader | AddressScheme
> = true
const readStoreProvidesLoader: Equals<
  ProvidedOf<typeof layerReadStore>,
  CasLoader
> = true
const valueGetNeedsLoaderOnly: Equals<
  ContextOf<ReturnType<CasValue<number>["get"]>>,
  CasLoader
> = true
const valuePutNeedsStore: Equals<
  ContextOf<ReturnType<CasValue<number>["put"]>>,
  CasStore
> = true

it.effect("the static description-vs-code checks elaborated", () =>
  Effect.sync(() => {
    expect([
      memoryProvides,
      fileProvides,
      filePlatform,
      pathReaderIsReadOnly,
      kvsProvidesBytesOnly,
      kvsNeedsKeyValueStore,
      storeNeedsReadWrite,
      readStoreNeedsReadOnly,
      readStoreProvidesLoader,
      valueGetNeedsLoaderOnly,
      valuePutNeedsStore,
    ]).toEqual(Array.from({ length: 11 }, () => true))
  }))

it.effect("the capability matrix renders to the pin the Lean model guards", () =>
  Effect.sync(() => {
    expect(canonicalJson(capabilityMatrix(value))).toBe(capabilityMatrixPin)
  }))

it.effect("the seam keys and the scheme key are the real service keys", () =>
  Effect.sync(() => {
    expect(seamKeys).toEqual({
      read: ByteReader.key,
      roots: RootStore.key,
      write: ByteWriter.key,
    })
    expect(addressSchemeKey).toBe(AddressScheme.key)
  }))

it.effect("the description arrives as a service through its layer", () =>
  Effect.gen(function* () {
    const description = yield* Service
    expect(description).toBe(value)
    expect(description.types.map((carrier) => carrier.name)).toContain("address")
    expect(description.laws.find((law) => law.name === "loader")?.needs)
      .toEqual(["read"])
  }).pipe(Effect.provide(layer)))
