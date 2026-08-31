/**
 * The CAS plane, one front door — a content-addressed store as a data
 * structure. The `Cas` prefix of an internal module name drops here
 * because the namespace already carries it; everything else in
 * `src/cas/` and `src/internal/` is implementation.
 *
 * The shape is three layers: dumb byte-plane seams at the bottom
 * (`ByteReader`/`ByteWriter`/`RootStore`) with interchangeable
 * backends (memory, file, key-value, any path-addressed host); the typed-node
 * store law over them (admission at put, re-verification at load);
 * and the typed laws above the store — value projections with typed
 * references, verified blob reads, graph closure and audit. The same
 * backend value serves embedded use or a server: hand it to the
 * `Server` namespace and nothing else changes.
 */
// Node vocabulary and the typed error family.
export {
  AddressMismatch,
  Byte,
  CasErrorTag as ErrorTag,
  CasNodeInput as NodeInput,
  CasReference as Reference,
  ContentId,
  ContentNotFound,
  DanglingReference,
  isCasError,
  matchCasError as matchError,
  NodeKind,
  NonCanonicalBytes,
  StoreFailure,
  UnknownKind,
  WrongKindReference,
} from "./cas/Node.ts"
export type { CasError as Error } from "./cas/Node.ts"

// The byte-plane seams: read, write, and roots capabilities as
// separate services — a read-only backend simply never provides the
// writer — plus the store-root layout contract path-shaped backends
// share.
export {
  BackendFailure,
  ByteReader,
  ByteWriter,
  layerMemoryBackend,
  makeMemoryBackend,
  objectRelativePath,
  RootStore,
  rootRelativePath,
} from "./cas/Backend.ts"
export type {
  ByteReaderShape,
  ByteWriterShape,
  MemoryBackend,
  PresenceStatus,
  RootStoreShape,
} from "./cas/Backend.ts"

// The file backend: a store root on any `FileSystem` realization.
export {
  layerFileBackend,
  layerFileBackendFromFileUrl,
  layerFileBackendWithPath,
  makeFileBackend,
  makeFileBackendFromFileUrl,
  makeFileBackendWithPath,
  normalizeStoreRoot,
  normalizeStoreRootWith,
  storeRootFromFileUrl,
  StoreRoot,
} from "./cas/FileBackend.ts"

// The key-value backend: the byte plane over any Effect
// `KeyValueStore` — memory, a directory, or SQL, which is the SQLite
// and therefore the Litestream route. It provides read and write and
// never roots: a key-value store carries no key enumeration, so
// `RootStore.list` cannot be written over it.
export { layerKvsBackend, makeKvsBackend } from "./cas/KvsBackend.ts"
export type { KvsBackend } from "./cas/KvsBackend.ts"

// The word log: the receipts seam — the store's own history,
// persisted per store and readable from a mark. The record shapes are
// the generated word-wire mirrors; nothing here invents a spelling.
export {
  defaultWordTable,
  layerFileWordLog,
  layerMemoryWordLog,
  layerSqlWordLog,
  makeFileWordLog,
  makeMemoryWordLog,
  makeSqlWordLog,
  WordLog,
  wordLogColumns,
  wordLogLockRelativePath,
  wordLogPageLimit,
  wordLogRelativePath,
} from "./cas/WordLog.ts"
export type {
  SqlWordLogOptions,
  WordHistory,
  WordLogAppend,
  WordLogEntry,
  WordLogShape,
} from "./cas/WordLog.ts"

// The roots registry over SQL: the one capability the key-value
// backend cannot serve, because SQL enumerates and a key-value store
// does not. It is the naming plane only — the bytes stay the key-value
// backend's — so the two compose into a whole store over one database.
export {
  defaultRootsTable,
  layerSqlRootStore,
  makeSqlRootStore,
} from "./cas/SqlRootStore.ts"
export type { SqlRootStoreOptions } from "./cas/SqlRootStore.ts"

// The path-reader backend: a read-only byte plane over any host that
// serves bytes at a path — a git server's raw endpoint, an object
// store, a static file host. The caller supplies `ReadPath`.
export {
  layerPathReader,
  makePathReader,
  PathReadError,
} from "./cas/PathReader.ts"
export type { ReadPath } from "./cas/PathReader.ts"

// The whole-node store law over the seams, the scheme-0 canonical
// codec, and the composed conveniences (memory and file stores with
// their seams exposed).
export {
  AddressScheme,
  CasLoader as Loader,
  CasSchemeVersion as SchemeVersion,
  CasStore as Store,
  decodeCasNode as decodeNode,
  encodeCasNode as encodeNode,
  layerAddressSha256Live,
  layerCryptoWebCrypto,
  layerFile,
  layerFileFromFileUrl,
  layerFileWithPath,
  layerMemory,
  layerMemoryLive,
  layerMemoryWith,
  layerReadStore,
  layerStore,
  layerWorded,
  makeCasLoaderOver as makeLoaderOver,
  makeCasStore as makeStore,
  makeCasStoreOver as makeStoreOver,
  makeMemoryCasStore as makeMemoryStore,
  makeSha256Address,
  verifyNodeBytes,
} from "./cas/Store.ts"
export type {
  CasAddress as Address,
  CasLoaderShape as LoaderShape,
  CasStoreShape as StoreShape,
  PutOutcome,
} from "./cas/Store.ts"

// Graph laws over the read seam alone: children-first closure and the
// untrusted-host audit.
export * as Graph from "./cas/Graph.ts"

// The library described in itself: the architecture as a value, its
// Schema, a service, and a layer — pinned against the Lean model's
// twin description through one shared canonical matrix.
export * as Architecture from "./cas/Architecture.ts"

// The schema plane's root: canonical schemas as content — identity by
// digest of canonical bytes — carried by Effect Schema through the
// annotation API. No schema stands above it.
export * as CanonicalSchema from "./cas/CanonicalSchema.ts"

// The materializer door: the generative direction of a described
// schema. A canonical code held as store content, revived, and
// materialized into either register — a live validator, or rendered
// TypeScript stamped with the address it was materialized from.
export * as Materialize from "./cas/Materialize.ts"

// The persistent annotation namespace: string keys under `foldlab/cas/`,
// attached to the encoded side and read the way Effect resolves them —
// and the sidecar annotation kind, whose subject is a typed reference to
// the schema node it annotates.
export * as Annotations from "./cas/Annotations.ts"

// Interactions as content: the exchange kind, the stored form of a
// recorded prompt/answer turn at the agent seam (R15), whose subject
// addresses either a schema node or the exchange before it.
export * as Exchanges from "./cas/Exchanges.ts"

// Programs as content (R7): the host mirror of `Cas.Lang.encodeProg` —
// a defunctionalized table laid down children-first as step nodes under
// one cont node, whose address IS the program's. Put one, load one by
// address, run one against the same store through the same doors.
export * as Programs from "./cas/Programs.ts"

// The registered replay surface: the Lean-emitted conformance vector
// as a first-class type, wire schemas hand-mirroring the emitter.
export * as ConformanceVector from "./cas/ConformanceVector.ts"

// Typed value projection, with typed references (CAS-005).
export { ProjectionCodecFailure, ref, value } from "./cas/Value.ts"
export type {
  CasValue as Value,
  ProjectionError,
  ReferenceSentinel,
  Root,
  ValueOptions,
} from "./cas/Value.ts"

// Verified blob reads and recipe-1 construction.
export { CasBlob as Blob } from "./cas/Blob.ts"
