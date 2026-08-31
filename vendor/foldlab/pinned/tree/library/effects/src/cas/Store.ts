/**
 * The CAS store service: the typed-node law over the byte-plane seams.
 *
 * Closure and kind-typing are checked at put; load verifies address
 * recomputation, canonical decode, and known kind, fail-closed with the
 * clause-named CAS errors (ruling GR-6). Renormalize-on-read is a named
 * defect. The store owns no storage: it is one law over whichever
 * `ByteReader`/`ByteWriter` backend the composition supplies, so a
 * corrupt, concurrent, or hostile backend surfaces as a typed refusal
 * on read, never as silently served bytes. Check-then-insert is sound
 * without a lock because the byte plane only grows.
 */
import {
  Clock,
  Context,
  Crypto,
  Effect,
  Encoding,
  Layer,
  Option,
  PlatformError,
} from "effect"
import type { FileSystem, Path } from "effect"
import {
  ByteReader,
  ByteWriter,
  layerMemoryBackend,
  makeMemoryBackend,
  type BackendFailure,
  type ByteReaderShape,
  type ByteWriterShape,
  type RootStore,
} from "./Backend.ts"
import {
  layerFileBackend,
  layerFileBackendFromFileUrl,
  layerFileBackendWithPath,
} from "./FileBackend.ts"
import { WordLog, type WordLogShape } from "./WordLog.ts"
import {
  judgeAdmission,
  type AdmissionFacts,
} from "../internal/admission.ts"
import { bytesEqual } from "../internal/bytes.ts"
import {
  CasSchemeVersion,
  decodeCasNode,
  encodeCasNode,
} from "../internal/casCodec.ts"
import {
  AddressMismatch,
  CasNodeInput,
  ContentNotFound,
  ContentId,
  DanglingReference,
  NonCanonicalBytes,
  StoreFailure,
  UnknownKind,
  WrongKindReference,
  type CasError,
} from "./Node.ts"

/** The read half of the store law as a plain shape: one operation, stated
 * over whole nodes rather than bytes. The service below is this shape in
 * the context; embeddings that hold a backend directly use it as a value. */
export interface CasLoaderShape {
  /** Load and re-verify a node: recomputed address, canonical decode, known
   * kind. Never renormalizes. */
  readonly load: (id: ContentId) => Effect.Effect<CasNodeInput, CasError>
}

/** The load-only law: everything a typed read needs, requiring only the
 * read seam — so a read-only composition (a path-reader host) serves
 * typed values and graphs with no writer anywhere. Every store
 * composition provides it alongside `CasStore`. */
export class CasLoader extends Context.Service<CasLoader, CasLoaderShape>()(
  "foldlab/cas/CasLoader",
) {}

/** What a put ANSWERS in the model: the host spelling of
 * `Cas.PutOutcome` (`Cas/Core/Admission.lean`) — the address either
 * way, and which arm fired. A duplicate is not an error (the byte
 * plane is grow-only; a re-put answers the same address), but it is a
 * different OUTCOME: the word law appends on `fresh` and leaves the
 * word unchanged on `duplicate` (`Interp.lean:76-79`,
 * `Handler.lean:84-85`), so an interpreter that cannot see the arm
 * cannot leave the word `runP` leaves. */
export type PutOutcome =
  | { readonly _tag: "fresh"; readonly id: ContentId }
  | { readonly _tag: "duplicate"; readonly id: ContentId }

/** The whole store law: reading, plus the one operation that grows the
 * store. `put` is where admission is judged, which is why nothing below
 * this shape is allowed to judge it. */
export interface CasStoreShape extends CasLoaderShape {
  /** Admit and store a node. Every referenced address must already resolve
   * in the store, at its declared kind. Answers the address alone — the
   * projection of `putOutcome` for the caller that only names content. A
   * consumer whose law branches on admission (the run word does) uses
   * `putOutcome` instead. */
  readonly put: (node: CasNodeInput) => Effect.Effect<ContentId, CasError>
  /** The same admission, answering the model's `PutOutcome`: the address,
   * and whether this put admitted the node (`fresh`) or found it already
   * resident (`duplicate`). This is the operation the model calls `put`;
   * the host `put` above is its address projection. */
  readonly putOutcome: (node: CasNodeInput) => Effect.Effect<PutOutcome, CasError>
}

/** The store law in the context: admission at put, re-verification at
 * load, over whichever backend and address scheme the composition
 * supplies. */
export class CasStore extends Context.Service<CasStore, CasStoreShape>()(
  "foldlab/cas/CasStore",
) {}

/** Abstract address function. The model quantifies over this function; the
 * default runtime adapter below supplies SHA-256. */
export interface CasAddress {
  readonly digest: (
    canonicalBytes: Uint8Array,
  ) => Effect.Effect<ContentId, StoreFailure>
}

export { CasSchemeVersion, decodeCasNode, encodeCasNode } from "../internal/casCodec.ts"

const cloneNode = (node: CasNodeInput): CasNodeInput =>
  CasNodeInput.make({
    kind: { ...node.kind },
    payload: node.payload.slice(),
    refs: node.refs.map((ref) => ({ ...ref })),
  })

const ensureKnownKind = (node: CasNodeInput): Effect.Effect<void, UnknownKind> =>
  node.kind.version === CasSchemeVersion
    ? Effect.void
    : Effect.fail(new UnknownKind(node.kind))

const validateNode = (
  input: CasNodeInput,
): Effect.Effect<CasNodeInput, StoreFailure> =>
  CasNodeInput.makeEffect(input).pipe(
    Effect.mapError((issue) => new StoreFailure({
      reason: `Invalid CAS node input: ${String(issue)}`,
      cause: issue,
    })),
  )

const backendFailure = (failure: BackendFailure): StoreFailure =>
  new StoreFailure({
    reason: `Backend failed: ${failure.reason}`,
    cause: failure,
  })

/** The read-verification law, shared by `load` and the graph walks:
 * canonical decode, byte-identical re-encoding, known kind, recomputed
 * address. Never renormalizes; a failing byte plane surfaces typed. */
export const verifyNodeBytes = Effect.fn("CasStore.verifyNodeBytes")(
  function* (
    address: CasAddress,
    id: ContentId,
    bytes: Uint8Array,
  ): Effect.fn.Return<CasNodeInput, CasError> {
    const canonicalBytes = bytes.slice()
    const decodedNode = decodeCasNode(canonicalBytes)
    if (Option.isNone(decodedNode)
      || !bytesEqual(encodeCasNode(decodedNode.value), canonicalBytes)) {
      return yield* new NonCanonicalBytes({ id })
    }
    const decoded = decodedNode.value

    yield* ensureKnownKind(decoded)
    const actual = yield* address.digest(canonicalBytes.slice())
    if (actual !== id) {
      return yield* new AddressMismatch({ expected: id, actual })
    }

    return cloneNode(decoded)
  },
)

/** Resolve SHA-256 through Effect's platform-independent Crypto service. The
 * host runtime supplies the native implementation; this module never reaches
 * through an ambient global. */
export const makeSha256Address: Effect.Effect<CasAddress, never, Crypto.Crypto> =
    Crypto.Crypto.pipe(
      Effect.map((crypto) => ({
        digest: Effect.fn("CasAddress.sha256")(function* (canonicalBytes) {
        const digest = yield* crypto.digest("SHA-256", canonicalBytes).pipe(
          Effect.mapError((cause) => new StoreFailure({
            reason: `SHA-256 failed: ${String(cause)}`,
            cause,
          })),
        )
        // A wrong-width digest is a broken host crypto service: fail typed
        // before the branded hex constructor turns it into a defect.
        if (digest.byteLength !== 32) {
          return yield* new StoreFailure({
            reason: `SHA-256 digest was ${digest.byteLength} bytes, expected 32`,
          })
        }
        return ContentId.make(Encoding.encodeHex(digest))
      }),
    })))

/** Construct the load-only law over an explicit read seam. */
export const makeCasLoaderOver = (
  address: CasAddress,
  reader: ByteReaderShape,
): CasLoaderShape => ({
  load: Effect.fn("CasLoader.load")(function* (id: ContentId) {
    const resident = yield* reader.loadBytes(id).pipe(
      Effect.mapError(backendFailure),
    )
    if (Option.isNone(resident)) {
      return yield* new ContentNotFound({ id })
    }
    return yield* verifyNodeBytes(address, id, resident.value)
  }),
})

/** Construct the store law over explicit seam shapes — the constructor
 * for embeddings that hold a backend directly, without Layer wiring.
 *
 * `wordLog` is the optional receipts seam. When present, every FRESH
 * admission is receipted — bytes first, receipt second, the crash
 * matrix's safe direction — and a duplicate put appends nothing,
 * exactly as the Lean `step` leaves the word unchanged on `duplicate`.
 * A put whose bytes land but whose receipt does not FAILS TOGETHER,
 * typed: BROKEN-SILENT is the only alarm category, and a receipt that
 * silently never existed would break "words are receipts" without a
 * sound. The content stays resident either way (the byte plane is
 * grow-only), so the refusal names that a re-put answers the same
 * address — the same posture as an unacknowledged put. */
export const makeCasStoreOver = (
  address: CasAddress,
  reader: ByteReaderShape,
  writer: ByteWriterShape,
  wordLog?: WordLogShape,
): CasStoreShape => {
  /** Answer the admission judgment's facts from the byte plane: the
   * verified kind tag per reference, and any bytes resident at the
   * candidate id. */
  const admissionFacts = Effect.fn("CasStore.admissionFacts")(function* (
    node: CasNodeInput,
    id: ContentId,
  ) {
    const refTags: Array<Option.Option<number>> = []
    for (const ref of node.refs) {
      const resident = yield* reader.loadBytes(ref.id).pipe(
        Effect.mapError(backendFailure),
      )
      if (Option.isNone(resident)) {
        refTags.push(Option.none())
      } else {
        const verified = yield* verifyNodeBytes(address, ref.id, resident.value)
        refTags.push(Option.some(verified.kind.tag))
      }
    }
    const resident = yield* reader.loadBytes(id).pipe(
      Effect.mapError(backendFailure),
    )
    const facts: AdmissionFacts = { refTags, resident }
    return facts
  })

  const putOutcome = Effect.fn("CasStore.put")(function* (
    input: CasNodeInput,
  ): Effect.fn.Return<PutOutcome, CasError> {
    const node = yield* validateNode(input)
    yield* ensureKnownKind(node)
    const canonicalBytes = encodeCasNode(node)
    const id = yield* address.digest(canonicalBytes.slice())

    // One admission law for every backend: the shared pure judge over
    // facts the byte plane answers. Grow-only monotonicity makes
    // check-then-insert sound without a lock.
    const verdict = judgeAdmission(
      canonicalBytes,
      yield* admissionFacts(node, id),
    )
    switch (verdict._tag) {
      case "DanglingReference":
        return yield* new DanglingReference({ missing: verdict.missing })
      case "WrongKindReference":
        return yield* new WrongKindReference({
          ref: verdict.ref,
          expectedTag: verdict.expectedTag,
          actualTag: verdict.actualTag,
        })
      case "Collision":
        return yield* new StoreFailure({
          reason: `Content identifier collision at ${id}`,
        })
      case "AlreadyResident":
        return { _tag: "duplicate", id }
      case "NonCanonical":
      case "UnknownKind":
        // Unreachable for a validated, freshly encoded node; kept
        // typed so a codec regression cannot admit silently.
        return yield* new StoreFailure({
          reason: `Admission refused own encoding: ${verdict._tag}`,
        })
      case "Admit": {
        yield* writer.putBytes(id, canonicalBytes).pipe(
          Effect.mapError(backendFailure),
        )
        if (wordLog !== undefined) {
          const at = yield* Clock.currentTimeMillis
          yield* wordLog.append({
            address: id,
            at,
            size: node.payload.length,
            tag: node.kind.tag,
          }).pipe(
            Effect.mapError((failure) => new StoreFailure({
              reason: `admitted ${id} but its receipt was not written: ${failure.reason} — the content is resident and a re-put answers the same address; the word under-reports this admission`,
              cause: failure,
            })),
          )
        }
        return { _tag: "fresh", id }
      }
    }
  })

  const put = (node: CasNodeInput): Effect.Effect<ContentId, CasError> =>
    Effect.map(putOutcome(node), (outcome) => outcome.id)

  return CasStore.of({ put, putOutcome, ...makeCasLoaderOver(address, reader) })
}

/** The address scheme as a service: the digest the laws recompute is a
 * dependency of the composition, never an argument threaded by hand.
 * The model quantifies over the address function, and so does the
 * context — a test or a vector binding provides its own scheme with
 * `AddressScheme.layerOf`. */
export class AddressScheme extends Context.Service<AddressScheme, CasAddress>()(
  "foldlab/cas/AddressScheme",
) {
  /** An explicit scheme as a layer — deterministic tests and vector
   * bindings. */
  static readonly layerOf = (address: CasAddress): Layer.Layer<AddressScheme> =>
    Layer.succeed(AddressScheme, address)

  /** Scheme-0 SHA-256 through the runtime's `Crypto` service. */
  static readonly layerSha256: Layer.Layer<
    AddressScheme,
    never,
    Crypto.Crypto
  > = Layer.effect(AddressScheme, makeSha256Address)
}

/** Construct the store law over the seams and scheme in context. The
 * word log is read as an OPTIONAL service: a composition that provides
 * `WordLog` gets receipted admissions, and one that does not gets the
 * store law unchanged — the requirement never appears in `R`, so no
 * existing composition owes a log it did not choose. */
export const makeCasStore: Effect.Effect<
  CasStoreShape,
  never,
  ByteReader | ByteWriter | AddressScheme
> = Effect.map(
  Effect.all([
    AddressScheme,
    ByteReader,
    ByteWriter,
    Effect.serviceOption(WordLog),
  ]),
  ([address, reader, writer, wordLog]) =>
    makeCasStoreOver(address, reader, writer, Option.getOrUndefined(wordLog)),
)

/** Construct an isolated in-memory store: the law over one fresh memory
 * backend, for callers that need a store value rather than a Layer. */
export const makeMemoryCasStore = (
  address: CasAddress,
): Effect.Effect<CasStoreShape> =>
  Effect.sync(() => {
    const backend = makeMemoryBackend()
    return makeCasStoreOver(address, backend.reader, backend.writer)
  })

/** The store-law Layer over whichever backend and address scheme the
 * composition supplies, the load-only law provided beside it. */
export const layerStore: Layer.Layer<
  CasStore | CasLoader,
  never,
  ByteReader | ByteWriter | AddressScheme
> = Layer.effectContext(
  makeCasStore.pipe(
    Effect.map((store) => Context.make(CasStore, store).pipe(
      Context.add(CasLoader, { load: store.load }),
    )),
  ),
)

/**
 * The store law over a backend AND a word log — the worded
 * composition, spelled once.
 *
 * The optionality ruling stands: `makeCasStore` reads `WordLog` as an
 * optional service, so a composition that provides none gets the store
 * law unchanged. What that ruling costs is an ordering that must be
 * got right every time — the log has to stand UNDER the law's build,
 * where the law can see it. Merged BESIDE the law instead, the build
 * finds no log and every admission goes unreceipted, SILENTLY, because
 * "no log" is a legal composition. That is a trap worth spelling in
 * one place rather than in every caller.
 *
 * The address scheme and any realization the pieces need stay visible
 * requirements: this combinator decides the ordering and nothing else.
 */
export const layerWorded = <ROut, E, RIn, EW, RW>(
  backend: Layer.Layer<ROut, E, RIn>,
  wordLog: Layer.Layer<WordLog, EW, RW>,
): Layer.Layer<
  CasStore | CasLoader | WordLog | ROut,
  E | EW,
  | RIn
  | RW
  | Exclude<ByteReader | ByteWriter | AddressScheme, WordLog | ROut>
> => layerStore.pipe(Layer.provideMerge(Layer.merge(backend, wordLog)))

/** The load-only law over the read seam alone — what a read-only
 * composition (a path-reader host) provides so typed reads work with
 * no writer anywhere. */
export const layerReadStore: Layer.Layer<
  CasLoader,
  never,
  ByteReader | AddressScheme
> = Layer.effect(
  CasLoader,
  Effect.map(
    Effect.all([AddressScheme, ByteReader]),
    ([address, reader]) => makeCasLoaderOver(address, reader),
  ),
)

/** One isolated in-memory CAS: the store law over a fresh memory
 * backend, with the seams exposed for further composition — the same
 * backend value can stand under a server. The address scheme stays a
 * visible requirement; `AddressScheme.layerSha256` is the production
 * one. */
export const layerMemory: Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore,
  never,
  AddressScheme
> = layerStore.pipe(Layer.provideMerge(layerMemoryBackend))

/** One isolated in-memory CAS under an explicit address scheme — the
 * deterministic-digest form tests and vector bindings compose. */
export const layerMemoryWith = (address: CasAddress): Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore | AddressScheme
> => layerMemory.pipe(Layer.provideMerge(AddressScheme.layerOf(address)))

/** One file-backed CAS: the store law over a store root, seams exposed
 * for further composition — the same backend value can stand under a
 * server. The `FileSystem` realization and the address scheme stay
 * visible layer requirements. */
export const layerFile = (storeRoot: string): Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore,
  never,
  FileSystem.FileSystem | AddressScheme
> => layerStore.pipe(Layer.provideMerge(layerFileBackend(storeRoot)))

/** File-backed CAS using the host-provided Effect Path implementation. */
export const layerFileWithPath = (storeRoot: string): Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore,
  never,
  FileSystem.FileSystem | Path.Path | AddressScheme
> => layerStore.pipe(Layer.provideMerge(layerFileBackendWithPath(storeRoot)))

/** File-backed CAS rooted at a file URL through `Path.fromFileUrl`. */
export const layerFileFromFileUrl = (url: URL): Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore,
  BackendFailure,
  FileSystem.FileSystem | Path.Path | AddressScheme
> => layerStore.pipe(Layer.provideMerge(layerFileBackendFromFileUrl(url)))

/** The WebCrypto-backed `Crypto` layer: SHA-256 through the platform's
 * `crypto.subtle`, which every target runtime provides. The package ships
 * no other Crypto implementation, so this is the production digest path a
 * local composition supplies — proved against the scheme-0 known-answer
 * vectors by the conformance gate. */
export const layerCryptoWebCrypto: Layer.Layer<Crypto.Crypto> = Layer.succeed(
  Crypto.Crypto,
  Crypto.make({
    randomBytes: (size) => crypto.getRandomValues(new Uint8Array(size)),
    digest: (algorithm, data) =>
      Effect.tryPromise({
        // The pre-image is copied into a plain buffer: a shared or resizable
        // backing store must not change under an in-flight digest.
        try: () => crypto.subtle.digest(algorithm, Uint8Array.from(data)),
        catch: (cause) =>
          new PlatformError.PlatformError(
            new PlatformError.BadArgument({
              module: "Crypto",
              method: "digest",
              description: `${algorithm} failed: ${String(cause)}`,
            }),
          ),
      }).pipe(Effect.map((digest) => new Uint8Array(digest))),
  }),
)

/** The production address scheme, zero configuration: scheme-0 SHA-256
 * through WebCrypto. */
export const layerAddressSha256Live: Layer.Layer<AddressScheme> =
  AddressScheme.layerSha256.pipe(Layer.provide(layerCryptoWebCrypto))

/** The zero-configuration local runtime: one isolated in-memory store over
 * scheme-0 SHA-256 through WebCrypto, seams and scheme exposed. */
export const layerMemoryLive: Layer.Layer<
  CasStore | CasLoader | ByteReader | ByteWriter | RootStore | AddressScheme
> = layerMemory.pipe(Layer.provideMerge(layerAddressSha256Live))
