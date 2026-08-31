/**
 * GENERATED — do not edit. Effect layers lowered from an authored
 * service topology (`tools/EmitLayers.lean`), stored at the system
 * kind and printed by `lake exe emitlayers`; regeneration is
 * byte-identity-gated (`--check`, wired into `check:cas`).
 *
 * Every import path below is RESOLVED, not copied: a constructor
 * reference names its module by store address (`CodeRef.file`, at the
 * file kind), and the specifier is recovered from that file node's
 * name. The file nodes are markers — they certify WHICH MODULE, never
 * which bytes; full-content provenance is the open half of that
 * ruling (`Cas/Backend/EmitLayer.lean`).
 *
 * The acceptance this module carries is BEHAVIOURAL SHAPE, not byte
 * identity of a hand-written original: `EmittedLayers.test.ts` builds
 * each requirement-free layer below and asserts its Context holds
 * exactly the key set the topology declares.
 *
 * What that certifies: the key set. What it does not: acquisition
 * order, provide-versus-provideMerge residuals below the surface, and
 * how many instances of a shared child exist. The last one is the
 * failure mode worth naming, because its industry precedent is silent
 * — an action cache that agrees on a hash and disagrees on the output
 * serves the wrong answer without a word. This gate is the loud
 * version of that check, and it is deliberately narrower than the
 * estate's usual byte gate. The module's own BYTES are still gated by
 * `--check`; what is behavioural is only the claim that the wiring
 * means what the description says.
 *
 * emitted — schemaVersion 1, emitter `emitlayers`,
 * module `library/cas/tools/EmitLayers.lean`, toolchain Lean 4.33.1.
 */
import { ByteReader, ByteWriter, RootStore, layerMemoryBackend } from "../../src/cas/Backend.ts"
import { layerKvsBackend } from "../../src/cas/KvsBackend.ts"
import { AddressScheme, CasLoader, CasStore, layerCryptoWebCrypto, layerStore } from "../../src/cas/Store.ts"
import { Crypto, Layer } from "effect"
import { KeyValueStore, layerMemory } from "effect/unstable/persistence/KeyValueStore"

/** The platform digest, as a leaf this grammar refuses to open: the
 * constructor reaches for `crypto.subtle` through `Effect.tryPromise`.
 * It contributes identity, never structure. */
export const cryptoWebCrypto: Layer.Layer<Crypto.Crypto> = layerCryptoWebCrypto

/** Scheme-0 SHA-256 as the address scheme — one key answered, one
 * key still demanded. */
export const addressSha256: Layer.Layer<AddressScheme, never, Crypto.Crypto> = AddressScheme.layerSha256

/** The scheme over the platform digest, the digest kept PRIVATE:
 * `provide` keeps only the outer layer's answers. */
export const addressLive: Layer.Layer<AddressScheme> = Layer.provide(addressSha256, cryptoWebCrypto)

/** The three byte-plane seams from one in-memory backend — a leaf
 * whose constructor answers a whole context. */
export const memoryBacking: Layer.Layer<ByteReader | ByteWriter | RootStore> = layerMemoryBackend

/** The same backing, built again rather than shared. This topology
 * wants ITS OWN store, and `fresh` is the only place a description
 * can say so: sharing is extensional here, by digest, so two
 * occurrences of one backing are one instance unless told otherwise. */
export const freshMemoryBacking: Layer.Layer<ByteReader | ByteWriter | RootStore> = Layer.fresh(memoryBacking)

/** The scheme and the seams side by side — neither demands anything
 * of the other. */
export const foundation: Layer.Layer<AddressScheme | ByteReader | ByteWriter | RootStore> = Layer.mergeAll(addressLive, freshMemoryBacking)

/** The typed-node law: two services answered, three demanded. Left
 * unsatisfied on purpose, so the residual fold has something to
 * discharge. */
export const storeLaw: Layer.Layer<CasLoader | CasStore, never, AddressScheme | ByteReader | ByteWriter> = layerStore

/** The whole system: the law over its own foundation, with the
 * foundation KEPT — `provideMerge` answers with both sides, and
 * nothing is demanded of the caller. */
export const casSystem: Layer.Layer<AddressScheme | ByteReader | ByteWriter | CasLoader | CasStore | RootStore> = Layer.provideMerge(storeLaw, foundation)

/** Effect's own in-memory key-value store — the persistence family's
 * simplest realization, and a written constructor like any other. */
export const kvsMemory: Layer.Layer<KeyValueStore> = layerMemory

/** The byte-plane seams derived from whatever `KeyValueStore` the
 * composition supplies — two seams answered, the realization
 * demanded. */
export const kvsBacking: Layer.Layer<ByteReader | ByteWriter, never, KeyValueStore> = layerKvsBackend

/** The seams over the memory realization, the realization kept
 * private. */
export const kvsSeams: Layer.Layer<ByteReader | ByteWriter> = Layer.provide(kvsBacking, kvsMemory)

/** The scheme beside the key-value seams. */
export const kvsFoundation: Layer.Layer<AddressScheme | ByteReader | ByteWriter> = Layer.mergeAll(addressLive, kvsSeams)

/** The second root: the SAME law, over a different backing. It
 * answers with no `RootStore` — the key-value seams do not publish
 * roots — which is the residual fold visibly doing its job rather
 * than copying the first root's answer. */
export const kvsSystem: Layer.Layer<AddressScheme | ByteReader | ByteWriter | CasLoader | CasStore> = Layer.provideMerge(storeLaw, kvsFoundation)

/** Every requirement-free topology beside the service keys it
 * declares and the address it resides at — what the
 * Context-key-set differential compares. */
export const topology = [
  {
    name: "cryptoWebCrypto",
    address: "f629a281678b414c7ada146fbc0b75a868de94aaa2de1498381a86717a8eae8e",
    keys: ["effect/Crypto"],
    layer: cryptoWebCrypto,
  },
  {
    name: "addressLive",
    address: "af1acb89deefcc3d5f1f605342cbb4d0a19e8351b28c0fe01cca3b4c4ef220c2",
    keys: ["foldlab/cas/AddressScheme"],
    layer: addressLive,
  },
  {
    name: "memoryBacking",
    address: "2301f618e4cc6f30b7c3604647e0f0a4b5d6292f311fcf41cfba26f8e5adf08f",
    keys: ["foldlab/cas/ByteReader", "foldlab/cas/ByteWriter", "foldlab/cas/RootStore"],
    layer: memoryBacking,
  },
  {
    name: "freshMemoryBacking",
    address: "4a72438b9ba5e7d94c6bb3c3a7adeeec44fc68f8e8c848b83db64778d8d1e227",
    keys: ["foldlab/cas/ByteReader", "foldlab/cas/ByteWriter", "foldlab/cas/RootStore"],
    layer: freshMemoryBacking,
  },
  {
    name: "foundation",
    address: "0fec852a1bc0caa80172c965d41536daec872bfd66dd27087298f304fc3132bc",
    keys: ["foldlab/cas/AddressScheme", "foldlab/cas/ByteReader", "foldlab/cas/ByteWriter", "foldlab/cas/RootStore"],
    layer: foundation,
  },
  {
    name: "casSystem",
    address: "71a69b64d0152178366363153474d4429f24c9756f358ad9835b2baf3cc3de50",
    keys: ["foldlab/cas/AddressScheme", "foldlab/cas/ByteReader", "foldlab/cas/ByteWriter", "foldlab/cas/CasLoader", "foldlab/cas/CasStore", "foldlab/cas/RootStore"],
    layer: casSystem,
  },
  {
    name: "kvsMemory",
    address: "240e5b55d344a4ab9c3d26a37cae1019e076774d10798cdfb12fac82d660407f",
    keys: ["effect/persistence/KeyValueStore"],
    layer: kvsMemory,
  },
  {
    name: "kvsSeams",
    address: "297fe32abcb3ed0a193bd857fa79d2be299fde724328066d0eef9123b4e25f53",
    keys: ["foldlab/cas/ByteReader", "foldlab/cas/ByteWriter"],
    layer: kvsSeams,
  },
  {
    name: "kvsFoundation",
    address: "04860cc6386a39ff7b5a080ac5efc682cfda6139de07ea95ea1c70264fddc800",
    keys: ["foldlab/cas/AddressScheme", "foldlab/cas/ByteReader", "foldlab/cas/ByteWriter"],
    layer: kvsFoundation,
  },
  {
    name: "kvsSystem",
    address: "1387314d1d9c1f842af4709be02e797d004e48baa67fa6a4507221931252c6a1",
    keys: ["foldlab/cas/AddressScheme", "foldlab/cas/ByteReader", "foldlab/cas/ByteWriter", "foldlab/cas/CasLoader", "foldlab/cas/CasStore"],
    layer: kvsSystem,
  },
]
