/**
 * GENERATED — do not edit. THE ARCHITECTURE, as data: the data
 * vocabulary with its model and runtime homes, the capability seams,
 * the laws above them, the backends below them, and the capability
 * matrix's pinned rendering — emitted from
 * `library/cas/Cas/Architecture.lean` by `lake exe emitarchitecture`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`).
 *
 * `src/cas/Architecture.ts` is this file's consumer, and what it adds
 * is everything here is not: the Schema of the description, the
 * service and the layer that carry it, the matrix derivation the
 * pin above is compared against, and the seam-to-service-key map,
 * which names TypeScript service keys the model does not carry. The
 * two descriptions used to be two hand-maintained spellings agreeing
 * only on the matrix — so they could disagree about what a law MEANS
 * with every gate green. Now there is one.
 *
 * emitted — schemaVersion 1, emitter `emitarchitecture`,
 * module `library/cas/tools/EmitArchitecture.lean`, toolchain Lean 4.33.1.
 */

/** One capability of the byte plane — the unit the seams split by.
 * The union IS the seam set: the model's `lawsNeedOnlySeams` and
 * `backendsProvideOnlySeams` say no law needs and no backend
 * provides a capability outside it. */
export type ArchCapability = "read" | "roots" | "write"

/** One carrier of the data vocabulary, with its model and runtime
 * homes. */
export interface ArchTypeRow {
  readonly form: string
  readonly lean: string
  readonly name: string
  readonly ts: string
}

/** One law above the seams: what it means, and which capabilities
 * it needs — nothing else about storage. The plane union is read
 * off the laws themselves. */
export interface ArchLawRow {
  readonly means: string
  readonly name: string
  readonly needs: ReadonlyArray<ArchCapability>
  readonly plane: "cas" | "server"
}

/** One backend below the seams: which capabilities it provides —
 * dumbness is the absence of anything else to say. */
export interface ArchBackendRow {
  readonly means: string
  readonly name: string
  readonly provides: ReadonlyArray<ArchCapability>
}

/** The library's shape: data vocabulary, seams, laws, backends. */
export interface ArchDescription {
  readonly backends: ReadonlyArray<ArchBackendRow>
  readonly laws: ReadonlyArray<ArchLawRow>
  readonly seams: ReadonlyArray<ArchCapability>
  readonly types: ReadonlyArray<ArchTypeRow>
}

/** The value: `@foldlab/cas` — the description `Cas.foldlabCas`
 * carries, row for row and string for string. `src/cas/Architecture.ts`
 * lifts it through the description's own Schema; nothing between the
 * two is retyped. */
export const architecture: ArchDescription = {
  backends: [
    {
      means: "plain maps, grow-only",
      name: "memory",
      provides: ["read", "write", "roots"],
    },
    {
      means: "a store root: objects/<2 hex>/<62 hex> + roots/<hex>, temp+rename",
      name: "file",
      provides: ["read", "write", "roots"],
    },
    {
      means: "any Effect KeyValueStore; SQL is the Litestream route; no roots seam",
      name: "kvs",
      provides: ["read", "write"],
    },
    {
      means: "any host serving bytes at a path; writes do not compile",
      name: "pathReader",
      provides: ["read"],
    },
  ],
  laws: [
    {
      means: "put is the admission law: closure and edge kinds checked",
      name: "store",
      needs: ["read", "write"],
      plane: "cas",
    },
    {
      means: "load-only re-verification: digest recomputed, canonical re-decode",
      name: "loader",
      needs: ["read"],
      plane: "cas",
    },
    {
      means: "typed values encode; references marker-lowered in canonical order",
      name: "valuePut",
      needs: ["read", "write"],
      plane: "cas",
    },
    {
      means: "typed values decode; references resolve to lazy typed roots",
      name: "valueGet",
      needs: ["read"],
      plane: "cas",
    },
    {
      means: "verified chunked blobs, recipe 1",
      name: "blob",
      needs: ["read", "write"],
      plane: "cas",
    },
    {
      means: "children-first deduplicated reachability",
      name: "graphClosure",
      needs: ["read"],
      plane: "cas",
    },
    {
      means: "the untrusted-host audit: every reachable node re-verified",
      name: "graphVerify",
      needs: ["read"],
      plane: "cas",
    },
    {
      means: "cas-http/0 interpreted over the same seams an embedded store uses",
      name: "serverCore",
      needs: ["read", "write", "roots"],
      plane: "server",
    },
  ],
  seams: ["read", "write", "roots"],
  types: [
    {
      form: "32-byte digest of the canonical pre-image — the identity",
      lean: "Addr32 (Cas/Node.lean)",
      name: "address",
      ts: "ContentId (src/cas/Node.ts)",
    },
    {
      form: "expected kind tag + address: one typed edge",
      lean: "Ref (Cas/Node.lean)",
      name: "ref",
      ts: "CasReference (src/cas/Node.ts)",
    },
    {
      form: "version byte, kind tag, payload bytes, ordered refs",
      lean: "Node (Cas/Node.lean)",
      name: "node",
      ts: "CasNodeInput (src/cas/Node.ts)",
    },
    {
      form: "partial map address ⇀ node; grows only; closed = nothing dangles",
      lean: "Store (Cas/Store.lean)",
      name: "store",
      ts: "seams + store law (src/cas/Backend.ts, Store.ts)",
    },
    {
      form: "typed address: phantom value type + expected kind tag",
      lean: "Root α (Cas/Refs.lean)",
      name: "root",
      ts: "Root<A> (src/cas/Value.ts)",
    },
    {
      form: "{\"$ref\": k} — the k-th reference, in canonical byte order",
      lean: "marker grammar (Cas/Refs.lean)",
      name: "marker",
      ts: "refMarkers walks (src/internal/refMarkers.ts)",
    },
    {
      form: "canonical JSON envelope {revision, value}",
      lean: "Json.Value + renderCompact (Cas/Json.lean)",
      name: "payload",
      ts: "canonicalJson (src/cas/Value.ts)",
    },
    {
      form: "the digest the laws recompute — quantified over, never fixed",
      lean: "H : Bytes → Addr (Cas/Address.lean)",
      name: "addressScheme",
      ts: "AddressScheme service (src/cas/Store.ts)",
    },
  ],
}

/** The pinned canonical rendering of the load-bearing shared
 * projection — which capabilities each law needs, each backend
 * provides, the seam set, and the data-vocabulary names. Both sides
 * DERIVE the matrix from their own copy of the description and
 * render it through their own canonical JSON; this is the one
 * literal they are both held to, and it is emitted from the model's
 * `Cas.capabilityMatrixPin` so there is no longer a second home to
 * update. */
export const capabilityMatrixPin = "{\"backends\":{\"file\":[\"read\",\"roots\",\"write\"],\"kvs\":[\"read\",\"write\"],\"memory\":[\"read\",\"roots\",\"write\"],\"pathReader\":[\"read\"]},\"laws\":{\"blob\":[\"read\",\"write\"],\"graphClosure\":[\"read\"],\"graphVerify\":[\"read\"],\"loader\":[\"read\"],\"serverCore\":[\"read\",\"roots\",\"write\"],\"store\":[\"read\",\"write\"],\"valueGet\":[\"read\"],\"valuePut\":[\"read\",\"write\"]},\"seams\":[\"read\",\"roots\",\"write\"],\"types\":[\"address\",\"addressScheme\",\"marker\",\"node\",\"payload\",\"ref\",\"root\",\"store\"]}"
