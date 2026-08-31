/**
 * @foldlab/cas — a content-addressed store as a data structure,
 * servable.
 *
 * Two planes, two namespaces, nothing else at the root:
 *
 * - `Cas` — the data structure: the byte-plane seams and their
 *   backends (memory, file, key-value, path-reader), the typed-node
 *   store and load laws, graph closure and verification, node
 *   vocabulary and typed errors, typed value projection with typed
 *   references, and verified blob reads.
 * - `Server` — the same seams, served: the closed cas-http/0 request
 *   algebra as data, the pure wire law, the semantic core, and the
 *   four-step HTTP shell.
 *
 * The record/replay plane is stashed at `archive/replay-plane/`, and
 * the hand-built remote client with its streaming-proof machinery at
 * `archive/remote-plane/`, while the library focuses on CAS semantics,
 * the DSL, and metaprogramming; history-node kind tags stay reserved
 * in the registry, and a remote returns as a generated transport
 * adapter of the operation manifest, never as bespoke machinery.
 * TypeScript observations and Lean model claims remain separate
 * surfaces.
 */
export * as Cas from "./Cas.ts"
export * as Server from "./Server.ts"
