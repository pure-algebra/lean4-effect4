/** Streamed mechanics above the whole-node CasStore boundary. */
import { Context, Effect, Stream } from "effect"
import type { CasError, CasNodeInput, CasReference, ContentId, NodeKind } from "./Node.ts"
import {
  oneShot,
  restartable,
  type CasPresence,
  type CasPushReport,
  type CasRemoteError,
  type RemoteCapabilities,
  type UploadSource,
} from "./Remote.ts"

export { oneShot, restartable, type UploadSource }
export type { CasPresence, CasPushReport, RemoteCapabilities }

export interface PutStreamOptions {
  readonly kind: NodeKind
  readonly refs: ReadonlyArray<CasReference>
  readonly expected?: ContentId
}

export interface CasTransferShape {
  /**
   * Capabilities probed per remote layer, during acquisition or lazily on
   * first wire-backed use according to the configured probe mode. A
   * successful probe is memoized for the layer's life; a retryable
   * unavailability re-probes on the next call, while authentication and
   * policy failures stay memoized.
   */
  readonly capabilities: Effect.Effect<RemoteCapabilities, CasRemoteError>

  /**
   * Query one request-order batch. Presence is advisory planning data only:
   * it never admits content and absence is never cached.
   */
  readonly missing: (
    keys: ReadonlyArray<ContentId>,
  ) => Effect.Effect<CasPresence, CasRemoteError>

  /** Publish only after the root and its declared closure stand confirmed. */
  readonly publish: (
    root: ContentId,
    closure: ReadonlyArray<ContentId>,
  ) => Effect.Effect<void, CasRemoteError>

  /**
   * Enumerate a complete local graph children-first, negotiate in capability-
   * sized batches, transfer only missing nodes, and publish the root last.
   * The peer's maxBlobBytes capability is an identity-preserving node-body
   * bound: an oversized node is refused rather than silently re-chunked.
   */
  readonly push: (
    root: ContentId,
  ) => Effect.Effect<CasPushReport, CasRemoteError | CasError>

  /**
   * Consume the complete source, verify its computed address on every
   * attempt, and succeed only after a verified remote acknowledgement.
   */
  readonly putStream: (
    source: UploadSource,
    options: PutStreamOptions,
  ) => Effect.Effect<ContentId, CasRemoteError | CasError>

  /**
   * Return checked bytes after internally managing transport scope. The current adapter uses a
   * decoded-budget-bounded in-memory whole-object spool before emitting any
   * byte. A cold reference-carrying parent whose children are absent locally
   * fails as RemoteFailure(DanglingReference); discovery-order closure pull is
   * a documented deferred boundary. Filesystem spooling and chunk-proof early
   * emission are later slices.
   */
  readonly loadStream: (
    id: ContentId,
  ) => Effect.Effect<
    Stream.Stream<Uint8Array, CasRemoteError | CasError>,
    CasRemoteError | CasError
  >
}

export class CasTransfer extends Context.Service<CasTransfer, CasTransferShape>()(
  "foldlab/cas/CasTransfer",
) {}

export type { CasNodeInput }
