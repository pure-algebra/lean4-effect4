import { Effect, type Scope } from "effect"

export interface PeerCapabilities {
  readonly profile: "cas-http/0"
  readonly supportsUpload: boolean
}

export interface PeerObservation {
  readonly requests: number
  readonly gets: number
  readonly puts: number
  readonly bodyBytesWritten: number
  readonly bodyBytesReceived: number
  readonly openSockets: number
  /** Reference-peer-only ordering evidence; absent on hostile peers. */
  readonly putIds?: ReadonlyArray<string>
  readonly publishedRoots?: ReadonlyArray<string>
  readonly events?: ReadonlyArray<string>
}

export interface PeerEndpoint {
  readonly authority: string
  readonly observe: () => PeerObservation
}

const socketReleaseHooks = new WeakMap<PeerEndpoint, () => Effect.Effect<void>>()

/** Register a close-event hook without widening the public peer endpoint. */
export const registerSocketReleaseHook = (
  endpoint: PeerEndpoint,
  hook: () => Effect.Effect<void>,
): void => {
  socketReleaseHooks.set(endpoint, hook)
}

/** Await actual socket close events while the owning peer scope is still live. */
export const awaitPeerSocketsReleased = (endpoint: PeerEndpoint): Effect.Effect<void> => {
  const hook = socketReleaseHooks.get(endpoint)
  return hook === undefined
    ? Effect.die(new Error("peer did not register a socket-release hook"))
    : hook()
}

interface CloseObservable {
  readonly once: (event: "close", listener: () => void) => unknown
  readonly off: (event: "close", listener: () => void) => unknown
}

/** Build an event-driven hook that settles only after the live socket set is empty. */
export const socketReleaseHook = (
  sockets: ReadonlySet<CloseObservable>,
): (() => Effect.Effect<void>) => () => Effect.callback<void>((released) => {
  let cancelled = false
  let armed: ReadonlyArray<CloseObservable> = []
  let scheduled = false
  const cleanup = () => {
    for (const socket of armed) socket.off("close", onClose)
    armed = []
  }
  const check = () => {
    cleanup()
    scheduled = false
    if (cancelled) return
    if (sockets.size === 0) {
      released(Effect.void)
      return
    }
    armed = [...sockets]
    for (const socket of armed) socket.once("close", onClose)
  }
  const onClose = () => {
    if (scheduled) return
    scheduled = true
    // Recheck after every listener for this close event has run. This observes
    // the peer's actual socket-set deletion and catches connections created in
    // the same turn without polling.
    setImmediate(check)
  }
  setImmediate(check)
  return Effect.sync(() => {
    cancelled = true
    cleanup()
  })
})

export interface ScenarioRealization {
  readonly nodes?: ReadonlyMap<string, Uint8Array>
  readonly fault?: string
  readonly body?: Uint8Array
  readonly declared?: number
  readonly reportedMissing?: ReadonlySet<string>
  readonly acknowledgementContentType?: string
  readonly uploadAcknowledgementBody?: Uint8Array
  readonly publishAcknowledgementBody?: Uint8Array
  readonly capabilities?: {
    readonly maxBatchKeys: number
    readonly maxBlobBytes: number
  }
}

/**
 * Test-side seam reserved for the later LeanServer binding.
 * TODO(LeanServer peer): bind the adopted server here in its own slice.
 */
export interface ConformancePeer {
  readonly name: string
  readonly capabilities: PeerCapabilities
  readonly serve: (
    realization: ScenarioRealization,
  ) => Effect.Effect<PeerEndpoint, never, Scope.Scope>
}
