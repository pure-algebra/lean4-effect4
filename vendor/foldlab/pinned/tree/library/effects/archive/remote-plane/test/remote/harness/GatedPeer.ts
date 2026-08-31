import { Deferred, Effect } from "effect"
import type { Scope } from "effect"
import { createServer, type Socket } from "node:net"
import {
  registerSocketReleaseHook,
  socketReleaseHook,
  type PeerObservation,
} from "./ConformancePeer.ts"
import { encodeCapabilityDocument } from "../../../src/internal/remoteControl.ts"

export interface GatedEndpoint {
  readonly authority: string
  readonly observe: () => PeerObservation
  readonly awaitRequest: (count: 1 | 2) => Effect.Effect<void>
  readonly awaitClosed: (count: 1 | 2) => Effect.Effect<void>
}

/**
 * Where the peer stops answering a data-plane request: after writing the
 * response headers and half the body, before writing anything at all, or not
 * at all — a complete response inside whatever deadline the caller set.
 */
export type GatedStall = "afterHeaders" | "beforeHeaders" | "none"

/** A raw peer whose partial responses expose deterministic Deferred gates. */
export const serveGatedPeer = (
  body: Uint8Array,
  stall: GatedStall = "afterHeaders",
): Effect.Effect<GatedEndpoint, never, Scope.Scope> =>
  Effect.gen(function* () {
    const firstStarted = yield* Deferred.make<void>()
    const secondStarted = yield* Deferred.make<void>()
    const firstClosed = yield* Deferred.make<void>()
    const secondClosed = yield* Deferred.make<void>()
    return yield* Effect.acquireRelease(
      Effect.callback<{ readonly endpoint: GatedEndpoint; readonly close: Effect.Effect<void> }>((resume) => {
        const sockets = new Set<Socket>()
        const stats = {
          requests: 0,
          gets: 0,
          puts: 0,
          bodyBytesWritten: 0,
          bodyBytesReceived: 0,
        }
        const server = createServer((socket) => {
          sockets.add(socket)
          let ordinal: 1 | 2 | undefined
          socket.on("error", () => undefined)
          socket.once("close", () => {
            sockets.delete(socket)
            if (ordinal !== undefined) {
              const closed = ordinal === 1 ? firstClosed : secondClosed
              Effect.runFork(Deferred.succeed(closed, undefined))
            }
          })
          let handled = false
          socket.on("data", (chunk) => {
            const text = chunk.toString("latin1")
            if (handled || !text.includes("\r\n\r\n")) return
            handled = true
            if (text.startsWith("GET /control/capabilities ")) {
              const capabilities = encodeCapabilityDocument({
                maxBatchKeys: 4,
                maxBlobBytes: 4096,
              })
              socket.write([
                "HTTP/1.1 200 OK",
                "Connection: close",
                "Content-Type: application/octet-stream",
                `Content-Length: ${capabilities.length}`,
                "",
                "",
              ].join("\r\n"))
              socket.end(capabilities)
              return
            }
            stats.bodyBytesReceived += chunk.length
            ordinal = (stats.requests + 1) as 1 | 2
            stats.requests += 1
            stats.gets += 1
            const started = stats.requests === 1 ? firstStarted : secondStarted
            if (stall === "none") {
              stats.bodyBytesWritten += body.length
              socket.write([
                "HTTP/1.1 200 OK",
                "Connection: close",
                "Content-Type: application/octet-stream",
                `Content-Length: ${body.length}`,
                "",
                "",
              ].join("\r\n"))
              socket.end(body)
              Effect.runFork(Deferred.succeed(started, undefined))
              return
            }
            if (stall === "beforeHeaders") {
              // The request is received and nothing is ever written back.
              Effect.runFork(Deferred.succeed(started, undefined))
              return
            }
            socket.write([
              "HTTP/1.1 200 OK",
              "Connection: close",
              "Content-Type: application/octet-stream",
              "Transfer-Encoding: chunked",
              "",
              "",
            ].join("\r\n"))
            const partial = body.subarray(0, Math.max(1, Math.floor(body.length / 2)))
            stats.bodyBytesWritten += partial.length
            socket.write(`${partial.length.toString(16)}\r\n`)
            socket.write(partial)
            socket.write("\r\n")
            Effect.runFork(Deferred.succeed(started, undefined))
          })
        })
        server.once("error", (cause) => resume(Effect.die(cause)))
        server.listen(0, "127.0.0.1", () => {
          const address = server.address()
          if (address === null || typeof address === "string") {
            resume(Effect.die(new Error("gated peer did not bind TCP")))
            return
          }
          const close = Effect.callback<void>((closed) => {
            for (const socket of sockets) socket.destroy()
            sockets.clear()
            server.close(() => closed(Effect.void))
          })
          const endpoint: GatedEndpoint = {
              authority: `http://127.0.0.1:${address.port}`,
              observe: () => ({ ...stats, openSockets: sockets.size }),
              awaitRequest: (count) => Deferred.await(count === 1 ? firstStarted : secondStarted),
              awaitClosed: (count) => Deferred.await(count === 1 ? firstClosed : secondClosed),
          }
          registerSocketReleaseHook(endpoint, socketReleaseHook(sockets))
          resume(Effect.succeed({
            endpoint,
            close,
          }))
        })
        return Effect.sync(() => {
          for (const socket of sockets) socket.destroy()
          sockets.clear()
          server.close()
        })
      }),
      (managed) => managed.close,
    ).pipe(Effect.map((managed) => managed.endpoint))
  })
