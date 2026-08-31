import { Effect, Option } from "effect"
import type { Scope } from "effect"
import { createServer, type IncomingMessage, type ServerResponse } from "node:http"
import type { Socket } from "node:net"
import { registerSocketReleaseHook, socketReleaseHook } from "./ConformancePeer.ts"
import {
  decodeKeyListDocument,
  encodeCapabilityDocument,
} from "../../../src/internal/remoteControl.ts"
import type { PeerEndpoint, PeerObservation } from "./ConformancePeer.ts"

export interface CredentialObservation extends PeerObservation {
  /** Every request's Authorization header in arrival order, `undefined` where
   * the request carried none. */
  readonly authorizations: ReadonlyArray<string | undefined>
}

export interface CredentialEndpoint extends PeerEndpoint {
  readonly observe: () => CredentialObservation
}

export interface CredentialRealization {
  readonly nodes?: ReadonlyMap<string, Uint8Array>
  /**
   * Answer every data-plane and find-missing request with `401` and a
   * challenge header. The profile has no challenge negotiation at `/0`, so a
   * conforming client answers neither: `401` is terminal for its operation.
   */
  readonly unauthenticated?: boolean
}

/**
 * A peer that records the credential presentation on every request. The
 * capability probe always succeeds so a layer can be acquired even in the
 * unauthenticated realization, leaving the operation under test as the only
 * request the status table governs.
 */
export const serveCredentialPeer = (
  realization: CredentialRealization,
): Effect.Effect<CredentialEndpoint, never, Scope.Scope> =>
  Effect.acquireRelease(
    Effect.callback<{
      readonly endpoint: CredentialEndpoint
      readonly close: Effect.Effect<void>
    }>((resume) => {
      const nodes = new Map(realization.nodes ?? [])
      const sockets = new Set<Socket>()
      const authorizations: Array<string | undefined> = []
      const stats = {
        requests: 0,
        gets: 0,
        puts: 0,
        bodyBytesWritten: 0,
        bodyBytesReceived: 0,
      }

      const readBody = (request: IncomingMessage): Promise<Uint8Array> =>
        new Promise((resolve, reject) => {
          const chunks: Array<Uint8Array> = []
          request.on("data", (chunk: Buffer) => chunks.push(new Uint8Array(chunk)))
          request.on("error", reject)
          request.on("end", () => {
            const length = chunks.reduce((sum, chunk) => sum + chunk.length, 0)
            const bytes = new Uint8Array(length)
            let offset = 0
            for (const chunk of chunks) {
              bytes.set(chunk, offset)
              offset += chunk.length
            }
            resolve(bytes)
          })
        })

      const handler = (request: IncomingMessage, response: ServerResponse) => {
        response.setHeader("connection", "close")
        stats.requests += 1
        authorizations.push(request.headers["authorization"])

        if (request.url === "/control/capabilities") {
          const bytes = encodeCapabilityDocument({ maxBatchKeys: 4, maxBlobBytes: 4096 })
          stats.bodyBytesWritten += bytes.length
          response.writeHead(200, {
            "content-length": bytes.length,
            "content-type": "application/octet-stream",
          })
          response.end(bytes)
          return
        }

        const deny = () => {
          response.writeHead(401, {
            "content-length": 0,
            "www-authenticate": "Bearer realm=\"cas\"",
          }).end()
        }

        if (request.url === "/control/missing") {
          stats.gets += 1
          if (realization.unauthenticated === true) {
            deny()
            return
          }
          void readBody(request).then((body) => {
            stats.bodyBytesReceived += body.length
            const decoded = decodeKeyListDocument(body)
            if (Option.isNone(decoded)) {
              response.writeHead(400).end()
              return
            }
            const statuses = Uint8Array.from(decoded.value, (key) => nodes.has(key) ? 1 : 0)
            stats.bodyBytesWritten += statuses.length
            response.writeHead(200, {
              "content-length": statuses.length,
              "content-type": "application/octet-stream",
            })
            response.end(statuses)
          }, () => response.destroy())
          return
        }

        if (/^\/roots\/[0-9a-f]{64}$/.test(request.url ?? "")) {
          if (realization.unauthenticated === true) {
            deny()
            return
          }
          void readBody(request).then(() => response.writeHead(204).end(), () => response.destroy())
          return
        }

        const match = /^\/cas\/([0-9a-f]{64})$/.exec(request.url ?? "")
        const id = match?.[1]
        if (id === undefined) {
          response.writeHead(400).end()
          return
        }
        if (realization.unauthenticated === true) {
          if (request.method === "PUT") stats.puts += 1
          else stats.gets += 1
          deny()
          return
        }
        if (request.method === "PUT") {
          stats.puts += 1
          void readBody(request).then((bytes) => {
            stats.bodyBytesReceived += bytes.length
            nodes.set(id, bytes.slice())
            response.writeHead(201).end()
          }, () => response.destroy())
          return
        }
        stats.gets += 1
        const bytes = nodes.get(id)
        if (bytes === undefined) {
          response.writeHead(404).end()
          return
        }
        stats.bodyBytesWritten += bytes.length
        response.writeHead(200, {
          "content-length": bytes.length,
          "content-type": "application/octet-stream",
        })
        response.end(bytes)
      }

      const server = createServer(handler)
      server.on("connection", (socket) => {
        sockets.add(socket)
        socket.on("error", () => undefined)
        socket.once("close", () => sockets.delete(socket))
      })
      server.once("error", (cause) => resume(Effect.die(cause)))
      server.listen(0, "127.0.0.1", () => {
        const address = server.address()
        if (address === null || typeof address === "string") {
          resume(Effect.die(new Error("credential peer did not bind TCP")))
          return
        }
        const close = Effect.callback<void>((closed) => {
          for (const socket of sockets) socket.destroy()
          sockets.clear()
          server.close(() => closed(Effect.void))
        })
        const endpoint: CredentialEndpoint = {
          authority: `http://127.0.0.1:${address.port}`,
          observe: () => ({
            ...stats,
            openSockets: sockets.size,
            authorizations: [...authorizations],
          }),
        }
        registerSocketReleaseHook(endpoint, socketReleaseHook(sockets))
        resume(Effect.succeed({ endpoint, close }))
      })

      return Effect.sync(() => {
        for (const socket of sockets) socket.destroy()
        sockets.clear()
        server.close()
      })
    }),
    (managed) => managed.close,
  ).pipe(Effect.map((managed) => managed.endpoint))
