import { Effect, Option } from "effect"
import { createHash } from "node:crypto"
import { createServer, type IncomingMessage, type ServerResponse } from "node:http"
import type { Socket } from "node:net"
import { registerSocketReleaseHook, socketReleaseHook } from "./ConformancePeer.ts"
import {
  decodeKeyListDocument,
  encodeCapabilityDocument,
} from "../../../src/internal/remoteControl.ts"
import type {
  ConformancePeer,
  PeerEndpoint,
  PeerObservation,
  ScenarioRealization,
} from "./ConformancePeer.ts"

const digest = (bytes: Uint8Array): string =>
  createHash("sha256").update(bytes).digest("hex")

const readRequest = (request: IncomingMessage): Promise<Uint8Array> =>
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

export const ReferencePeer: ConformancePeer = {
  name: "node-reference-cas-http-0",
  capabilities: { profile: "cas-http/0", supportsUpload: true },
  serve: (realization: ScenarioRealization) => Effect.acquireRelease(
    Effect.callback<{ readonly endpoint: PeerEndpoint; readonly close: Effect.Effect<void> }>((resume) => {
      const nodes = new Map(realization.nodes ?? [])
      const roots = new Set<string>()
      const sockets = new Set<Socket>()
      const stats = {
        requests: 0,
        gets: 0,
        puts: 0,
        bodyBytesWritten: 0,
        bodyBytesReceived: 0,
        putIds: [] as Array<string>,
        publishedRoots: [] as Array<string>,
        events: [] as Array<string>,
      }

      const handler = (request: IncomingMessage, response: ServerResponse) => {
        response.setHeader("connection", "close")
        stats.requests += 1
        if (request.headers["cas-profile"] !== "cas-http/0") {
          response.writeHead(400).end()
          return
        }
        if (request.url === "/control/capabilities") {
          if (request.method !== "GET") {
            response.writeHead(405).end()
            return
          }
          const bytes = encodeCapabilityDocument(realization.capabilities ?? {
            maxBatchKeys: 4,
            maxBlobBytes: 4096,
          })
          response.writeHead(200, {
            "content-length": bytes.length,
            "content-type": "application/octet-stream",
          })
          response.end(bytes)
          return
        }
        if (request.url === "/control/missing") {
          if (request.method !== "POST"
            || request.headers["content-type"] !== "application/octet-stream") {
            response.writeHead(400).end()
            return
          }
          void readRequest(request).then((body) => {
            stats.bodyBytesReceived += body.length
            const decoded = decodeKeyListDocument(body)
            if (Option.isNone(decoded)) {
              response.writeHead(400).end()
              return
            }
            stats.events.push(`missing:${decoded.value.length}`)
            const statuses = Uint8Array.from(decoded.value, (key) =>
              realization.reportedMissing?.has(key) === true
                ? 0
                : nodes.has(key)
                ? 1
                : 0)
            stats.bodyBytesWritten += statuses.length
            response.writeHead(200, {
              "content-length": statuses.length,
              "content-type": "application/octet-stream",
            })
            response.end(statuses)
          }, () => response.destroy())
          return
        }
        const rootMatch = /^\/roots\/([0-9a-f]{64})$/.exec(request.url ?? "")
        if (rootMatch !== null) {
          if (request.method !== "PUT"
            || request.headers["content-type"] !== "application/octet-stream") {
            response.writeHead(400).end()
            return
          }
          const root = rootMatch[1]
          if (root === undefined) {
            response.writeHead(400).end()
            return
          }
          void readRequest(request).then((body) => {
            stats.bodyBytesReceived += body.length
            const closure = decodeKeyListDocument(body)
            if (Option.isNone(closure)) {
              response.writeHead(400).end()
              return
            }
            if (!nodes.has(root) || closure.value.some((key) => !nodes.has(key))) {
              response.writeHead(409).end()
              return
            }
            roots.add(root)
            stats.publishedRoots.push(root)
            stats.events.push(`publish:${root}`)
            const acknowledgement = realization.publishAcknowledgementBody
            if (acknowledgement === undefined) {
              response.writeHead(204).end()
            } else {
              response.writeHead(200, {
                "content-length": acknowledgement.length,
                "content-type": realization.acknowledgementContentType
                  ?? "application/octet-stream",
              })
              response.end(acknowledgement)
            }
          }, () => response.destroy())
          return
        }
        const match = /^\/cas\/([0-9a-f]{64})$/.exec(request.url ?? "")
        if (match === null) {
          response.writeHead(400).end()
          return
        }
        const id = match[1]
        if (id === undefined) {
          response.writeHead(400).end()
          return
        }
        if (request.method === "GET") {
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
          return
        }
        if (request.method === "PUT") {
          stats.puts += 1
          void readRequest(request).then((bytes) => {
            stats.bodyBytesReceived += bytes.length
            if (digest(bytes) !== id) {
              response.writeHead(409).end()
              return
            }
            nodes.set(id, bytes.slice())
            stats.putIds.push(id)
            stats.events.push(`put:${id}`)
            const acknowledgement = realization.uploadAcknowledgementBody
            if (acknowledgement === undefined) {
              response.writeHead(201).end()
            } else {
              response.writeHead(201, {
                "content-length": acknowledgement.length,
                "content-type": realization.acknowledgementContentType
                  ?? "application/octet-stream",
              })
              response.end(acknowledgement)
            }
          }, () => response.destroy())
          return
        }
        response.writeHead(405).end()
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
          resume(Effect.die(new Error("reference peer did not bind TCP")))
          return
        }
        const observe = (): PeerObservation => ({
          ...stats,
          putIds: [...stats.putIds],
          publishedRoots: [...stats.publishedRoots],
          events: [...stats.events],
          openSockets: sockets.size,
        })
        const close = Effect.callback<void>((closed) => {
          for (const socket of sockets) socket.destroy()
          sockets.clear()
          server.close(() => closed(Effect.void))
        })
        const endpoint: PeerEndpoint = {
          authority: `http://127.0.0.1:${address.port}`,
          observe,
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
  ).pipe(Effect.map((managed) => managed.endpoint)),
}
