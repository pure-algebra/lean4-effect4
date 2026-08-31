import { Effect, Option, Schema } from "effect"
import { createServer, type Socket } from "node:net"
import { registerSocketReleaseHook, socketReleaseHook } from "./ConformancePeer.ts"
import { encodeCapabilityDocument } from "../../../src/internal/remoteControl.ts"
import type {
  ConformancePeer,
  PeerEndpoint,
  PeerObservation,
  ScenarioRealization,
} from "./ConformancePeer.ts"

export const HostileFault = Schema.Literals([
  "complete",
  "truncated",
  "contentLengthLarger",
  "declaredOversize",
  "underreportedOversize",
  "chunkedOversize",
  "wrongBytes",
  "notFound",
  "resetMidBody",
  "cancellationMidDownload",
  "cancellationMidUpload",
  "redirect",
  "contentEncoding",
  "contentEncodingAck",
  "contentEncodingAck204",
  "rateLimitedAbsent",
  "rateLimitedDate",
  "rateLimitedNumeric",
  "capabilitiesMissing",
  "capabilitiesTruncated",
  "missingMalformed",
])
export type HostileFault = typeof HostileFault.Type

const headers = (status: string, values: ReadonlyArray<readonly [string, string]> = []): string =>
  [
    `HTTP/1.1 ${status}`,
    "Connection: close",
    ...values.map(([name, value]) => `${name}: ${value}`),
    "",
    "",
  ].join("\r\n")

export const HostilePeer: ConformancePeer = {
  name: "node-raw-hostile-cas-http-0",
  capabilities: { profile: "cas-http/0", supportsUpload: true },
  serve: (realization: ScenarioRealization) => Effect.acquireRelease(
    Effect.callback<{ readonly endpoint: PeerEndpoint; readonly close: Effect.Effect<void> }>((resume) => {
      const decodedFault = Schema.decodeUnknownOption(HostileFault)(realization.fault)
      if (Option.isNone(decodedFault)) {
        resume(Effect.die(new Error("hostile peer requires a declared fault realization")))
        return Effect.void
      }
      const fault = decodedFault.value
      const body = realization.body ?? new Uint8Array()
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
        socket.on("error", () => undefined)
        socket.once("close", () => sockets.delete(socket))
        let handled = false
        socket.on("data", (chunk) => {
          stats.bodyBytesReceived += chunk.length
          if (handled) {
            if (fault === "cancellationMidUpload") socket.destroy()
            return
          }
          const text = chunk.toString("latin1")
          const separator = text.indexOf("\r\n\r\n")
          if (separator < 0) return
          handled = true
          stats.requests += 1
          if (text.startsWith("GET /control/capabilities ")) {
            if (fault === "capabilitiesMissing") {
              socket.end(headers("404 Not Found", [["Content-Length", "0"]]))
              return
            }
            if (fault === "capabilitiesTruncated") {
              const truncated = Uint8Array.of(0, 0, 0, 4, 0)
              socket.write(headers("200 OK", [
                ["Content-Type", "application/octet-stream"],
                ["Content-Length", String(truncated.length)],
              ]))
              socket.end(truncated)
              return
            }
            const capabilities = encodeCapabilityDocument({
              maxBatchKeys: 4,
              maxBlobBytes: 4096,
            })
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Content-Length", String(capabilities.length)],
            ]))
            socket.end(capabilities)
            return
          }
          if (text.startsWith("POST /control/missing ") && fault === "missingMalformed") {
            stats.gets += 1
            const malformed = Uint8Array.of(3)
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Content-Length", String(malformed.length)],
            ]))
            socket.end(malformed)
            return
          }
          const isPut = text.startsWith("PUT ")
          if (isPut) stats.puts += 1
          else stats.gets += 1

          if (fault === "notFound") {
            socket.end(headers("404 Not Found", [["Content-Length", "0"]]))
            return
          }
          if (fault === "redirect") {
            socket.end(headers("302 Found", [
              ["Location", `http://127.0.0.1:${String((server.address() as { port: number }).port)}/cas/redirected`],
              ["Content-Length", "0"],
            ]))
            return
          }
          if (fault === "rateLimitedAbsent"
            || fault === "rateLimitedDate"
            || fault === "rateLimitedNumeric") {
            const retryAfter = fault === "rateLimitedDate"
              ? [["Retry-After", "Wed, 21 Oct 2015 07:28:00 GMT"]] as const
              : fault === "rateLimitedNumeric"
              ? [["Retry-After", "17"]] as const
              : []
            socket.end(headers("429 Too Many Requests", [
              ["Content-Length", "0"],
              ...retryAfter,
            ]))
            return
          }
          if ((fault === "contentEncodingAck" || fault === "contentEncodingAck204") && isPut) {
            socket.end(headers(
              fault === "contentEncodingAck204" ? "204 No Content" : "201 Created",
              [
              ["Content-Type", "application/octet-stream"],
              ["Content-Encoding", "gzip"],
              ["Content-Length", "0"],
              ],
            ))
            return
          }
          if (fault === "declaredOversize") {
            socket.end(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Content-Length", String(realization.declared ?? body.length)],
            ]))
            return
          }
          if (fault === "cancellationMidUpload" && isPut) {
            if (stats.puts === 1) socket.destroy()
            else socket.end(headers("201 Created", [["Content-Length", "0"]]))
            return
          }

          if (fault === "truncated") {
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Content-Length", String(body.length + 8)],
            ]))
            const partial = body.subarray(0, Math.max(1, Math.floor(body.length / 2)))
            stats.bodyBytesWritten += partial.length
            socket.write(partial)
            socket.destroy()
            return
          }
          if (fault === "contentLengthLarger") {
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Content-Length", String(body.length + 1)],
            ]))
            stats.bodyBytesWritten += body.length
            socket.end(body)
            return
          }
          if (fault === "resetMidBody") {
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Transfer-Encoding", "chunked"],
            ]))
            const partial = body.subarray(0, Math.max(1, Math.floor(body.length / 2)))
            stats.bodyBytesWritten += partial.length
            socket.write(`${partial.length.toString(16)}\r\n`)
            socket.write(partial)
            socket.write("\r\n")
            socket.destroy()
            return
          }
          if (fault === "chunkedOversize") {
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Transfer-Encoding", "chunked"],
            ]))
            stats.bodyBytesWritten += body.length
            socket.write(`${body.length.toString(16)}\r\n`)
            socket.write(body)
            socket.end("\r\n0\r\n\r\n")
            return
          }
          if (fault === "cancellationMidDownload") {
            socket.write(headers("200 OK", [
              ["Content-Type", "application/octet-stream"],
              ["Transfer-Encoding", "chunked"],
            ]))
            const partial = body.subarray(0, Math.max(1, Math.floor(body.length / 2)))
            stats.bodyBytesWritten += partial.length
            socket.write(`${partial.length.toString(16)}\r\n`)
            socket.write(partial)
            socket.write("\r\n")
            return
          }

          const payload = fault === "wrongBytes"
            ? Uint8Array.from(body, (byte, index) => index === 0 ? byte ^ 0xff : byte)
            : body
          const declared = fault === "underreportedOversize"
            ? Math.max(0, payload.length - 1)
            : payload.length
          stats.bodyBytesWritten += payload.length
          socket.write(headers("200 OK", [
            ["Content-Type", "application/octet-stream"],
            ...(fault === "contentEncoding"
              ? [["Content-Encoding", "gzip"]] as const
              : []),
            ["Content-Length", String(declared)],
          ]))
          socket.end(payload)
        })
      })

      server.once("error", (cause) => resume(Effect.die(cause)))
      server.listen(0, "127.0.0.1", () => {
        const address = server.address()
        if (address === null || typeof address === "string") {
          resume(Effect.die(new Error("hostile peer did not bind TCP")))
          return
        }
        const observe = (): PeerObservation => ({ ...stats, openSockets: sockets.size })
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
