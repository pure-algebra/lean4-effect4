/**
 * The real server bound as a conformance peer: the production
 * `makeCasHttpApp` dispatcher converted to a web handler and served over
 * the same socket harness the reference peer uses. Client-versus-server
 * differential runs are handler substitution — the network is only the
 * bridge, the semantics are the shipped server core.
 */
import { Context, Effect, Layer } from "effect"
import { HttpEffect } from "effect/unstable/http"
import { createServer, type IncomingMessage, type ServerResponse } from "node:http"
import type { Socket } from "node:net"
import { ByteWriter, layerMemoryBackend } from "../../../src/cas/Backend.ts"
import { ContentId } from "../../../src/cas/Node.ts"
import { layerAddressSha256Live } from "../../../src/cas/Store.ts"
import { CasServerCore } from "../../../src/server/Core.ts"
import { makeCasHttpApp } from "../../../src/server/HttpApp.ts"
import type { CasServerPolicy } from "../../../src/server/Protocol.ts"
import {
  registerSocketReleaseHook,
  socketReleaseHook,
  type ConformancePeer,
  type PeerEndpoint,
  type PeerObservation,
  type ScenarioRealization,
} from "./ConformancePeer.ts"

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

const webHeaders = (request: IncomingMessage): Headers => {
  const headers = new Headers()
  for (const [name, value] of Object.entries(request.headers)) {
    if (typeof value === "string") headers.set(name, value)
    else if (Array.isArray(value)) headers.set(name, value.join(", "))
  }
  return headers
}

export interface EffectPeerOptions {
  readonly policy?: Partial<CasServerPolicy>
}

export const makeEffectPeer = (options: EffectPeerOptions = {}): ConformancePeer => ({
  name: "effect-cas-http-0-server",
  capabilities: { profile: "cas-http/0", supportsUpload: true },
  serve: (realization: ScenarioRealization) => Effect.gen(function* () {
    const policy: CasServerPolicy = {
      maxBatchKeys: realization.capabilities?.maxBatchKeys ?? 4,
      maxNodeBytes: realization.capabilities?.maxBlobBytes ?? 4096,
      ...options.policy,
    }
    // The topology seam in one expression: the semantic core over
    // whichever backend layer this peer chooses to stand on.
    const context = yield* Layer.build(
      CasServerCore.layer(policy).pipe(
        Layer.provideMerge(Layer.mergeAll(
          layerMemoryBackend,
          layerAddressSha256Live,
        )),
      ),
    )
    const writer = Context.get(context, ByteWriter)
    for (const [id, bytes] of realization.nodes ?? []) {
      // Seeded nodes are peer-granted facts; the memory backend cannot
      // actually fail, so a refusal here is a harness defect.
      yield* writer.putBytes(ContentId.make(id), bytes).pipe(Effect.orDie)
    }

    const app = yield* makeCasHttpApp(policy).pipe(Effect.provide(context))
    const webHandler = HttpEffect.toWebHandler(app)

    return yield* Effect.acquireRelease(
      Effect.callback<{
        readonly endpoint: PeerEndpoint
        readonly close: Effect.Effect<void>
      }>((resume) => {
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
          const method = request.method ?? "GET"
          const path = request.url ?? "/"
          const casHex = /^\/cas\/([0-9a-f]{64})$/.exec(path)?.[1]
          const rootHex = /^\/roots\/([0-9a-f]{64})$/.exec(path)?.[1]
          if (method === "GET" && casHex !== undefined) stats.gets += 1
          if (method === "PUT" && casHex !== undefined) stats.puts += 1

          void readRequest(request).then(async (body) => {
            stats.bodyBytesReceived += body.length
            const webRequest = new Request(`http://cas.local${path}`, {
              method,
              headers: webHeaders(request),
              ...(method === "GET" || method === "HEAD"
                ? {}
                : { body: body.slice().buffer as ArrayBuffer }),
            })
            const webResponse = await webHandler(webRequest)
            const bytes = new Uint8Array(await webResponse.arrayBuffer())
            if (webResponse.status < 300) {
              if (method === "PUT" && casHex !== undefined && webResponse.status === 201) {
                stats.putIds.push(casHex)
                stats.events.push(`put:${casHex}`)
              }
              if (method === "PUT" && rootHex !== undefined) {
                stats.publishedRoots.push(rootHex)
                stats.events.push(`publish:${rootHex}`)
              }
              if (path === "/control/missing") stats.events.push("missing")
            }
            const headers: Record<string, string> = {}
            webResponse.headers.forEach((value, name) => {
              headers[name] = value
            })
            if (bytes.length > 0) headers["content-length"] = String(bytes.length)
            response.writeHead(webResponse.status, headers)
            stats.bodyBytesWritten += bytes.length
            if (bytes.length > 0) response.end(bytes)
            else response.end()
          }, () => response.destroy())
        }

        const server = createServer(handler)
        server.on("connection", (socket) => {
          sockets.add(socket)
          socket.on("error", () => undefined)
          socket.once("close", () => sockets.delete(socket))
        })
        server.once("error", (cause) => resume(Effect.die(cause)))
        server.listen(0, "127.0.0.1", () => {
          const bound = server.address()
          if (bound === null || typeof bound === "string") {
            resume(Effect.die(new Error("effect peer did not bind TCP")))
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
            authority: `http://127.0.0.1:${bound.port}`,
            observe,
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
  }),
})

export const EffectPeer: ConformancePeer = makeEffectPeer()
