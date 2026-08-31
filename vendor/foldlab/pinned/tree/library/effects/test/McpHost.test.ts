/**
 * The MCP host, driven the way a client drives it: newline-delimited
 * JSON-RPC into the `Stdio` service the transport reads, and the
 * frames it writes back read off the same seam. No handler is called
 * directly — every assertion here is about what came out of the
 * protocol, over a real store on disk.
 *
 * Two claims are under test and they are different claims. The first
 * is AGREEMENT: what this host serves is what `lake exe mcpspec`
 * emitted, name for name and code for code — and the tripwire trips
 * when it is not. The second is BEHAVIOUR: the tools are the store's
 * own verbs, so a node admitted through `cas_put` loads back through
 * `cas_load` byte for byte, publishes, and lists.
 */
import { describe, expect, it } from "@effect/vitest"
import { Effect, Fiber, Layer, Path, Sink, Stdio, Stream } from "effect"
import { Cas } from "../src/index.ts"
import { defaultServePolicy, type ServePolicy } from "../bin/cli/store.ts"
import {
  assertAgreement,
  manifestPath,
  readManifest,
  type ServedTool,
} from "../bin/mcp/manifest.ts"
import { applyServePolicy, gateOnManifest, layerServeStdio } from "../bin/mcp/server.ts"
import { servedTools } from "../bin/mcp/tools.ts"
import { layerDisk, layerDiskFs, withStoreRoot } from "./fixtures/diskFs.ts"

const encoder = new TextEncoder()
const decoder = new TextDecoder()

interface JsonRpcFrame {
  readonly id?: number
  readonly result?: Record<string, unknown>
  readonly error?: Record<string, unknown>
}

/** One stdio session: the frames go in, the server answers, and the
 * session ends once every request that carried an id has been
 * answered. Server notifications arrive on the same pipe and carry no
 * id, so they are counted out — waiting on a frame COUNT would end the
 * session on `notifications/tools/list_changed` and read the reply
 * that had not arrived yet.
 *
 * stdin never closes: closing it is how the transport signals
 * shutdown, and a shutdown racing the last write is not what these
 * cases are about. */
const session = (requests: ReadonlyArray<unknown>) =>
  Effect.gen(function* () {
    const awaited = requests
      .map((request) => (request as { readonly id?: number }).id)
      .filter((id): id is number => id !== undefined)
    const written: Array<string> = []
    const layerStdio = Stdio.layerTest({
      stdin: Stream.fromIterable(
        requests.map((request) => encoder.encode(`${JSON.stringify(request)}\n`)),
      ).pipe(Stream.concat(Stream.never)),
      stdout: () =>
        Sink.forEach((chunk: string | Uint8Array) =>
          Effect.sync(() => {
            written.push(typeof chunk === "string" ? chunk : decoder.decode(chunk))
          })
        ),
      stderr: () => Sink.drain,
    })

    const frames = (): ReadonlyArray<JsonRpcFrame> =>
      written
        .join("")
        .split("\n")
        .filter((line) => line.length > 0)
        .map((line) => JSON.parse(line) as JsonRpcFrame)

    // One provide over one composed layer (not a provide chain):
    // layerStdio feeds the host, both outputs exposed, one lifecycle.
    const server = yield* Effect.forkChild(
      Effect.never.pipe(
        Effect.provide(layerServeStdio({
          maxNodeBytes: defaultServePolicy.maxNodeBytes,
          maxInFlight: defaultServePolicy.maxInFlight,
        }).pipe(Layer.provideMerge(layerStdio))),
      ),
    )

    const answered = (): boolean => {
      const ids = new Set(frames().map((frame) => frame.id))
      return awaited.every((id) => ids.has(id))
    }
    for (let waited = 0; waited < 400 && !answered(); waited += 1) {
      yield* Effect.sleep("5 millis")
    }
    yield* Fiber.interrupt(server)
    return frames()
  })

/** The client half of `initialize`, plus the notification that
 * completes the handshake. Every session opens with these. */
const handshake: ReadonlyArray<unknown> = [
  {
    jsonrpc: "2.0",
    id: 1,
    method: "initialize",
    params: {
      protocolVersion: "2025-06-18",
      capabilities: {},
      clientInfo: { name: "foldlab-test", version: "0" },
    },
  },
  { jsonrpc: "2.0", method: "notifications/initialized" },
]

const call = (id: number, name: string, args: Record<string, unknown>): unknown => ({
  jsonrpc: "2.0",
  id,
  method: "tools/call",
  params: { name, arguments: args },
})

/** The structured reply of a `tools/call`, which is where a tool's
 * described result lands. */
const structured = (frame: JsonRpcFrame | undefined): Record<string, unknown> => {
  const result = frame?.result
  expect(result, `frame carried no result: ${JSON.stringify(frame)}`).toBeDefined()
  expect(result?.["isError"], `tool reported an error: ${JSON.stringify(result)}`)
    .not.toBe(true)
  return result?.["structuredContent"] as Record<string, unknown>
}

const replyTo = (frames: ReadonlyArray<JsonRpcFrame>, id: number) =>
  frames.find((frame) => frame.id === id)

/** "hello", as the node document spells a payload. */
const helloHex = "68656c6c6f"

describe("the MCP host agrees with the emitted manifest", () => {
  it.effect("the served table is the manifest's, row for row", () =>
    Effect.gen(function* () {
      const path = yield* manifestPath
      const manifest = yield* readManifest(path)
      yield* assertAgreement(manifest, servedTools)
      expect(manifest.tools.map((tool) => tool.name)).toEqual([
        "cas_put",
        "cas_load",
        "cas_run",
        "cas_run_ref",
        "cas_publish_root",
        "cas_list_roots",
      ])
    }).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer))))

  it.effect("a table that drifts from the manifest refuses the boot", () =>
    Effect.gen(function* () {
      const path = yield* manifestPath
      const manifest = yield* readManifest(path)
      // Three separate drifts, each on its own: a renamed tool, a
      // reworded description, and a params code that lost a field.
      const drifted: ReadonlyArray<ServedTool> = servedTools.map((tool, index) =>
        index === 0
          ? { ...tool, name: "cas_admit" }
          : index === 1
          ? { ...tool, description: "load a node" }
          : index === 5
          ? { ...tool, result: { _tag: "Struct", fields: {} } }
          : tool
      )
      const refusal = yield* Effect.flip(assertAgreement(manifest, drifted))
      expect(refusal.differences.some((line) => line.includes("cas_admit"))).toBe(true)
      expect(refusal.differences).toContain("cas_load: description differs from the manifest")
      expect(
        refusal.differences.some((line) => line.startsWith("cas_list_roots: result code differs")),
      ).toBe(true)
    }).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer))))

  it.effect("the boot gate passes against the generated document", () =>
    gateOnManifest.pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer))))
})

describe("the serve policy", () => {
  it.effect("honors maxNodeBytes and names what stdio cannot use", () =>
    Effect.gen(function* () {
      const limits = yield* applyServePolicy(defaultServePolicy)
      expect(limits.maxNodeBytes).toBe(defaultServePolicy.maxNodeBytes)
    }))

  it.effect("refuses a store whose policy gates reads", () =>
    Effect.gen(function* () {
      const gated: ServePolicy = {
        ...defaultServePolicy,
        anonymousReads: false,
        credentialEnv: "CAS_TOKEN",
      }
      const refusal = yield* Effect.flip(applyServePolicy(gated))
      expect(refusal.credentialEnv).toBe("CAS_TOKEN")
      expect(refusal.message).toContain("stdio cannot check one")
    }))
})

describe("the six tools, over the protocol", () => {
  it.live("lists exactly the manifest's tools, with its own descriptions", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const path = yield* manifestPath
        const manifest = yield* readManifest(path)
        const frames = yield* session(
          [...handshake, { jsonrpc: "2.0", id: 2, method: "tools/list" }],
        )
        const listed = replyTo(frames, 2)?.result?.["tools"] as ReadonlyArray<
          { readonly name: string; readonly description: string }
        >
        expect(listed.map((tool) => tool.name)).toEqual(
          manifest.tools.map((tool) => tool.name),
        )
        expect(listed.map((tool) => tool.description)).toEqual(
          manifest.tools.map((tool) => tool.description),
        )
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))

  it.live("admits a node and loads it back, byte for byte", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const admitted = yield* session([
          ...handshake,
          call(2, "cas_put", {
            version: Cas.SchemeVersion,
            tag: 1,
            payload: helloHex,
            refs: [],
          }),
        ])
        const address = structured(replyTo(admitted, 2))["address"] as string
        expect(address).toMatch(/^[0-9a-f]{64}$/u)

        // A second session over the SAME store: the address is the
        // only thing carried across, which is the whole claim of a
        // content-addressed store.
        //
        // One call per session, because calls within a session are not
        // ordered — the server answers them as they are dispatched, so
        // a listing sent beside a publication may legitimately be
        // answered first. Sequencing is the CLIENT's, and here that is
        // the session boundary.
        const read = yield* session([...handshake, call(2, "cas_load", { address })])
        expect(structured(replyTo(read, 2))).toEqual({
          version: Cas.SchemeVersion,
          tag: 1,
          payload: helloHex,
          refs: [],
        })

        const published = yield* session([
          ...handshake,
          call(2, "cas_publish_root", { address }),
        ])
        expect(structured(replyTo(published, 2))).toEqual({})

        const listed = yield* session([...handshake, call(2, "cas_list_roots", {})])
        expect(structured(replyTo(listed, 2))).toEqual({ roots: [address] })
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))

  it.live("runs a straight-line program and answers the word", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const frames = yield* session([
          ...handshake,
          call(2, "cas_run", {
            instructions: [
              {
                _tag: "put",
                version: Cas.SchemeVersion,
                tag: 1,
                payloadHex: helloHex,
                refs: [],
              },
              {
                _tag: "put",
                version: Cas.SchemeVersion,
                tag: 9,
                payloadHex: "",
                // The second instruction names the first answer by
                // index. Since queue item 22 an operand can also be a
                // literal address, and an instruction can be a load;
                // this one stays inside the older fragment on purpose,
                // so the growth is additive here rather than a rewrite.
                refs: [{ expectedTag: 1, source: { _tag: "answer", index: 0 } }],
              },
            ],
          }),
        ])

        const word = structured(replyTo(frames, 2))["word"] as ReadonlyArray<
          { readonly address: string }
        >
        expect(word).toHaveLength(2)
        for (const entry of word) expect(entry.address).toMatch(/^[0-9a-f]{64}$/u)

        // Every answer of the word is in the store, and the linked
        // node loads with the link the program gave it.
        const loaded = yield* session([
          ...handshake,
          call(2, "cas_load", { address: word[1]?.address ?? "" }),
        ])
        expect(structured(replyTo(loaded, 2))["refs"]).toEqual([
          { expectedTag: 1, id: word[0]?.address },
        ])

        // A run admits; it never publishes.
        const listed = yield* session([...handshake, call(3, "cas_list_roots", {})])
        expect(structured(replyTo(listed, 3))).toEqual({ roots: [] })
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))

  it.live("refuses a reference that names an answer not yet given", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const frames = yield* session([
          ...handshake,
          call(2, "cas_run", {
            instructions: [{
              _tag: "put",
              version: Cas.SchemeVersion,
              tag: 9,
              payloadHex: "",
              refs: [{ expectedTag: 1, source: { _tag: "answer", index: 0 } }],
            }],
          }),
        ])
        const result = replyTo(frames, 2)?.result
        expect(result?.["isError"]).toBe(true)
        expect(JSON.stringify(result)).toContain("EARLIER answer by index")
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))

  it.live("refuses a load of an address the store does not hold", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const absent = "0".repeat(64)
        const frames = yield* session(
          [...handshake, call(2, "cas_load", { address: absent })],
        )
        const result = replyTo(frames, 2)?.result
        expect(result?.["isError"]).toBe(true)
        // The clause arrives in the estate's own words, the same ones
        // `cas show` prints.
        expect(JSON.stringify(result)).toContain("nothing in the store at")
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))
})
