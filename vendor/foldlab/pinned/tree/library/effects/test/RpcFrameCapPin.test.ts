/**
 * Upstream pin — the NDJSON frame cap THROWS, and we notice if that
 * changes (ruling R1's upstream half).
 *
 * The stdio transport's silent-loss defect has two parts. Ours is
 * closed: BS-1 clamps `maxNodeBytes` so this host's own typed refusal
 * fires before the transport's cap can (`bin/mcp/server.ts`,
 * `test/McpBackpressure.test.ts`). Upstream's part is that an
 * oversized frame is not refused but THROWN — `RpcSerialization`'s
 * NDJSON parser raises `MaxBufferSizeExceeded` inside the transport's
 * stream, where `RpcServer` sandboxes, logs, and retries every 500 ms
 * and NEVER ANSWERS the requests buffered in the dropped frame data
 * (`RpcServer.ts:1295-1313` at the pin).
 *
 * This suite pins the upstream behavior itself, at the seam: the
 * default parser (the exact one `McpServer.layerStdio` builds, with no
 * options) throws at 16 MiB with the tagged error, and parses cleanly
 * under it. If a version bump makes either assertion fail, upstream
 * changed the contract BS-1's clamp is computed against — recompute
 * `maxServableNodeBytes` or retire the clamp, deliberately, before
 * green is restored.
 *
 * The daemon's HTTP transport is deliberately different and needs no
 * pin: an oversized body there is refused by `maxRequestBodySize` with
 * an HTTP status — answered, never lost.
 */
import { describe, expect, it } from "@effect/vitest"
import { RpcSerialization } from "effect/unstable/rpc"
import { transportFrameBytes } from "../bin/mcp/server.ts"

const frame = (bytes: number): string =>
  `${JSON.stringify({ pad: "a".repeat(bytes) })}\n`

describe("upstream pin — RpcSerialization NDJSON frame cap", () => {
  it("the option-less parser's cap is exactly the number the clamp is computed against", () => {
    // A frame one byte over the cap, without its newline yet: the
    // residual-buffer check fires.
    const parser = RpcSerialization.ndjson.makeUnsafe()
    let thrown: unknown
    try {
      parser.decode("a".repeat(transportFrameBytes + 1))
    } catch (error) {
      thrown = error
    }
    expect(thrown).toBeDefined()
    const tagged = thrown as { readonly _tag?: string; readonly maxBufferSize?: number }
    expect(tagged._tag).toBe("MaxBufferSizeExceeded")
    expect(tagged.maxBufferSize).toBe(transportFrameBytes)
    expect(tagged.maxBufferSize).toBe(16 * 1024 * 1024)
  })

  it("a complete oversized line throws rather than answering — the loss is upstream's, not a parse error", () => {
    const parser = RpcSerialization.ndjson.makeUnsafe()
    let thrown: unknown
    try {
      parser.decode(frame(transportFrameBytes))
    } catch (error) {
      thrown = error
    }
    expect((thrown as { readonly _tag?: string })._tag).toBe("MaxBufferSizeExceeded")
  })

  it("a frame under the cap decodes exactly", () => {
    const parser = RpcSerialization.ndjson.makeUnsafe()
    const decoded = parser.decode(`${JSON.stringify({ jsonrpc: "2.0", id: 1 })}\n`)
    expect(decoded).toEqual([{ jsonrpc: "2.0", id: 1 }])
  })

  it("the throw poisons nothing that follows — the parser resets its buffer", () => {
    // The observed production symptom: the oversized request's ids are
    // never answered, LATER requests are. The parser-level mechanism
    // is that the buffer is cleared on the throw; pin that too, so the
    // 'session survives' half of the audit's finding stays explained.
    const parser = RpcSerialization.ndjson.makeUnsafe()
    try {
      parser.decode(frame(transportFrameBytes))
    } catch {
      // expected
    }
    const decoded = parser.decode(`${JSON.stringify({ jsonrpc: "2.0", id: 2 })}\n`)
    expect(decoded).toEqual([{ jsonrpc: "2.0", id: 2 }])
  })
})
