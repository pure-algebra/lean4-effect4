/**
 * THE BRAIN STEM, DRIVEN — program interpretation, lifting, and
 * projection, proved by operation rather than by theorem.
 *
 * Every arrow below actually executes, over real MCP frames, against
 * the real serve host, over a real store on disk. Nothing is stubbed,
 * nothing is called directly, and no address in an assertion is copied
 * from the fixture into the store — the fixtures are only what the
 * store's own answers are COMPARED to.
 *
 * The chain:
 *
 *   lift document  →  table  →  step + cont nodes  →  cas_put ×N
 *        ↓                                                ↓
 *     (decode)                                    the cont address
 *                                                         ↓
 *                                              cas_publish_root
 *                                                         ↓
 *                                                 cas_run_ref
 *                                                         ↓
 *                                                     the word
 *                                                         ↓
 *                        cas_load ×N  →  table  →  TypeScript + prose
 *
 * and four independent equalities are asserted along it:
 *
 * 1. the cont address the HOST computes equals the one LEAN computed
 *    (`VectorProgramAddresses.json`) — the cross-host codec gate;
 * 2. the word `cas_run_ref` answers equals the word LEAN computed
 *    (`vectors/file-readme.json`) — the cross-host run gate, now
 *    reached BY ADDRESS rather than by a submitted document;
 * 3. the TypeScript re-emitted from the loaded content is byte-identical
 *    to the committed generated module's body — the projection back;
 * 4. the committed prose's address stamp names the address the store
 *    answered — R7's stamp clause, checked rather than asserted.
 *
 * The one arrow that is READ rather than run is the recognizer's:
 * `VectorProgramLifts.json` is the lift-harness's committed answer for
 * this program, and this suite starts from that document instead of
 * re-running the engines over the TypeScript source. That is a
 * deliberate boundary, not a gap — the harness has its own differential
 * suite for the recognition step, and re-running it here would test the
 * recognizer rather than the store.
 */
import { describe, expect, it } from "@effect/vitest"
import { Effect, Fiber, Layer, Path, Sink, Stdio, Stream } from "effect"
import { Cas } from "../src/index.ts"
import { defaultServePolicy } from "../bin/cli/store.ts"
import { layerServeStdio } from "../bin/mcp/server.ts"
import { layerDisk, layerDiskFs, withStoreRoot } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"

const { Programs } = Cas

/* ── the wire, exactly as a client speaks it ─────────────────────── */

const encoder = new TextEncoder()
const decoder = new TextDecoder()

interface JsonRpcFrame {
  readonly id?: number
  readonly result?: Record<string, unknown>
}

/** One stdio session. The whole transcript goes in as newline-delimited
 * JSON-RPC and the frames come back off the same seam; the session ends
 * once every request carrying an id has been answered. */
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
      written.join("").split("\n").filter((line) => line.length > 0)
        .map((line) => JSON.parse(line) as JsonRpcFrame)
    const server = yield* Effect.forkChild(
      Effect.never.pipe(
        Effect.provide(Layer.provideMerge(
          layerServeStdio({
            maxNodeBytes: defaultServePolicy.maxNodeBytes,
            maxInFlight: defaultServePolicy.maxInFlight,
          }),
          layerStdio,
        )),
      ),
    )
    const answered = (): boolean => {
      const ids = new Set(frames().map((frame) => frame.id))
      return awaited.every((id) => ids.has(id))
    }
    for (let waited = 0; waited < 800 && !answered(); waited += 1) {
      yield* Effect.sleep("5 millis")
    }
    yield* Fiber.interrupt(server)
    return frames()
  })

const handshake: ReadonlyArray<unknown> = [
  {
    jsonrpc: "2.0",
    id: 1,
    method: "initialize",
    params: {
      protocolVersion: "2025-06-18",
      capabilities: {},
      clientInfo: { name: "foldlab-brain-stem", version: "0" },
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

const structured = (
  frames: ReadonlyArray<JsonRpcFrame>,
  id: number,
): Record<string, unknown> => {
  const frame = frames.find((each) => each.id === id)
  const result = frame?.result
  expect(result, `frame ${id} carried no result: ${JSON.stringify(frame)}`).toBeDefined()
  expect(result?.["isError"], `frame ${id} reported an error: ${JSON.stringify(result)}`)
    .not.toBe(true)
  return result?.["structuredContent"] as Record<string, unknown>
}

/* ── bytes ───────────────────────────────────────────────────────── */

const hex = (s: string): Uint8Array =>
  Uint8Array.from({ length: s.length / 2 }, (_, i) => Number.parseInt(s.slice(i * 2, i * 2 + 2), 16))

const toHex = (bytes: Uint8Array): string =>
  Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("")

/** A node as the `cas_put` document spells it. */
const nodeDocument = (node: Cas.NodeInput): Record<string, unknown> => ({
  version: node.kind.version,
  tag: node.kind.tag,
  payload: toHex(node.payload),
  refs: node.refs.map((ref) => ({ expectedTag: ref.expectedTag, id: ref.id })),
})

/* ── the fixtures the answers are compared to ────────────────────── */

/** The program this transcript drives: four puts, a chunk under a tree
 * under a manifest under a file. Small enough to read in full, and it
 * exercises a reference chain rather than a single node. */
const PROGRAM = "fileReadme"
const VECTOR = "file-readme"

interface Fixtures {
  readonly table: Cas.Programs.Program
  readonly leanCont: string
  readonly leanSteps: ReadonlyArray<string>
  readonly leanWord: ReadonlyArray<string>
  readonly emittedSource: string
}

const loadFixtures = Effect.gen(function* () {
  const lifts = JSON.parse(
    yield* readFixtureString("test/generated/VectorProgramLifts.json"),
  ) as ReadonlyArray<{
    readonly name: string
    readonly instructions: ReadonlyArray<{
      readonly version: number
      readonly tag: number
      readonly payloadHex: string
      readonly refs: ReadonlyArray<{ readonly expectedTag: number; readonly source: number }>
    }>
  }>
  const addresses = JSON.parse(
    yield* readFixtureString("test/generated/VectorProgramAddresses.json"),
  ) as ReadonlyArray<{
    readonly name: string
    readonly contAddress: string
    readonly stepAddresses: ReadonlyArray<string>
  }>
  const vector = JSON.parse(
    yield* readFixtureString(`../cas/vectors/${VECTOR}.json`),
  ) as { readonly word: ReadonlyArray<{ readonly address: string }> }
  const emittedSource = yield* readFixtureString("test/generated/VectorPrograms.ts")

  const lift = lifts.find((each) => each.name === PROGRAM)
  const stamped = addresses.find((each) => each.name === PROGRAM)
  if (lift === undefined || stamped === undefined) {
    return yield* Effect.die(`${PROGRAM} is not in the committed fixtures`)
  }
  return {
    // THE DECODE: the recognizer's document becomes the carrier's own
    // table. Every operand in a v0 lift document is an answer index.
    table: lift.instructions.map((instruction): Cas.Programs.Line => ({
      _tag: "put",
      version: instruction.version,
      tag: instruction.tag,
      payload: hex(instruction.payloadHex),
      refs: instruction.refs.map((ref) => ({
        expectedTag: ref.expectedTag,
        source: Programs.answer(ref.source),
      })),
    })),
    leanCont: stamped.contAddress,
    leanSteps: stamped.stepAddresses,
    leanWord: vector.word.map((binding) => binding.address),
    emittedSource,
  } satisfies Fixtures
}).pipe(Effect.provide(layerDiskFs))

/* ── the projection back ─────────────────────────────────────────── */

/**
 * A recovered table, re-emitted as the TypeScript that runs it.
 *
 * This is the PROJECTION half of the brain stem, and it is written to
 * be byte-comparable rather than merely plausible: the statement shape
 * is `Cas.Backend.EmitProg`'s, so the lines this produces from content
 * loaded out of the store can be compared character for character
 * against the committed generated module.
 *
 * It renders from the TABLE — the thing recovered from the store — and
 * never from the fixture it is compared with.
 */
const emitTypeScript = (table: Cas.Programs.Program): string => {
  const operand = (source: Cas.Programs.Operand): string =>
    source._tag === "answer" ? `a${source.index}` : `"${source.address}"`
  const lines = table.map((line, index) => {
    if (line._tag === "load") {
      return `    const a${index} = yield* store.load(${operand(line.source)})`
    }
    const refs = line.refs
      .map((ref) => `{ id: ${operand(ref.source)}, expectedTag: ${ref.expectedTag} }`)
      .join(", ")
    return `    const a${index} = yield* store.put({ kind: { version: ${line.version}, tag: ${line.tag} }, payload: hex("${
      toHex(line.payload)
    }"), refs: [${refs}] })`
  })
  const answers = table.map((_, index) => `a${index}`).join(", ")
  return [...lines, `    return [${answers}]`].join("\n")
}

/** The committed generated module's body for one program — what the
 * projection above must reproduce. Read out of the emitted source so
 * the comparison is against the artifact, not against a copy. */
const committedBody = (source: string, name: string): string => {
  const head = source.indexOf(`export const ${name} = (store: CasStoreShape) =>`)
  const open = source.indexOf("Effect.gen(function* () {\n", head)
  const close = source.indexOf("\n  })", open)
  return source.slice(open + "Effect.gen(function* () {\n".length, close)
}

/** The committed docstring for one program — the authored point, the
 * computed envelope, and R7's address stamp. */
const committedProse = (source: string, name: string): ReadonlyArray<string> => {
  const head = source.indexOf(`export const ${name} = (store: CasStoreShape) =>`)
  const open = source.lastIndexOf("/** ", head)
  return source.slice(open, head).trim()
    .replace(/^\/\*\* /u, "").replace(/ \*\/$/u, "")
    .split("\n")
    .map((line) => line.replace(/^\s*\* ?/u, "").trim())
    .filter((line) => line.length > 0)
}

/* ── THE TRANSCRIPT ──────────────────────────────────────────────── */

describe("the brain stem, driven end to end over real MCP frames", () => {
  it.live("a program is decoded, put, published, run by address, and projected back", () =>
    withStoreRoot((storeRoot) =>
      Effect.gen(function* () {
        const fixtures = yield* loadFixtures
        const transcript: Array<string> = []
        const say = (line: string) => transcript.push(line)

        say(`# the brain stem — ${PROGRAM}, driven over MCP`)
        say("")

        /* 1 ── DECODE: the recognizer's document as the carrier's table */
        say(`1. DECODE   lift document → table: ${fixtures.table.length} code points`)
        expect(fixtures.table.length).toBe(4)

        /* 2 ── ENCODE + PUT: children-first, every address the host's */
        const steps = Programs.stepNodes(fixtures.table)
        const cont = (given: ReadonlyArray<Cas.ContentId>) => Programs.tableNode(given)

        // The step nodes first — each one a `cas_put` over the wire.
        const stepFrames = yield* session([
          ...handshake,
          ...steps.map((node, index) => call(10 + index, "cas_put", nodeDocument(node))),
        ])
        const stepAddresses = steps.map((_, index) =>
          structured(stepFrames, 10 + index)["address"] as Cas.ContentId
        )
        say(`2. PUT      ${steps.length} step nodes admitted through cas_put:`)
        for (const [index, address] of stepAddresses.entries()) {
          say(`              step ${index}  ${address}`)
        }

        // Then the cont node, which names them. It could not have gone
        // first: the store refuses a dangling reference, which is the
        // admission law and the reason `encodeProg` writes this order.
        const contFrames = yield* session([
          ...handshake,
          call(20, "cas_put", nodeDocument(cont(stepAddresses))),
        ])
        const contAddress = structured(contFrames, 20)["address"] as Cas.ContentId
        say(`              cont     ${contAddress}`)
        say("")

        /* EQUALITY 1 — the cross-host codec gate */
        say("3. GATE     the address the host computed vs. the address Lean computed")
        say(`              host  ${contAddress}`)
        say(`              lean  ${fixtures.leanCont}`)
        expect(stepAddresses.join(",")).toBe(fixtures.leanSteps.join(","))
        expect(contAddress).toBe(fixtures.leanCont)
        say("              → equal, step for step and at the cont")
        say("")

        /* 4 ── PUBLISH: the program becomes an entry point */
        // Two sessions, not two calls in one. `RpcServer` forks a fiber
        // per request, so calls inside one session are concurrent —
        // which is correct for a host and wrong for a transcript that
        // means "publish, THEN list".
        const publishFrames = yield* session([
          ...handshake,
          call(30, "cas_publish_root", { address: contAddress }),
        ])
        structured(publishFrames, 30)
        const listFrames = yield* session([...handshake, call(31, "cas_list_roots", {})])
        const roots = structured(listFrames, 31)["roots"] as ReadonlyArray<string>
        expect(roots).toEqual([contAddress])
        say(`4. PUBLISH  cas_publish_root, then cas_list_roots answers:`)
        say(`              ${roots.join("\n              ")}`)
        say("")

        /* 5 ── RUN BY ADDRESS: the verb this whole package exists for */
        const runFrames = yield* session([
          ...handshake,
          call(40, "cas_run_ref", { root: contAddress }),
        ])
        const word = (structured(runFrames, 40)["word"] as ReadonlyArray<
          { readonly address: string }
        >).map((entry) => entry.address)
        say(`5. RUN      cas_run_ref { root: ${contAddress} }`)
        say(`              the word, in admission order:`)
        for (const [index, address] of word.entries()) {
          say(`              ${index}  ${address}`)
        }
        say("")

        /* EQUALITY 2 — the cross-host run gate, reached by address */
        say("6. GATE     the word the host ran vs. the word Lean computed")
        expect(word).toEqual([...fixtures.leanWord])
        say(`              → equal, all ${word.length} bindings`)
        say("")

        /* 7 ── PROJECT BACK: content → table → TypeScript */
        const loadFrames = yield* session([
          ...handshake,
          call(50, "cas_load", { address: contAddress }),
          ...stepAddresses.map((address, index) =>
            call(60 + index, "cas_load", { address })
          ),
        ])
        const loadedCont = structured(loadFrames, 50)
        expect(loadedCont["tag"]).toBe(Programs.ContKindTag)
        const recovered = stepAddresses.map((_, index) => {
          const loaded = structured(loadFrames, 60 + index)
          const line = Programs.decodeLine({
            kind: {
              version: loaded["version"] as number,
              tag: loaded["tag"] as number,
            },
            payload: hex(loaded["payload"] as string),
            refs: [],
          })
          expect(line._tag, `step ${index} did not decode`).toBe("Some")
          return (line as { readonly value: Cas.Programs.Line }).value
        })

        const projected = emitTypeScript(recovered)
        const committed = committedBody(fixtures.emittedSource, PROGRAM)
        say("7. PROJECT  the program's TypeScript, re-emitted from the loaded content:")
        say("")
        for (const line of projected.split("\n")) say(`  ${line.trim()}`)
        say("")

        /* EQUALITY 3 — the projection is the artifact, byte for byte */
        expect(projected).toBe(committed)
        say("8. GATE     re-emitted source vs. the committed generated module")
        say("              → byte-identical")
        say("")

        /* EQUALITY 4 — the prose, and R7's stamp */
        const prose = committedProse(fixtures.emittedSource, PROGRAM)
        say("9. PROSE    the program's envelope, verbalized (ProgProse):")
        for (const line of prose) say(`              ${line}`)
        const stamp = prose.find((line) => line.includes("Its address as content"))
        expect(stamp, "the generated module carries no address stamp").toBeDefined()
        expect(stamp).toContain(contAddress)
        say("")
        say(`10. GATE    the stamp names ${contAddress} — the address the store answered`)

        // The transcript is a deliverable, not only an assertion log:
        // the point of this suite is that a human can READ the chain
        // and see every arrow execute. vitest intercepts console output
        // on a passing test, so read it with
        //
        //   bun --bun vitest run test/BrainStem.test.ts --disableConsoleIntercept
        //
        // The assertions above stand whether anyone reads it or not.
        console.log(`\n${transcript.join("\n")}\n`)
      }).pipe(Effect.provide(Layer.merge(layerDisk(storeRoot), Path.layer)))
    ))
})
