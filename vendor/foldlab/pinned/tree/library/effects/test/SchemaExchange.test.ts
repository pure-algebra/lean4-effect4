/**
 * The exchange loop, end to end — interactions as content (R15).
 *
 * The kind is authored once, in Lean, with `cas_struct` and `cas_union`
 * (`library/cas/Cas/Schema/Exchange.lean`); its canonical payload is
 * pinned as a committed fixture by `lake exe schemas`; the TypeScript
 * mirror is the library's own `Exchanges.Exchange`, hand-written and
 * held to those bytes; and an exchange node — whose subject addresses
 * either a schema or the exchange before it — round-trips through the
 * value plane.
 *
 * The point of the kind is that a RECORDED PROMPT AND ANSWER IS STORE
 * CONTENT. R15's seam is symmetric: `infer` calls the model as an
 * operation, and its answer enters only as recorded content. Recording
 * it as a described kind buys the store's own machinery — typed edges
 * checked at admission, one address per exchange, and provenance as a
 * DAG walk rather than a log to be parsed.
 *
 * The chain is the load-bearing case. Following `subject` while it
 * carries the `exchange` arm IS the conversation, and the store refuses
 * an arm whose target is of another kind, so a walk cannot wander off
 * the plane it is walking.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, cast } from "effect"
import { Cas } from "../src/index.ts"
import type { Exchange } from "../src/cas/Exchanges.ts"
import { ContentId } from "../src/cas/Node.ts"
import { CasStore } from "../src/cas/Store.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureBytes, readFixtureString } from "./fixtures/read.ts"
import { pinSample } from "./fixtures/schemaRegistry.ts"

const { CanonicalSchema, Exchanges } = Cas
const layer = Layer.mergeAll(Cas.layerMemoryLive, layerDiskFs)
const utf8 = new TextDecoder("utf-8", { fatal: true })

/** The exchange projection: revision 1 at the exchange kind's own
 * working tag. Unlike the annotation kind, the tag is not free for the
 * caller to pick — the subject union's `exchange` arm demands `0x58`,
 * so a chain is only walkable when its nodes reside there. */
const ExchangeNode = Cas.value({
  kindTag: Exchanges.KindTag,
  revision: 1,
  schema: Exchanges.Exchange,
})

const fixture = readFixtureBytes("../cas/schemas/exchange.json").pipe(
  Effect.orDie,
)

/** The one step of the walk: the address an exchange's subject carries
 * while that subject is another exchange, and nothing once it is not. */
const prior = (exchange: Exchange): unknown =>
  exchange.subject._tag === "exchange" ? exchange.subject.address : undefined

it.effect("the Lean-authored kind and its mirror are one identity, bytes and address", () =>
  Effect.gen(function* () {
    // Byte for byte: the fixture is the Lean self-codec's output, the
    // mirror is hand-written TypeScript, and neither is derived from
    // the other.
    const pinned = yield* fixture
    expect(utf8.decode(CanonicalSchema.payloadOf(Exchanges.Exchange)))
      .toBe(utf8.decode(pinned))

    // And at the address: the mirror admitted through the real store
    // answers the address Lean computed over the same node.
    const committed = JSON.parse(
      yield* readFixtureString("../cas/schemas/addresses.json").pipe(Effect.orDie),
    ) as { schemas: ReadonlyArray<{ name: string; address: string }> }
    const expected = committed.schemas.find((row) => row.name === "exchange")
    expect(yield* CanonicalSchema.put(Exchanges.Exchange))
      .toBe(expected?.address)
  }).pipe(Effect.provide(layer)))

it.effect("an exchange addresses the content it was about", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const subject = yield* CanonicalSchema.put(pinSample)
    const exchange = Exchanges.recorded(Exchanges.aboutSchema(subject))({
      prompt: "what does this schema describe?",
      answer: "a struct of seven fields, one of them a typed reference",
    })

    const root = yield* ExchangeNode.put(exchange)
    expect(yield* ExchangeNode.get(root)).toEqual(exchange)

    // The subject rides the node as a typed edge demanding the schema
    // kind, and the payload carries only its positional marker — the
    // prompt and the answer are content, the subject is an address.
    const node = yield* store.load(cast(root))
    expect(node.kind.tag).toBe(Exchanges.KindTag)
    expect(node.refs).toEqual([
      { expectedTag: CanonicalSchema.KindTag, id: subject },
    ])
    expect(utf8.decode(node.payload)).toBe(
      `{"revision":1,"value":{"answer":"a struct of seven fields, one of them a typed reference","prompt":"what does this schema describe?","subject":{"_tag":"schema","address":{"$ref":0}}}}`,
    )
  }).pipe(Effect.provide(layer)))

it.effect("a conversation is a DAG the store walks, one exchange at a time", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const schema = yield* CanonicalSchema.put(pinSample)

    // Turn one grounds the conversation in the content it is about;
    // every later turn addresses the turn before it, so the whole
    // conversation is reachable from its last address alone.
    const first = yield* ExchangeNode.put(
      Exchanges.recorded(Exchanges.aboutSchema(schema))({
        prompt: "what does this schema describe?",
        answer: "a struct of seven fields",
      }),
    )
    const turns = [
      { prompt: "which of them is a reference?", answer: "root, at kind tag 9" },
      { prompt: "and what does it point at?", answer: "a blob node" },
    ]
    const roots = [first]
    for (const turn of turns) {
      roots.push(
        yield* ExchangeNode.put(
          Exchanges.recorded(Exchanges.aboutExchange(roots.at(-1)!))(turn),
        ),
      )
    }

    // The walk: follow `subject` while it carries the exchange arm.
    const walked: Array<Exchange> = []
    let cursor: unknown = roots.at(-1)
    while (cursor !== undefined) {
      const one = yield* ExchangeNode.get(cast(cursor))
      walked.push(one)
      cursor = prior(one)
    }

    expect(walked.map((one) => one.prompt)).toEqual([
      "and what does it point at?",
      "which of them is a reference?",
      "what does this schema describe?",
    ])
    // The walk terminates on the schema arm, and that arm is the
    // address of the content the conversation was about.
    const root = walked[2]!.subject
    expect(root._tag).toBe("schema")
    expect(root.address).toBe(schema)

    // Three exchanges are three distinct nodes, each exactly one edge
    // wide: the store sees the conversation's shape without reading a
    // word of the prose it carries.
    expect(new Set(roots).size).toBe(3)
    const node = yield* store.load(cast(roots[2]!))
    expect(node.refs).toEqual([
      { expectedTag: Exchanges.KindTag, id: roots[1] },
    ])
  }).pipe(Effect.provide(layer)))

it.effect("a subject arm whose target is another kind is refused at admission", () =>
  Effect.gen(function* () {
    const schema = yield* CanonicalSchema.put(pinSample)
    const exchange = yield* ExchangeNode.put(
      Exchanges.recorded(Exchanges.aboutSchema(schema))({
        prompt: "p",
        answer: "a",
      }),
    )

    // The schema arm pointed at an exchange node: the arm names the
    // plane, and the store checks the plane.
    const schemaArmOnExchange = yield* ExchangeNode.put(
      Exchanges.recorded(Exchanges.aboutSchema(cast(exchange)))({
        prompt: "p",
        answer: "a",
      }),
    ).pipe(Effect.flip)
    expect(schemaArmOnExchange._tag).toBe("CasError/WrongKindReference")

    // And the same refusal in the other direction: an exchange arm
    // cannot be walked onto a schema node, so a chain cannot leave the
    // plane it is a chain of.
    const exchangeArmOnSchema = yield* ExchangeNode.put(
      Exchanges.recorded(Exchanges.aboutExchange(schema))({
        prompt: "p",
        answer: "a",
      }),
    ).pipe(Effect.flip)
    expect(exchangeArmOnSchema._tag).toBe("CasError/WrongKindReference")

    const dangling = yield* ExchangeNode.put(
      Exchanges.recorded(Exchanges.aboutExchange(ContentId.make("ab".repeat(32))))({
        prompt: "p",
        answer: "a",
      }),
    ).pipe(Effect.flip)
    expect(dangling._tag).toBe("CasError/DanglingReference")
  }).pipe(Effect.provide(layer)))
