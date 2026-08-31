/**
 * Demo entry point: build a folder of text, run an agent step over it with a
 * scripted oracle, print the chain, then branch by stepping from genesis
 * again — branching as a non-feature.
 */
import { Console, Effect, Layer, pipe } from "effect"
import { Cas } from "../../src/index.ts"
import { KindTag, textOf, utf8 } from "./kinds.ts"
import { genesis, putNode } from "./chain.ts"
import { renderNode } from "./context.ts"
import { Attestation, step } from "./agent.ts"
import { layerScripted } from "./oracle.ts"

const short = (id: string): string => id.slice(0, 8)

const putText = (text: string) => putNode(KindTag.value, utf8(text), [])

const putFolder = (
  entries: ReadonlyArray<readonly [string, Cas.ContentId, number]>,
) =>
  putNode(
    KindTag.folder,
    utf8(entries.map(([name]) => name).join("\n")),
    entries.map(([, id, expectedTag]) => ({ id, expectedTag })),
  )

/** Walk the chain head-to-genesis, printing each entry with addresses. */
const printChain = (head: Cas.ContentId, indent = ""): Effect.Effect<void, Cas.Error, Cas.Store> =>
  pipe(
    Effect.Do,
    Effect.bind("store", () => Cas.Store),
    Effect.bind("node", ({ store }) => store.load(head)),
    Effect.tap(({ node }) =>
      Console.log(`${indent}${short(head)} entry ${textOf(node.payload) || "(genesis)"}`)),
    Effect.flatMap(({ store, node }) =>
      Effect.forEach(node.refs, (ref) =>
        ref.expectedTag === KindTag.entry
          ? printChain(ref.id, indent)
          : pipe(
              store.load(ref.id),
              Effect.flatMap(renderNode),
              Effect.flatMap((rendered) =>
                Console.log(`${indent}  ${short(ref.id)} ${rendered.split("\n").join(" | ")}`)),
            ))),
    Effect.asVoid,
  )

const program = pipe(
  Effect.Do,
  Effect.bind("hello", () => putText("hello world")),
  Effect.bind("ideas", () => putText("# merkle to merkle")),
  Effect.bind("folder", ({ hello, ideas }) =>
    putFolder([
      ["hello.txt", hello, KindTag.value],
      ["ideas.md", ideas, KindTag.value],
    ])),
  Effect.bind("root", () => genesis),
  Effect.bind("ask", () => putText("what is in this folder?")),
  Effect.bind("one", ({ root, folder, ask }) =>
    step(root, [folder, ask], new Attestation({ model: "scripted", params: "t=0" }))),
  Effect.bind("two", ({ one }) =>
    step(one.history, [one.output], new Attestation({ model: "scripted", params: "t=0" }))),
  // The branch: step from GENESIS again — no branchFrom API, just an older root.
  Effect.bind("alt", ({ root, folder }) =>
    step(root, [folder], new Attestation({ model: "scripted", params: "alt" }))),
  Effect.tap(() => Console.log("— main chain —")),
  Effect.tap(({ two }) => printChain(two.history)),
  Effect.tap(() => Console.log("— branch from genesis —")),
  Effect.tap(({ alt }) => printChain(alt.history)),
  Effect.tap(({ two, alt }) =>
    Console.log(`heads diverge: ${short(two.history)} vs ${short(alt.history)}`)),
)

const oracle = layerScripted((prompt) =>
  prompt.includes("hello.txt") ? "two files; the greeting checks out" : "folded: " + prompt.length + " chars")

void Effect.runPromise(
  pipe(program, Effect.provide(Layer.mergeAll(Cas.layerMemoryLive, oracle))),
)
