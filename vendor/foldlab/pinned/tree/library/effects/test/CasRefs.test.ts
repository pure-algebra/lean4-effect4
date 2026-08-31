/**
 * Typed references end to end (CAS-005): DAGs of typed values over the
 * store, edges checked by the admission law the store already carries,
 * lazy typed roots on decode, and the wire shape pinned — positional
 * markers in the payload, typed entries in the reference array.
 */
import { expect, it } from "@effect/vitest"
import { cast, Effect, FileSystem, Layer, Schema } from "effect"
import { ContentId } from "../src/cas/Node.ts"
import { PathReadError, layerPathReader } from "../src/cas/PathReader.ts"
import {
  CasStore,
  layerAddressSha256Live,
  layerFile,
  layerMemoryLive,
  layerReadStore,
} from "../src/cas/Store.ts"
import { ref, value, type Root } from "../src/cas/Value.ts"
import { makeMemoryFs } from "./MemoryFsHarness.ts"

interface Author {
  readonly name: string
}
const Author = value({
  kindTag: 0x21,
  revision: 0,
  schema: Schema.Struct({ name: Schema.String }),
})

interface Post {
  readonly title: string
  readonly author: Root<Author>
  readonly replies: ReadonlyArray<Root<Post>>
}
const Post: ReturnType<typeof value<Post>> = value({
  kindTag: 0x22,
  revision: 0,
  schema: Schema.Struct({
    author: ref(() => Author),
    replies: Schema.Array(ref((): typeof Post => Post)),
    title: Schema.String,
  }),
})

const layer = layerMemoryLive

it.effect("builds and reads a typed DAG leaf-up, decoding refs lazily", () =>
  Effect.gen(function* () {
    const author = yield* Author.put({ name: "kokok" })
    const reply = yield* Post.put({ author, replies: [], title: "re" })
    const post = yield* Post.put({ author, replies: [reply], title: "hi" })

    const decoded = yield* Post.get(post)
    // Lazy: refs decode to typed ids, never loaded children.
    expect(decoded.title).toBe("hi")
    expect(decoded.author).toBe(author)
    expect(decoded.replies).toEqual([reply])

    // Descent is explicit, and typed all the way down.
    expect((yield* Author.get(decoded.author)).name).toBe("kokok")
    expect((yield* Post.get(decoded.replies[0]!)).title).toBe("re")
  }).pipe(Effect.provide(layer)))

it.effect("the wire shape is the marker law: positional markers, typed entries", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const author = yield* Author.put({ name: "kokok" })
    const post = yield* Post.put({ author, replies: [], title: "hi" })

    const node = yield* store.load(cast(post))
    expect(node.refs).toEqual([{ expectedTag: 0x21, id: author }])
    const payload = new TextDecoder().decode(node.payload)
    // Canonical key order puts author first, so it carries marker 0.
    expect(payload).toBe(
      `{"revision":0,"value":{"author":{"$ref":0},"replies":[],"title":"hi"}}`,
    )
  }).pipe(Effect.provide(layer)))

it.effect("sharing one target is two markers and two reference entries", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const author = yield* Author.put({ name: "kokok" })
    const a = yield* Post.put({ author, replies: [], title: "a" })
    const both = yield* Post.put({ author, replies: [a, a], title: "b" })

    const node = yield* store.load(cast(both))
    expect(node.refs.map((entry) => entry.id)).toEqual([author, a, a])
  }).pipe(Effect.provide(layer)))

it.effect("admission checks typed edges: wrong-kind and dangling refuse", () =>
  Effect.gen(function* () {
    const author = yield* Author.put({ name: "kokok" })
    const post = yield* Post.put({ author, replies: [], title: "hi" })

    // A post root smuggled into an author-typed field — the type system
    // refuses this statement, so the attack is staged with a cast, and
    // the store's admission law catches it at put.
    const smuggledPost: Root<Author> = cast(post)
    const wrongKind = yield* Post.put({
      author: smuggledPost,
      replies: [],
      title: "wrong",
    }).pipe(Effect.flip)
    expect(wrongKind._tag).toBe("CasError/WrongKindReference")

    const smuggledAbsent: Root<Author> = cast(ContentId.make("ab".repeat(32)))
    const dangling = yield* Post.put({
      author: smuggledAbsent,
      replies: [],
      title: "nowhere",
    }).pipe(Effect.flip)
    expect(dangling._tag).toBe("CasError/DanglingReference")
  }).pipe(Effect.provide(layer)))

it.effect("typed reads work over a read-only host: no writer anywhere", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const writeLayer = layerFile("published").pipe(
      Layer.provide(Layer.mergeAll(
        Layer.succeed(FileSystem.FileSystem, memory.fs),
        layerAddressSha256Live,
      )),
    )
    const { author, post } = yield* Effect.gen(function* () {
      const authorRoot = yield* Author.put({ name: "kokok" })
      const postRoot = yield* Post.put({
        author: authorRoot,
        replies: [],
        title: "hosted",
      })
      return { author: authorRoot, post: postRoot }
    }).pipe(Effect.provide(writeLayer))

    // The host serves bytes at paths; the read-only law stack decodes
    // typed values over it — ByteWriter appears nowhere.
    const host = layerPathReader((relativePath) =>
      memory.fs.readFile(`published/${relativePath}`).pipe(
        Effect.asSome,
        Effect.catchTag("PlatformError", (error) =>
          error.reason._tag === "NotFound"
            ? Effect.succeedNone
            : Effect.fail(new PathReadError({
                path: relativePath,
                reason: error.message,
              }))),
      ))
    yield* Effect.gen(function* () {
      const decoded = yield* Post.get(post)
      expect(decoded.title).toBe("hosted")
      expect((yield* Author.get(decoded.author)).name).toBe("kokok")
      expect(decoded.author).toBe(author)
    }).pipe(Effect.provide(layerReadStore.pipe(
      Layer.provideMerge(host),
      Layer.provide(layerAddressSha256Live),
    )))
  }))

it.effect("user data colliding with the reserved keys refuses the encode", () =>
  Effect.gen(function* () {
    const Free = value({
      kindTag: 0x23,
      revision: 0,
      schema: Schema.Struct({ data: Schema.Json }),
    })
    const refusal = yield* Free.put({ data: { $ref: 0 } }).pipe(Effect.flip)
    expect(refusal._tag).toBe("ProjectionCodecFailure")
    expect(String((refusal as { readonly issue: string }).issue))
      .toContain("$ref")
  }).pipe(Effect.provide(layer)))

it.effect("leaf projections and their bytes are untouched by the marker law", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const author = yield* Author.put({ name: "kokok" })
    const node = yield* store.load(cast(author))
    expect(node.refs).toEqual([])
    expect(new TextDecoder().decode(node.payload))
      .toBe(`{"revision":0,"value":{"name":"kokok"}}`)
    expect((yield* Author.get(author)).name).toBe("kokok")
  }).pipe(Effect.provide(layer)))
