/**
 * The sidecar annotation loop, end to end (stipulation S2).
 *
 * The kind is authored once, in Lean, with `cas_struct`
 * (`library/cas/Cas/Schema/Annotation.lean`); its canonical payload is
 * pinned as a committed fixture by `lake exe schemas`; the TypeScript
 * mirror is the library's own `Annotations.Annotation`, hand-written and
 * held to those bytes; and an annotation node — whose subject is a typed
 * reference on one of the estate's addressable planes — round-trips
 * through the value plane.
 *
 * The point of the kind is that ANNOTATION CONTENT IS STORE CONTENT. The
 * schema carrier gains no annotation field; an annotation is a node that
 * references its subject by address. So "twenty encoded other schemas"
 * is twenty annotation nodes, and an annotation whose value is itself a
 * schema carries that schema's ADDRESS as a typed edge — not, as it once
 * did, as hex text nothing checks.
 *
 * ## What the convergent naming ruling changed here
 *
 * `subject` was pinned at the schema plane and `value` was a `String`.
 * This suite therefore asserted that a non-schema subject is REFUSED —
 * a true statement about the old kind and a false one about the new. It
 * now asserts the law that replaced it: every addressable plane has an
 * arm, an arm still DEMANDS ITS TAG, and what refusal means is that the
 * node at the address is of another kind or is not there at all.
 *
 * The node kind an annotation resides at USED to be the caller's — the
 * annotation plane had no reserved tag of its own, and this suite
 * picked `0x41` exactly as any consumer would. Decision 40 ratified
 * that same byte as the `annotation` registry row, so the plane is
 * library-owned now and `Cas.value` refuses it like every other row.
 * The projection under test is therefore `Annotations.Node`, the row's
 * one interpretation, at the emitted tag and revision.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, cast } from "effect"
import { Cas } from "../src/index.ts"
import { ContentId } from "../src/cas/Node.ts"
import { CasStore } from "../src/cas/Store.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureBytes, readFixtureString } from "./fixtures/read.ts"
import { pinSample } from "./fixtures/schemaRegistry.ts"
import { topology } from "./generated/EmittedLayers.ts"

const { Annotations, CanonicalSchema } = Cas
const layer = Layer.mergeAll(Cas.layerMemoryLive, layerDiskFs)
const utf8 = new TextDecoder("utf-8", { fatal: true })

/** THE annotation projection: the library's own, at the ratified row
 * `0x41` and the emitted revision. */
const AnnotationNode = Annotations.Node

const fixture = readFixtureBytes("../cas/schemas/annotation.json").pipe(
  Effect.orDie,
)

it.effect("the Lean-authored kind and its mirror are one identity, bytes and address", () =>
  Effect.gen(function* () {
    // Byte for byte: the fixture is the Lean self-codec's output, the
    // mirror is hand-written TypeScript, and neither is derived from
    // the other.
    const pinned = yield* fixture
    expect(utf8.decode(CanonicalSchema.payloadOf(Annotations.Annotation)))
      .toBe(utf8.decode(pinned))

    // And at the address: the mirror admitted through the real store
    // answers the address Lean computed over the same node.
    const committed = JSON.parse(
      yield* readFixtureString("../cas/schemas/addresses.json").pipe(Effect.orDie),
    ) as { schemas: ReadonlyArray<{ name: string; address: string }> }
    const expected = committed.schemas.find((row) => row.name === "annotation")
    expect(yield* CanonicalSchema.put(Annotations.Annotation))
      .toBe(expected?.address)
  }).pipe(Effect.provide(layer)))

it.effect("an annotation node addresses the schema it annotates", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const subject = yield* CanonicalSchema.put(pinSample)
    const annotation = Annotations.annotationOn(Annotations.onSchema(subject))({
      key: `${Annotations.Namespace}note`,
      value: Annotations.text("the pin sample"),
    })

    const root = yield* AnnotationNode.put(annotation)
    expect(yield* AnnotationNode.get(root)).toEqual(annotation)

    // The subject rides the node as a typed edge demanding the schema
    // kind, and the payload carries only its positional marker.
    const node = yield* store.load(cast(root))
    expect(node.refs).toEqual([
      { expectedTag: CanonicalSchema.KindTag, id: subject },
    ])
    expect(utf8.decode(node.payload)).toBe(
      `{"revision":1,"value":{"key":"foldlab/cas/note","subject":{"_tag":"schema","address":{"$ref":0}},"value":{"_tag":"text","text":"the pin sample"}}}`,
    )
  }).pipe(Effect.provide(layer)))

it.effect("twenty annotations ride one subject, and a value carries another schema", () =>
  Effect.gen(function* () {
    const subject = yield* CanonicalSchema.put(pinSample)
    const carried = yield* CanonicalSchema.put(Annotations.Annotation)

    const on = Annotations.annotationOn(Annotations.onSchema(subject))
    const roots = yield* Effect.forEach(
      Array.from({ length: 20 }, (_, index) => index),
      (index) =>
        AnnotationNode.put(on({
          key: `${Annotations.Namespace}related/${index}`,
          // Store content in a value is an ADDRESS, and after the
          // widening it is a typed edge rather than hex text: the
          // twentieth annotation carries a whole schema, not a copy of
          // one and not a string nothing checks.
          value: index === 19
            ? Annotations.ref(Annotations.onSchema(carried))
            : Annotations.text(`note ${index}`),
        })),
    )

    // Twenty distinct nodes, all naming one subject.
    expect(new Set(roots).size).toBe(20)
    const read = yield* Effect.forEach(roots, (root) => AnnotationNode.get(root))
    expect(read.map((one) => one.subject)).toEqual(
      Array(20).fill({ _tag: "schema", address: subject }),
    )
    expect(read.map((one) => one.key)).toEqual(
      Array.from({ length: 20 }, (_, index) => `foldlab/cas/related/${index}`),
    )

    // The value's reference is a SECOND typed edge on the node, not a
    // string: the store carries it in the reference array, so a wrong
    // kind at that address would have been refused at admission.
    const carrier = read[19]!.value
    expect(carrier._tag).toBe("ref")
    const node = yield* (yield* CasStore).load(cast(roots[19]!))
    expect(node.refs).toEqual([
      { expectedTag: CanonicalSchema.KindTag, id: subject },
      { expectedTag: CanonicalSchema.KindTag, id: carried },
    ])

    // And the carried address resolves as a schema through the front
    // door, exactly as before.
    const document = yield* CanonicalSchema.get(
      ContentId.make(carrier._tag === "ref" ? carrier.address.address : ""),
    )
    expect(utf8.decode(CanonicalSchema.payloadOf(document)))
      .toBe(utf8.decode(yield* fixture))
  }).pipe(Effect.provide(layer)))

/** THE NAME SEAT, worked.
 *
 * A human-facing name for a stored value was unspellable before the
 * subject widened: `key = "foldlab/name"` needs a subject that can
 * address something other than a schema node, and there was none. This
 * is that annotation, on the system plane, through the real store.
 *
 * The subject is the SYSTEM arm, so the store demands kind tag `0x54`
 * at that address — which is the whole content of the arm. The name
 * itself is a `text` value: a name is a scalar, and the value union is
 * what lets it be one without giving up the `ref` arm elsewhere. */
it.effect("a stored topology carries a human-facing name through the system arm", () =>
  Effect.gen(function* () {
    const store = yield* CasStore

    // A node at the system kind. The host has no `SystemNode` codec —
    // that lane generates layers and does not ingest them — so this
    // suite stores the node the way any consumer without a mirror
    // would, at the plane's working tag.
    const stored = yield* store.put({
      kind: { version: Cas.SchemeVersion, tag: Annotations.SystemKindTag },
      payload: new TextEncoder().encode("a service topology"),
      refs: [],
    })

    const named = Annotations.annotationOn(Annotations.onSystem(stored))({
      key: "foldlab/name",
      value: Annotations.text("casSystem"),
    })
    const root = yield* AnnotationNode.put(named)
    expect(yield* AnnotationNode.get(root)).toEqual(named)

    // One typed edge, at the system kind, and the name in the payload.
    const node = yield* store.load(cast(root))
    expect(node.refs).toEqual([
      { expectedTag: Annotations.SystemKindTag, id: stored },
    ])
    expect(utf8.decode(node.payload)).toBe(
      `{"revision":1,"value":{"key":"foldlab/name","subject":{"_tag":"system","address":{"$ref":0}},"value":{"_tag":"text","text":"casSystem"}}}`,
    )
  }).pipe(Effect.provide(layer)))

/** The same seat, aimed at one of the two AUTHORED topologies.
 *
 * `EmittedLayers.ts` now stamps each requirement-free topology with the
 * address it resides at, so the name seat can point at the real thing
 * rather than a stand-in. What this asserts is the honest state of the
 * estate: the annotation is well formed and names the exact address
 * Lean computed, and admission fails DANGLING — because no host has
 * ever PUT a system node. The gap is the missing host-side codec, not
 * the annotation, and the day that codec lands this assertion is the
 * one that has to change. */
it.effect("the name seat aims at the authored topology's own address", () =>
  Effect.gen(function* () {
    const casSystem = topology.find((entry) => entry.name === "casSystem")
    expect(casSystem).toBeDefined()

    const subject = Annotations.onSystem(ContentId.make(casSystem!.address))
    expect(subject.address).toBe(casSystem!.address)

    const refusal = yield* AnnotationNode.put(
      Annotations.annotationOn(subject)({
        key: "foldlab/name",
        value: Annotations.text("casSystem"),
      }),
    ).pipe(Effect.flip)
    expect(refusal._tag).toBe("CasError/DanglingReference")
  }).pipe(Effect.provide(layer)))

/** What refusal means now.
 *
 * This test used to read "an annotation whose subject is not a schema
 * node is refused at admission" — the old law, and false under the
 * widening: a topology, a program, an exchange and a git object are all
 * first-class subjects now. The assertions are flipped rather than
 * deleted, because the property that survived is the one worth keeping:
 * AN ARM STILL DEMANDS ITS TAG. Widening the union added planes; it did
 * not weaken the edge. */
it.effect("an arm still demands its tag, and a missing node is still dangling", () =>
  Effect.gen(function* () {
    const store = yield* CasStore

    // A node on a plane no arm names. Nothing can subject it — which is
    // what "one arm per addressable plane the estate HAS" means: the
    // union is a list of planes, not a hole.
    const unaddressable = yield* store.put({
      kind: { version: Cas.SchemeVersion, tag: 0x42 },
      payload: new TextEncoder().encode("no plane names this"),
      refs: [],
    })
    const noPlane = yield* AnnotationNode.put(
      Annotations.annotationOn(Annotations.onSchema(unaddressable))({
        key: `${Annotations.Namespace}note`,
        value: Annotations.text("wrong subject"),
      }),
    ).pipe(Effect.flip)
    expect(noPlane._tag).toBe("CasError/WrongKindReference")

    // And a real node under the WRONG ARM is refused just as hard: the
    // schema arm demands 0x53, so a system node under it does not pass
    // however addressable its own plane is.
    const aTopology = yield* store.put({
      kind: { version: Cas.SchemeVersion, tag: Annotations.SystemKindTag },
      payload: new TextEncoder().encode("a service topology"),
      refs: [],
    })
    const wrongArm = yield* AnnotationNode.put(
      Annotations.annotationOn(Annotations.onSchema(aTopology))({
        key: "foldlab/name",
        value: Annotations.text("casSystem"),
      }),
    ).pipe(Effect.flip)
    expect(wrongArm._tag).toBe("CasError/WrongKindReference")

    // The VALUE's reference is an edge now, so it is refused on the
    // same law — which is the whole point of promoting it off `String`.
    // A hex string in the old `value` could name anything at all and
    // nothing ever checked it.
    const schema = yield* CanonicalSchema.put(pinSample)
    const wrongValueArm = yield* AnnotationNode.put(
      Annotations.annotationOn(Annotations.onSchema(schema))({
        key: `${Annotations.Namespace}view`,
        value: Annotations.ref(Annotations.onSystem(schema)),
      }),
    ).pipe(Effect.flip)
    expect(wrongValueArm._tag).toBe("CasError/WrongKindReference")

    const dangling = yield* AnnotationNode.put(
      Annotations.annotationOn(
        Annotations.onSchema(ContentId.make("ab".repeat(32))),
      )({
        key: `${Annotations.Namespace}note`,
        value: Annotations.text("nowhere"),
      }),
    ).pipe(Effect.flip)
    expect(dangling._tag).toBe("CasError/DanglingReference")
  }).pipe(Effect.provide(layer)))
