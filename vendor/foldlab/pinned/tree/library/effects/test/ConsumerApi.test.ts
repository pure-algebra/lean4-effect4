/**
 * The consumer surface, exercised exactly as a package consumer would:
 * one barrel import, layers composed by name, the data structure and
 * the server reached through their front doors only.
 */
import { expect, it } from "@effect/vitest"
import { cast, Effect, Layer, Schema } from "effect"
import { Cas, Server } from "../src/index.ts"

/** A caller-defined projection, at a tag no registry row claims.
 *
 * It rode `0x41` until decision 40 ratified that byte as the
 * `annotation` row — and `Cas.value` refusing it afterwards is the door
 * working, not breaking: a consumer's own projection may not alias a
 * kind plane the library already reads. `0x21` is what a consumer picks
 * instead, which is what this file is here to exercise. */
const Note = Cas.value({
  kindTag: 0x21,
  revision: 0,
  schema: Schema.Struct({ text: Schema.String }),
})

const layer = Cas.layerMemoryLive

it.effect("the barrel is exactly the two plane doors", () =>
  Effect.sync(() => {
    expect(Object.keys({ Cas, Server }).sort()).toEqual(["Cas", "Server"])
    expect("value" in Cas).toBe(true)
    expect("ref" in Cas).toBe(true)
    expect("layerPathReader" in Cas).toBe(true)
    expect("Graph" in Cas).toBe(true)
    expect("Architecture" in Cas).toBe(true)
    expect("Materialize" in Cas).toBe(true)
    expect("Core" in Server).toBe(true)
    expect("httpApp" in Server).toBe(true)
  }))

it.effect("a consumer stores and reads typed values through the front door", () =>
  Effect.gen(function* () {
    const root = yield* Note.put({ text: "hello" })
    expect((yield* Note.get(root)).text).toBe("hello")

    // The error family folds by name through the front door.
    const absentRoot: typeof root = cast(Cas.ContentId.make("ab".repeat(32)))
    const absent = yield* Note.get(absentRoot).pipe(Effect.flip)
    if (Cas.isCasError(absent)) {
      const label = Cas.matchError({
        onOther: () => "other",
        ContentNotFound: () => "not-found",
      })(absent)
      expect(label).toBe("not-found")
    }
  }).pipe(Effect.provide(layer)))

it.effect("the same backend value serves: core over the seams the store stands on", () =>
  Effect.gen(function* () {
    const core = yield* Server.Core
    const outcome = yield* core.serve(
      Server.Principal.Anonymous(),
      Server.Request.ReadCapabilities(),
    )
    expect(outcome).toEqual(Server.Outcome.Capabilities({
      maxBatchKeys: 8,
      maxNodeBytes: 1024,
    }))
  }).pipe(Effect.provide(
    Server.Core.layer({ maxBatchKeys: 8, maxNodeBytes: 1024 }).pipe(
      Layer.provideMerge(Cas.layerMemoryBackend),
      Layer.provideMerge(Cas.layerAddressSha256Live),
    ),
  )))
