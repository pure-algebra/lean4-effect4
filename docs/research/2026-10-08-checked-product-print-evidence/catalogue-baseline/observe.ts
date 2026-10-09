import { Effect, SynchronizedRef, Stream } from "effect"
import { pathToFileURL } from "node:url"
import { readFileSync } from "node:fs"

const folder = process.argv[2]
if (!folder) throw new Error("Missing packet directory")
const manifest = JSON.parse(readFileSync(`${folder}/manifest.json`, "utf8"))
const rows = []
for (const c of manifest.cases) {
  const loaded = await import(pathToFileURL(`${folder}/${c.file}`).href)
  rows.push({ id: c.id, observed: await Effect.runPromise(loaded.main) })
}
const latest = {
  stream: await Effect.runPromise(Stream.runCollect(Stream.fromArray([1, 2, 3]))),
  empty: await Effect.runPromise(Stream.runCollect(Stream.fromArray([] as number[]))),
  sync: await Effect.runPromise(Effect.gen(function*() {
    const ref = yield* SynchronizedRef.make(5)
    const reply = yield* SynchronizedRef.modify(ref, current => [current, current + 2] as const)
    return [reply, yield* SynchronizedRef.get(ref)]
  })),
  strings: await Effect.runPromise(Effect.gen(function*() {
    const ref = yield* SynchronizedRef.make("before")
    const reply = yield* SynchronizedRef.modify(ref, current => [current, "after"] as const)
    return [reply, yield* SynchronizedRef.get(ref)]
  }))
}
console.log(JSON.stringify({ rows, latest }))
