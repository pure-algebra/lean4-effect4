// Probe, not a gate. Nothing imports it and no script runs it; it records the
// rc.112 facts `generated/traces/ref/*.tsv` are stated against, so the register
// rows cite an execution rather than a reading of the source.
//
//   cd <a directory whose node_modules is the pinned install>
//   node --experimental-strip-types --no-warnings ref-probe.mjs
import { Effect, Ref, Scope } from "effect"
import { handleIndex, registerHandle, wire } from "./tracer.ts"

const show = (label, value) => {
  let wired
  try { wired = wire(value) } catch (error) { wired = `THROWS ${error.constructor.name}: ${error.message}` }
  console.log(`${label.padEnd(46)} runtime=${value === undefined ? "undefined" : typeof value}  wire=${wired}`)
}

console.log("--- 1. what each rc.112 call answers, under its declared type ---")
registerHandle((value) => "~effect/Ref" in value)
await Effect.runPromise(Effect.gen(function* () {
  const ref = yield* Ref.make(41)
  show("Ref.make      declared Effect<Ref<number>>", ref)
  show("Ref.set       declared Effect<void>", yield* Ref.set(ref, 7))
  show("Ref.update    declared Effect<void>", yield* Ref.update(ref, (n) => n + 5))
  show("Ref.modify    declared Effect<number>", yield* Ref.modify(ref, (n) => [n, n + 1]))
  show("Ref.getAndSet declared Effect<number>", yield* Ref.getAndSet(ref, 0))
}))

console.log("")
console.log("--- 2. the handle counter is global, not per family ---")
// `ref-tail.ts` brands one handle type, so its refs are indexed 0, 1, 2, … and
// match the Lean face's per-store `Handle`. A tail that branded two and
// interleaved their allocation would not: `nextHandleIndex` in tracer.ts is one
// counter over every branded object. counterexample: E4-SEM-CE-014
registerHandle((value) => "~effect/Scope" in value)
const scope = Scope.makeUnsafe()
const laterRef = await Effect.runPromise(Ref.make(1))
console.log(`first scope   -> host handle index ${handleIndex(scope)}`)
console.log(`next  ref     -> host handle index ${handleIndex(laterRef)}`)
console.log(`a per-family Lean store would name that ref 0, not ${handleIndex(laterRef)}`)
