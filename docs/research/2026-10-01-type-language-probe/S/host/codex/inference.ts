import * as Schema from "effect/Schema"

export const FromEntries = Schema.Struct(Object.fromEntries([
  ["a-b", Schema.String],
  ["__proto__", Schema.Number]
]))
export const Computed = Schema.Struct({
  ["a-b"]: Schema.String,
  ["__proto__"]: Schema.Number
})

type From = typeof FromEntries.Type
type Exact = typeof Computed.Type
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends
  (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
type Expected = { readonly "a-b": string; readonly "__proto__": number }
export type ComputedHasExactFields = Assert<Equal<Exact, Expected>>

// Rejecting controls: each must produce a type error.
// @ts-expect-error Missing required fields.
const computedMissing: Exact = {}
// @ts-expect-error Wrong type for a-b.
const computedWrong: Exact = { ["a-b"]: 42, ["__proto__"]: 1 }
// @ts-expect-error Not a declared key.
const computedExtra: keyof Exact = "invented"
const computedGood: Exact = { ["a-b"]: "ok", ["__proto__"]: 1 }

// Witnesses of lost precision: these assignments all compile without casts.
const entriesMissing: From = {}
const entriesWrong: From = { ["a-b"]: 42, ["__proto__"]: "wrong" }
const entriesExtra: keyof From = "invented"
export { computedGood, entriesMissing, entriesWrong, entriesExtra }
