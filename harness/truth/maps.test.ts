import { expect, test } from "bun:test"
import { Option } from "effect"
import { mapEmpty, mapGet, mapSet, mapKeys, mapEntries, mapFromEntries } from "./prelude-atoms.gen.ts"

test("map presence separates absent keys from present empty values", () => {
  expect(Option.isNone(mapGet(mapEmpty(), "toString"))).toBe(true)
  expect(Option.isSome(mapGet(mapSet(mapEmpty(), "unit", undefined), "unit"))).toBe(true)
  const nested = mapGet(mapSet(mapEmpty(), "option", Option.none()), "option")
  expect(Option.isSome(nested) && Option.isNone(nested.value)).toBe(true)
})

test("map updates retain the input and preserve prototype names as own keys", () => {
  const original = mapSet(mapEmpty(), "__proto__", 7)
  const updated = mapSet(original, "__proto__", "changed")
  expect(Option.getOrUndefined(mapGet(original, "__proto__"))).toBe(7)
  expect(Option.getOrUndefined(mapGet(updated, "__proto__"))).toBe("changed")
  expect(Object.getPrototypeOf(updated)).toBe(Object.prototype)
  expect(Object.hasOwn(updated, "__proto__")).toBe(true)
})

test("keys and entries use UTF-8 order rather than numeric or UTF-16 order", () => {
  const input = mapFromEntries([["😀", 5], ["2", 2], ["10", 1], ["", 4], ["a-b", 3]])
  const keys = ["10", "2", "a-b", "", "😀"]
  expect(mapKeys(input)).toEqual(keys)
  expect(mapEntries(input)).toEqual(keys.map((key, index) => [key, index + 1]))
})

test("entry conversion keeps the last repeated value and round trips", () => {
  const map = mapFromEntries([["z", 1], ["__proto__", 2], ["z", 3], ["", 4]])
  expect(mapEntries(map)).toEqual([["", 4], ["__proto__", 2], ["z", 3]])
  expect(mapEntries(mapFromEntries(mapEntries(map)))).toEqual(mapEntries(map))
})
