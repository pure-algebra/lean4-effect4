import { describe, expect, test } from "bun:test"
import { tuple } from "./prelude-atoms.gen.ts"
import { tupleAt } from "./tuples.ts"

describe("tuple construction and static projection", () => {
  test("empty, singleton, pair and larger tuples use ordinary array positions", () => {
    expect(tuple()).toEqual([])
    expect(tupleAt<"0">("0")(tuple(7))).toBe(7)
    expect(tupleAt<"1">("1")(tuple(7, "x"))).toBe("x")
    expect(tupleAt<"2">("2")(tuple(7, "x", true))).toBe(true)
  })
  test("projection retains nested value identity and evaluates its receiver once", () => {
    const value = { id: 7 }
    let calls = 0
    const target = () => { calls++; return tuple(value, "x") }
    expect(tupleAt<"0">("0")(target())).toBe(value)
    expect(calls).toBe(1)
    expect(tupleAt<"0">("0")(tupleAt<"0">("0")(tuple(tuple(value))))).toBe(value)
  })
})
