import { expect, test } from "bun:test"
import { Result } from "effect"
import type { Eff } from "../eff.gen.ts"
import { effWire, litWire } from "../wire.gen.ts"
import { readTypeScript } from "../read.ts"

const hex = (bytes: Uint8Array) => Buffer.from(bytes).toString("hex")

test("p42 agrees with the independent pre-generator wire golden", () => {
  const p: Eff = { _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 42 } } }
  const expected = "0a00000000000000390200000000000000000a0000000000000027020000000000000001010a0000000000000014020000000000000001010200000000000000012a"
  expect(hex(effWire(p))).toBe(expected)
})

test("canonical natural boundaries and malformed UTF-16 never lose information", () => {
  for (const value of [-1, -0, 0.5, NaN, Infinity, 2 ** 53, 2 ** 62]) {
    expect(() => litWire({ _tag: "nat", value })).toThrow()
  }
  expect(hex(litWire({ _tag: "nat", value: 0 }))).toEndWith("020000000000000000")
  expect(hex(litWire({ _tag: "nat", value: 256 }))).toEndWith("0200000000000000020100")
  expect(() => litWire({ _tag: "nat", value: Number.MAX_SAFE_INTEGER })).not.toThrow()
  for (const value of ["\ud800", "\udfff", "\ud800x"]) expect(() => litWire({ _tag: "str", value })).toThrow("surrogate")
  expect(hex(litWire({ _tag: "str", value: "😀" }))).toEndWith("030000000000000004f09f9880")
})

test("a deep program uses the explicit work stack", () => {
  let p: Eff = { _tag: "succeed", value: { _tag: "lit", value: { _tag: "unit" } } }
  for (let i = 0; i < 15000; i++) p = { _tag: "exit", body: p }
  const encoded = effWire(p)
  // One single-argument constructor adds a 9-byte frame and a 10-byte ordinal.
  expect(encoded.length).toBe(55 + 15000 * 19)
})

test("different named atoms keep different wire bytes", () => {
  const parse = (atom: string) => {
    const p = readTypeScript(`Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, ${atom}))`)
    if (Result.isFailure(p)) throw new Error("control refused")
    return p.success
  }
  expect(hex(effWire(parse("incr")))).not.toBe(hex(effWire(parse("takeAndBump"))))
})
