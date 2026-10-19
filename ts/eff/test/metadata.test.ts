import { expect, test } from "bun:test"
import { Schema } from "effect"
import * as Types from "../eff.gen.ts"
import * as Wire from "../wire.gen.ts"
import * as Json from "../json.gen.ts"

const text = await Bun.file(new URL("../../../ocaml/eff/goldens/metadata.tsv", import.meta.url)).text()
const rows = text.trimEnd().split("\n").map((line) => line.split("\t"))
const selections = {
  Ty: [Types.Ty, Wire.tyWire, Json.tyJson],
  RowKind: [Types.RowKind, Wire.rowKindWire, Json.rowKindJson],
  RowShape: [Types.RowShape, Wire.rowShapeWire, Json.rowShapeJson],
  Registration: [Types.Registration, Wire.registrationWire, Json.registrationJson],
  Row: [Types.Row, Wire.rowWire, Json.rowJson],
  EffTy: [Types.EffTy, Wire.effTyWire, Json.effTyJson],
} as const

// A row of `metadata.tsv` (`OCaml5.Eff.Metadata`): the name, the family, Lean's canonical bytes, the
// OCaml goldens' own `V` spelling (an internal fixture format, read by no writer here), and the
// value's JSON node as Lean's `Tools.ProfileJson` writes it.
test("all six selected metadata families agree with canonical Lean bytes and write back their node", () => {
  const seen = new Set<string>()
  // Keep each schema/writer pair together at its actual carrier. No unchecked writer call.
  function compare<A>(schema: Schema.Codec<A>, wire: (a: A) => Uint8Array,
    json: (a: A) => unknown, node: unknown, hex: string, vValue: unknown) {
    const value = Schema.decodeUnknownSync(schema)(node)
    expect(Buffer.from(wire(value)).toString("hex")).toBe(hex)
    // the tagged print writes the node the schema read, up to the order of an object's keys
    expect(json(value)).toEqual(node)
    // the control: the goldens' `V` spelling of the same value is another JSON value
    expect(json(value)).not.toEqual(vValue)
  }
  for (const row of rows) {
    const [name, family, hex, vSpelling, node] = row
    if (row.length !== 5 || !name || !family || !hex || !vSpelling || !node) throw Error("metadata arity")
    seen.add(family)
    const input: unknown = JSON.parse(node)
    const vInput: unknown = JSON.parse(vSpelling)
    switch (family) {
      case "Ty": compare(...selections.Ty, input, hex, vInput); break
      case "RowKind": compare(...selections.RowKind, input, hex, vInput); break
      case "RowShape": compare(...selections.RowShape, input, hex, vInput); break
      case "Registration": compare(...selections.Registration, input, hex, vInput); break
      case "Row": compare(...selections.Row, input, hex, vInput); break
      case "EffTy": compare(...selections.EffTy, input, hex, vInput); break
      default: throw Error(`unsupported metadata family ${family}`)
    }
  }
  expect([...seen].sort()).toEqual(Object.keys(selections).sort())
})

test("requirement schema and writer reject duplicate and unordered keys", () => {
  const key = (name: number, service: number) => ({ name: { value: name }, service: { value: service } })
  for (const requires of [[key(1, 2), key(1, 2)], [key(2, 0), key(1, 3)], [key(1, 3), key(1, 2)]]) {
    const value: Types.EffTy = { answer: { _tag: "nat" }, error: { _tag: "never" }, requires }
    expect(() => Schema.decodeUnknownSync(Types.EffTy)(value)).toThrow()
    expect(() => Wire.effTyWire(value)).toThrow("noncanonical requirements")
  }
  expect(() => Schema.decodeUnknownSync(Types.EffTy)({ answer: { _tag: "unsupported" }, error: { _tag: "never" }, requires: [] })).toThrow()
})
