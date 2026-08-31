import { expect, it } from "@effect/vitest"
import { Effect, Option } from "effect"
import { ContentId } from "../../src/cas/Node.ts"
import {
  decodeKeyListDocument,
  decodePresenceDocument,
  encodeKeyListDocument,
  encodePresenceDocument,
  keyListDocumentEncodedLength,
} from "../../src/internal/wire.ts"

const key = (byte: number): ContentId => ContentId.make(byte.toString(16).padStart(2, "0").repeat(32))

it.effect("the key-list framing is canonical, exact, and order preserving", () => Effect.sync(() => {
  const keys = [key(0x12), key(0xab)]
  const encoded = encodeKeyListDocument(keys)
  expect(encoded.length).toBe(68)
  expect(Array.from(encoded.subarray(0, 4))).toEqual([0, 0, 0, 2])
  expect(decodeKeyListDocument(encoded)).toEqual(Option.some(keys))
  expect(decodeKeyListDocument(encodeKeyListDocument([...keys].reverse())))
    .toEqual(Option.some([...keys].reverse()))
  expect(Option.isNone(decodeKeyListDocument(encoded.subarray(0, encoded.length - 1)))).toBe(true)

  const trailing = new Uint8Array(encoded.length + 1)
  trailing.set(encoded)
  expect(Option.isNone(decodeKeyListDocument(trailing))).toBe(true)
}))

it("key-list encoded length is exact without allocation and rejects non-u32 counts", () => {
  expect(keyListDocumentEncodedLength(0)).toEqual(Option.some(4))
  expect(keyListDocumentEncodedLength(2)).toEqual(Option.some(68))
  expect(keyListDocumentEncodedLength(0xffff_ffff))
    .toEqual(Option.some(4 + 0xffff_ffff * 32))
  expect(Option.isNone(keyListDocumentEncodedLength(-1))).toBe(true)
  expect(Option.isNone(keyListDocumentEncodedLength(0x1_0000_0000))).toBe(true)
  expect(Option.isNone(keyListDocumentEncodedLength(1.5))).toBe(true)
})

it.effect("the presence framing is canonical, exact, and positionally aligned", () => Effect.sync(() => {
  const present = key(0x12)
  const missing = key(0xab)
  const failed = key(0x7f)
  const keys = [present, missing, failed]
  const statuses = ["present", "missing", "failed"] as const

  const encoded = encodePresenceDocument(statuses)
  expect(Array.from(encoded)).toEqual([1, 0, 2])

  const decoded = decodePresenceDocument(keys, encoded)
  expect(decoded).toEqual(Option.some({
    presence: { present: [present], missing: [missing], failed: [failed] },
    statuses: [...statuses],
  }))

  // A successful decode's input is exactly the canonical encoding of its result.
  if (Option.isNone(decoded)) throw new Error("presence document failed to decode")
  expect(Array.from(encodePresenceDocument(decoded.value.statuses)))
    .toEqual(Array.from(encoded))

  // Exactly one byte per requested key: no header, no trailing content.
  expect(Option.isNone(decodePresenceDocument(keys, encoded.subarray(0, 2)))).toBe(true)
  const overlong = new Uint8Array(encoded.length + 1)
  overlong.set(encoded)
  expect(Option.isNone(decodePresenceDocument(keys, overlong))).toBe(true)

  // Only the three declared status bytes decode.
  expect(Option.isNone(decodePresenceDocument(keys, Uint8Array.from([1, 0, 3])))).toBe(true)
}))
