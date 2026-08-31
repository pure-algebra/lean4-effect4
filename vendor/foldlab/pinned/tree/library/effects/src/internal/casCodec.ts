/**
 * The scheme-0 canonical node codec, mirrored from
 * `Effects/Cas/Codec.lean`. Schema encoding is deliberately absent from
 * this digest pre-image. The codec lives beneath both the store and the
 * admission core so neither depends on the other.
 */
import { Encoding, Option } from "effect"
import { CasNodeInput, ContentId } from "../cas/Node.ts"
import { decodeValidatedHex } from "./bytes.ts"

/** The only scheme version currently admitted by the runtime adapter. */
export const CasSchemeVersion = 0

const writeNat32 = (target: Uint8Array, offset: number, value: number): void => {
  target[offset] = (value >>> 24) & 0xff
  target[offset + 1] = (value >>> 16) & 0xff
  target[offset + 2] = (value >>> 8) & 0xff
  target[offset + 3] = value & 0xff
}

const readNat32 = (source: Uint8Array, offset: number): number =>
  (source[offset] ?? 0) * 0x1000000
  + (source[offset + 1] ?? 0) * 0x10000
  + (source[offset + 2] ?? 0) * 0x100
  + (source[offset + 3] ?? 0)

/** Project-owned canonical encoder. */
export const encodeCasNode = (node: CasNodeInput): Uint8Array => {
  const size = 10 + node.payload.length + node.refs.length * 33
  const bytes = new Uint8Array(size)
  bytes[0] = node.kind.version
  bytes[1] = node.kind.tag
  writeNat32(bytes, 2, node.payload.length)
  bytes.set(node.payload, 6)

  let offset = 6 + node.payload.length
  writeNat32(bytes, offset, node.refs.length)
  offset += 4

  for (const ref of node.refs) {
    // The branded ContentId is validated 64-char lowercase hex, so the
    // total decoder has no failure branch to model.
    bytes[offset] = ref.expectedTag
    bytes.set(decodeValidatedHex(ContentId.make(ref.id)), offset + 1)
    offset += 33
  }

  return bytes
}

/** Closed decoder: parses exactly one canonical node and rejects every
 * truncation, malformed count, or trailing byte. Returns `Option` like
 * every other closed decoder in the package. */
export const decodeCasNode = (bytes: Uint8Array): Option.Option<CasNodeInput> => {
  if (bytes.length < 10) return Option.none()

  const payloadLength = readNat32(bytes, 2)
  const countOffset = 6 + payloadLength
  if (countOffset + 4 > bytes.length) return Option.none()

  const refCount = readNat32(bytes, countOffset)
  const refsOffset = countOffset + 4
  if (refsOffset + refCount * 33 !== bytes.length) return Option.none()

  const refs: Array<{ readonly id: ContentId; readonly expectedTag: number }> = []
  let offset = refsOffset
  for (let index = 0; index < refCount; index += 1) {
    const expectedTag = bytes[offset] ?? 0
    const id = ContentId.make(Encoding.encodeHex(bytes.subarray(offset + 1, offset + 33)))
    refs.push({ id, expectedTag })
    offset += 33
  }

  return Option.some(CasNodeInput.make({
    kind: { version: bytes[0] ?? 0, tag: bytes[1] ?? 0 },
    payload: bytes.slice(6, countOffset),
    refs,
  }))
}
