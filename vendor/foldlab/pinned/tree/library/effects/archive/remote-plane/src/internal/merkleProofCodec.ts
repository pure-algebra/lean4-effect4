/**
 * Closed proof-document codecs mirrored from Effects/Merkle/ProofCodec.lean.
 *
 * These carriers are proofs and slices, never CAS identity inputs. Successful
 * decoding consumes the input exactly and therefore returns the one canonical
 * document whose encoding is the original byte string.
 */
import { Match, Option, pipe, Schema } from "effect"
import type { Bytes } from "./merkleChunk.ts"
import type { DInput } from "./merkleDecoder.ts"

export type Address32 = ReadonlyArray<number>
export type ByteInput = Uint8Array | Bytes

export interface OpeningDoc {
  readonly index: number
  readonly total: number
  readonly leaf: Bytes
  readonly siblings: ReadonlyArray<Address32>
}

export interface StreamHeader {
  readonly total: number
  readonly lo: number
  readonly hi: number
}

export interface StreamDoc {
  readonly header: StreamHeader
  readonly items: ReadonlyArray<DInput<Address32>>
}

const UInt32Limit = 0x1_0000_0000
const ByteSchema = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xff }))
const ByteArraySchema = Schema.Array(ByteSchema)

const isUInt32 = (value: number): boolean =>
  Number.isInteger(value) && value >= 0 && value < UInt32Limit

const requireUInt32 = (value: number): void => {
  if (!isUInt32(value)) throw new RangeError(`not an unsigned 32-bit integer: ${value}`)
}

const requireBytes = (bytes: Bytes): void => {
  if (!bytes.every((byte) => Number.isInteger(byte) && byte >= 0 && byte <= 0xff)) {
    throw new RangeError("byte strings must contain only unsigned bytes")
  }
}

const requireAddress = (address: Address32): void => {
  if (address.length !== 32) {
    throw new RangeError("address must contain exactly 32 bytes")
  }
  requireBytes(address)
}

const decodeByteInput = (input: ByteInput): Option.Option<Bytes> =>
  Schema.decodeOption(ByteArraySchema)(Array.from(input))

export const encodeNat32 = (value: number): Bytes => {
  requireUInt32(value)
  return [
    Math.floor(value / 0x1_000000) % 0x100,
    Math.floor(value / 0x1_0000) % 0x100,
    Math.floor(value / 0x100) % 0x100,
    value % 0x100,
  ]
}

interface Nat32Read {
  readonly value: number
  readonly offset: number
}

const readNat32 = (bytes: Bytes, offset: number): Option.Option<Nat32Read> => {
  const a = bytes[offset]
  const b = bytes[offset + 1]
  const c = bytes[offset + 2]
  const d = bytes[offset + 3]
  if (a === undefined || b === undefined || c === undefined || d === undefined) {
    return Option.none()
  }
  return Option.some({
    value: a * 0x1_000000 + b * 0x1_0000 + c * 0x100 + d,
    offset: offset + 4,
  })
}

const readAddresses = (bytes: Bytes, offset: number): Option.Option<ReadonlyArray<Address32>> => {
  const remaining = bytes.length - offset
  if (remaining % 32 !== 0) return Option.none()
  const addresses: Array<Address32> = []
  for (let cursor = offset; cursor < bytes.length; cursor += 32) {
    addresses.push(bytes.slice(cursor, cursor + 32))
  }
  return Option.some(addresses)
}

export const encodeOpening = (doc: OpeningDoc): Bytes => {
  requireUInt32(doc.index)
  requireUInt32(doc.total)
  requireUInt32(doc.leaf.length)
  requireBytes(doc.leaf)
  for (const sibling of doc.siblings) requireAddress(sibling)
  return [
    ...encodeNat32(doc.index),
    ...encodeNat32(doc.total),
    ...encodeNat32(doc.leaf.length),
    ...doc.leaf,
    ...doc.siblings.flat(),
  ]
}

/** Closed opening decoder; a boundary after the leaf is a shorter document. */
export const decodeOpening = (input: ByteInput): Option.Option<OpeningDoc> => {
  const decodedBytes = decodeByteInput(input)
  if (Option.isNone(decodedBytes)) return Option.none()
  const bytes = decodedBytes.value
  const index = readNat32(bytes, 0)
  if (Option.isNone(index)) return Option.none()
  const total = readNat32(bytes, index.value.offset)
  if (Option.isNone(total)) return Option.none()
  const length = readNat32(bytes, total.value.offset)
  if (Option.isNone(length)) return Option.none()
  const leafEnd = length.value.offset + length.value.value
  if (leafEnd > bytes.length) return Option.none()
  const siblings = readAddresses(bytes, leafEnd)
  if (Option.isNone(siblings)) return Option.none()
  return Option.some({
    index: index.value.value,
    total: total.value.value,
    leaf: bytes.slice(length.value.offset, leafEnd),
    siblings: siblings.value,
  })
}

export const encodeItem: (item: DInput<Address32>) => Bytes = pipe(
  Match.type<DInput<Address32>>(),
  Match.withReturnType<Bytes>(),
  Match.tagsExhaustive({
    ChunkNode: (item) => {
      requireUInt32(item.bytes.length)
      requireBytes(item.bytes)
      return [1, ...encodeNat32(item.bytes.length), ...item.bytes]
    },
    ParentNode: (item) => {
      requireAddress(item.left)
      requireAddress(item.right)
      return [2, ...item.left, ...item.right]
    },
    SkipNode: () => [0],
  }),
)

const readItems = (
  bytes: Bytes,
  start: number,
): Option.Option<ReadonlyArray<DInput<Address32>>> => {
  const items: Array<DInput<Address32>> = []
  let offset = start
  while (offset < bytes.length) {
    const tag = bytes[offset]
    offset += 1
    if (tag === 0) {
      items.push({ _tag: "SkipNode" })
      continue
    }
    if (tag === 1) {
      const length = readNat32(bytes, offset)
      if (Option.isNone(length)) return Option.none()
      const end = length.value.offset + length.value.value
      if (end > bytes.length) return Option.none()
      items.push({ _tag: "ChunkNode", bytes: bytes.slice(length.value.offset, end) })
      offset = end
      continue
    }
    if (tag === 2) {
      const end = offset + 64
      if (end > bytes.length) return Option.none()
      items.push({
        _tag: "ParentNode",
        left: bytes.slice(offset, offset + 32),
        right: bytes.slice(offset + 32, end),
      })
      offset = end
      continue
    }
    return Option.none()
  }
  return Option.some(items)
}

export const encodeStream = (doc: StreamDoc): Bytes => {
  requireUInt32(doc.header.total)
  requireUInt32(doc.header.lo)
  requireUInt32(doc.header.hi)
  return [
    ...encodeNat32(doc.header.total),
    ...encodeNat32(doc.header.lo),
    ...encodeNat32(doc.header.hi),
    ...doc.items.flatMap(encodeItem),
  ]
}

export const decodeStream = (input: ByteInput): Option.Option<StreamDoc> => {
  const decodedBytes = decodeByteInput(input)
  if (Option.isNone(decodedBytes)) return Option.none()
  const bytes = decodedBytes.value
  const total = readNat32(bytes, 0)
  if (Option.isNone(total)) return Option.none()
  const lo = readNat32(bytes, total.value.offset)
  if (Option.isNone(lo)) return Option.none()
  const hi = readNat32(bytes, lo.value.offset)
  if (Option.isNone(hi)) return Option.none()
  const items = readItems(bytes, hi.value.offset)
  if (Option.isNone(items)) return Option.none()
  return Option.some({
    header: { total: total.value.value, lo: lo.value.value, hi: hi.value.value },
    items: items.value,
  })
}
