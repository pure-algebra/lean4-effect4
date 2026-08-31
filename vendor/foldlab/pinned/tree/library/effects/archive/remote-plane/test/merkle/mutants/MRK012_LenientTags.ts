import { Option } from "effect"
import type {
  Address32,
  StreamDoc,
} from "../../../src/internal/merkleProofCodec.ts"
import type { Bytes } from "../../../src/internal/merkleChunk.ts"
import type { DInput } from "../../../src/internal/merkleDecoder.ts"
import type { StreamDecodeFunction } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a stream reader that treats unknown item tags as skips instead of rejecting — a forward-compatibility reflex that lets an attacker splice unverified structure into a proof stream."

const readNat32 = (bytes: Bytes, offset: number): readonly [number, number] | undefined => {
  const a = bytes[offset]
  const b = bytes[offset + 1]
  const c = bytes[offset + 2]
  const d = bytes[offset + 3]
  return a === undefined || b === undefined || c === undefined || d === undefined
    ? undefined
    : [a * 0x1_000000 + b * 0x1_0000 + c * 0x100 + d, offset + 4]
}

/** Unknown tags are interpreted as bare skip tokens. */
export const mutantDecode: StreamDecodeFunction = (bytes) => {
  const total = readNat32(bytes, 0)
  if (total === undefined) return Option.none()
  const lo = readNat32(bytes, total[1])
  if (lo === undefined) return Option.none()
  const hi = readNat32(bytes, lo[1])
  if (hi === undefined) return Option.none()

  const items: Array<DInput<Address32>> = []
  let offset = hi[1]
  while (offset < bytes.length) {
    const tag = bytes[offset]
    offset += 1
    if (tag === 0 || (tag !== 1 && tag !== 2)) {
      items.push({ _tag: "SkipNode" })
      continue
    }
    if (tag === 1) {
      const length = readNat32(bytes, offset)
      if (length === undefined) return Option.none()
      const end = length[1] + length[0]
      if (end > bytes.length) return Option.none()
      items.push({ _tag: "ChunkNode", bytes: bytes.slice(length[1], end) })
      offset = end
      continue
    }
    const end = offset + 64
    if (end > bytes.length) return Option.none()
    items.push({
      _tag: "ParentNode",
      left: bytes.slice(offset, offset + 32),
      right: bytes.slice(offset + 32, end),
    })
    offset = end
  }

  return Option.some<StreamDoc>({
    header: { total: total[0], lo: lo[0], hi: hi[0] },
    items,
  })
}
