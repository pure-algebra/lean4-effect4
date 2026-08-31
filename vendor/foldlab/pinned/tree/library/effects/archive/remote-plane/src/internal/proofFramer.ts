/** Incremental proof-frame parser mirrored from Effects/Merkle/Parser.lean. */
import { Data } from "effect"
import type { DInput } from "./merkleDecoder.ts"

export type ProofFrame = DInput<ReadonlyArray<number>>

export type FrameParse = Data.TaggedEnum<{
  Parsed: {
    readonly item: ProofFrame
    readonly remainder: ReadonlyArray<number>
  }
  NeedMore: {}
  Malformed: {}
}>

export const FrameParse = Data.taggedEnum<FrameParse>()

export type FramerResult = Data.TaggedEnum<{
  Parsed: {
    readonly items: ReadonlyArray<ProofFrame>
    readonly remainder: ReadonlyArray<number>
  }
  Malformed: {}
}>

export const FramerResult = Data.taggedEnum<FramerResult>()

const readNat32 = (bytes: ReadonlyArray<number>, offset: number): number =>
  (bytes[offset] ?? 0) * 0x1000000
  + (bytes[offset + 1] ?? 0) * 0x10000
  + (bytes[offset + 2] ?? 0) * 0x100
  + (bytes[offset + 3] ?? 0)

/** Parse exactly the first frame, retaining every unconsumed input byte. */
export const parseFrame = (bytes: ReadonlyArray<number>): FrameParse => {
  const tag = bytes[0]
  if (tag === undefined) return FrameParse.NeedMore()
  if (tag === 0) {
    return FrameParse.Parsed({
      item: { _tag: "SkipNode" },
      remainder: bytes.slice(1),
    })
  }
  if (tag === 1) {
    if (bytes.length < 5) return FrameParse.NeedMore()
    const length = readNat32(bytes, 1)
    const end = 5 + length
    if (bytes.length < end) return FrameParse.NeedMore()
    return FrameParse.Parsed({
      item: { _tag: "ChunkNode", bytes: bytes.slice(5, end) },
      remainder: bytes.slice(end),
    })
  }
  if (tag === 2) {
    if (bytes.length < 65) return FrameParse.NeedMore()
    return FrameParse.Parsed({
      item: {
        _tag: "ParentNode",
        left: bytes.slice(1, 33),
        right: bytes.slice(33, 65),
      },
      remainder: bytes.slice(65),
    })
  }
  return FrameParse.Malformed()
}

/** Drain the maximal complete prefix, preserving a partial final frame. */
export const drain = (bytes: ReadonlyArray<number>): FramerResult => {
  const items: Array<ProofFrame> = []
  let remainder = bytes
  while (remainder.length > 0) {
    const parsed = parseFrame(remainder)
    switch (parsed._tag) {
      case "Malformed":
        return FramerResult.Malformed()
      case "NeedMore":
        return FramerResult.Parsed({ items, remainder: remainder.slice() })
      case "Parsed":
        items.push(parsed.item)
        remainder = parsed.remainder
        break
    }
  }
  return FramerResult.Parsed({ items, remainder: [] })
}

/** Feed one transport fragment into the current incremental parse state. */
export const feed = (
  state: FramerResult,
  fragment: ReadonlyArray<number>,
): FramerResult => {
  if (state._tag === "Malformed") return state
  const next = drain([...state.remainder, ...fragment])
  return next._tag === "Malformed"
    ? next
    : FramerResult.Parsed({
        items: [...state.items, ...next.items],
        remainder: next.remainder,
      })
}

/** Fold transport fragments left-to-right through the incremental parser. */
export const feedAll = (
  fragments: ReadonlyArray<ReadonlyArray<number>>,
): FramerResult => {
  let state: FramerResult = FramerResult.Parsed({ items: [], remainder: [] })
  for (const fragment of fragments) state = feed(state, fragment)
  return state
}
