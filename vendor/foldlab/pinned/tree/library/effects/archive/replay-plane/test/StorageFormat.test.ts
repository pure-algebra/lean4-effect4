/**
 * Backward-compatibility pins for the internal storage format.
 *
 * Histories and witnesses are durable CAS content: bytes written today
 * must decode forever, so the format is pinned by GOLDEN LITERALS —
 * encoding these fixtures must reproduce the recorded bytes exactly,
 * and decoding the recorded bytes must reproduce the fixtures. Any
 * encoder change that would strand existing stored histories turns
 * this suite red before it lands. A seeded structural sweep guards the
 * general value codec's round-trip beyond the fixtures.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Schema } from "effect"
import {
  decodeHistoryEntry,
  decodeStoredValue,
  decodeWitness,
  encodeHistoryEntry,
  encodeStoredValue,
  encodeWitness,
  StoredHistoryEntry,
  StoredWitness,
} from "../src/internal/storage.ts"

const hex = (bytes: Uint8Array): string => Buffer.from(bytes).toString("hex")

const goldenWitness = Schema.decodeUnknownSync(StoredWitness)({
  mode: "record",
  executionId: "golden-1",
  consumed: 2,
  trace: [
    { _tag: "LiveDelegation", operation: "op/a", at: 0 },
    { _tag: "TypedRejection", category: "DelegationOutstanding", at: 1 },
  ],
  outcome: {
    _tag: "Rejected",
    category: "UnsolicitedOutcome",
    at: 1,
    terminalSoFar: { _tag: "Succeeded", value: "v" },
  },
  historyRoot: "ab".repeat(32),
})

const GOLDEN_WITNESS_HEX =
  "464c52500102080000000600000008636f6e73756d65640340000000000000000000000b657865637574696f6e49640400000008676f6c64656e2d310000000b686973746f7279526f6f74040000004061626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162000000046d6f646504000000067265636f7264000000076f7574636f6d650800000004000000045f746167040000000852656a6563746564000000026174033ff00000000000000000000863617465676f72790400000012556e736f6c6963697465644f7574636f6d650000000d7465726d696e616c536f4661720800000002000000045f74616704000000095375636365656465640000000576616c756504000000017600000005747261636505000000020800000003000000045f746167040000000e4c69766544656c65676174696f6e000000026174030000000000000000000000096f7065726174696f6e04000000046f702f610800000003000000045f746167040000000e547970656452656a656374696f6e000000026174033ff00000000000000000000863617465676f7279040000001544656c65676174696f6e4f75747374616e64696e67"

const goldenEntry = Schema.decodeUnknownSync(StoredHistoryEntry)({
  op: "op/a",
  revision: 3,
  request: "req-1",
  outcome: { _tag: "Success", value: "ok" },
})

const GOLDEN_ENTRY_HEX =
  "464c525001010800000004000000026f7004000000046f702f61000000076f7574636f6d650800000002000000045f7461670400000007537563636573730000000576616c756504000000026f6b000000077265717565737404000000057265712d31000000087265766973696f6e034008000000000000"

const goldenValue = {
  a: [1, -2.5, true, null, "s", { b: "c" }],
  big: 10n,
  bytes: new Uint8Array([1, 2, 3]),
}

const GOLDEN_VALUE =
  "080000000300000001610500000006033ff000000000000003c00400000000000002000400000001730800000001000000016204000000016300000003626967070000000231300000000562797465730600000003010203"

it.effect("witness and history bytes are pinned — old artifacts decode forever", () =>
  Effect.sync(() => {
    expect(hex(encodeWitness(goldenWitness))).toBe(GOLDEN_WITNESS_HEX)
    expect(hex(encodeHistoryEntry(goldenEntry))).toBe(GOLDEN_ENTRY_HEX)
    expect(encodeStoredValue(goldenValue)).toBe(GOLDEN_VALUE)

    const witness = Schema.decodeUnknownSync(StoredWitness)(
      decodeWitness(Uint8Array.from(Buffer.from(GOLDEN_WITNESS_HEX, "hex"))),
    )
    expect(witness).toEqual(goldenWitness)
    const entry = Schema.decodeUnknownSync(StoredHistoryEntry)(
      decodeHistoryEntry(Uint8Array.from(Buffer.from(GOLDEN_ENTRY_HEX, "hex"))),
    )
    expect(entry).toEqual(goldenEntry)
    expect(decodeStoredValue(GOLDEN_VALUE)).toEqual(goldenValue)
  }))

/** splitmix32 — deterministic structural generator for the sweep. */
const splitmix32 = (seed: number) => () => {
  seed = (seed + 0x9e3779b9) | 0
  let z = seed
  z = Math.imul(z ^ (z >>> 16), 0x21f0aaad)
  z = Math.imul(z ^ (z >>> 15), 0x735a2d97)
  z = z ^ (z >>> 15)
  return (z >>> 0) / 0x1_0000_0000
}

const generate = (rng: () => number, depth: number): unknown => {
  const pick = Math.floor(rng() * (depth > 0 ? 9 : 6))
  switch (pick) {
    case 0: return null
    case 1: return rng() < 0.5
    case 2: return Math.floor(rng() * 0x1_0000_0000) - 0x8000_0000
    case 3: return `s${Math.floor(rng() * 1e6)}\n"\\🀄`
    case 4: return BigInt(Math.floor(rng() * 1e9)) * (rng() < 0.5 ? -1n : 1n)
    case 5: return new Uint8Array(Array.from({ length: Math.floor(rng() * 9) },
      () => Math.floor(rng() * 256)))
    case 6: return Array.from({ length: Math.floor(rng() * 4) },
      () => generate(rng, depth - 1))
    default: {
      const out: Record<string, unknown> = {}
      const size = Math.floor(rng() * 4)
      for (let index = 0; index < size; index += 1) {
        out[`k${Math.floor(rng() * 100)}`] = generate(rng, depth - 1)
      }
      return out
    }
  }
}

it.effect("the value codec round-trips seeded structures beyond the fixtures", () =>
  Effect.sync(() => {
    for (let seed = 1; seed <= 64; seed += 1) {
      const rng = splitmix32(seed)
      const value = generate(rng, 3)
      expect({ seed, value: decodeStoredValue(encodeStoredValue(value)) })
        .toEqual({ seed, value })
    }
  }))
