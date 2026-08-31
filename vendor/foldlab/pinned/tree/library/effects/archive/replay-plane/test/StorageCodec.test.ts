import { expect, it } from "@effect/vitest"
import { Encoding, Schema } from "effect"
import { ContentId } from "../src/cas/Node.ts"
import {
  decodeHistoryEntry,
  decodeWitness,
  encodeHistoryEntry,
  encodeWitness,
  StoredHistoryEntry,
  StoredWitness,
} from "../src/internal/storage.ts"

const HistoryBytes = "464c525001010800000004000000026f7004000000056f702fceb1000000076f7574636f6d650800000002000000045f74616704000000074661696c757265000000056572726f720400000002303400000007726571756573740400000003726571000000087265766973696f6e03401c000000000000"
const WitnessBytes = "464c52500102080000000600000008636f6e73756d6564033ff00000000000000000000b657865637574696f6e49640400000013776f726b65722d372f617474656d70742d34320000000b686973746f7279526f6f74040000004061626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162616261626162000000046d6f646504000000067265706c6179000000076f7574636f6d650800000002000000045f7461670400000009436f6d706c65746564000000087465726d696e616c0800000002000000045f74616704000000095375636365656465640000000576616c7565040000000e303430303030303030323666366200000005747261636505000000020800000002000000045f746167040000000f486973746f7279436f6e73756d65640000000261740300000000000000000800000002000000045f7461670400000009436f6d706c6574656400000008636f6e73756d6564033ff0000000000000"

it("internal history and witness encodings remain byte-identical", () => {
  const history = StoredHistoryEntry.make({
    op: "op/α",
    revision: 7,
    request: "req",
    outcome: { _tag: "Failure", error: "04" },
  })
  const witness = StoredWitness.make({
    mode: "replay",
    executionId: "worker-7/attempt-42",
    consumed: 1,
    trace: [
      { _tag: "HistoryConsumed", at: 0 },
      { _tag: "Completed", consumed: 1 },
    ],
    outcome: {
      _tag: "Completed",
      terminal: { _tag: "Succeeded", value: "04000000026f6b" },
    },
    historyRoot: ContentId.make("ab".repeat(32)),
  })

  const historyBytes = encodeHistoryEntry(history)
  const witnessBytes = encodeWitness(witness)
  expect(Encoding.encodeHex(historyBytes)).toBe(HistoryBytes)
  expect(Encoding.encodeHex(witnessBytes)).toBe(WitnessBytes)
  expect(Schema.decodeUnknownSync(StoredHistoryEntry)(decodeHistoryEntry(historyBytes)))
    .toEqual(history)
  expect(Schema.decodeUnknownSync(StoredWitness)(decodeWitness(witnessBytes)))
    .toEqual(witness)
})
