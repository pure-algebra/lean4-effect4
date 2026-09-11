import { describe, expect, test } from "bun:test"
import { allows, decodeKeyed, transition, type KeyedHeader, type KeyedRecording, type DecisionRecord } from "./keyed-protocol.ts"
import { valueJson } from "./keyed-recorder.ts"
import { Result } from "effect"
const expected = { program: "two", table: [{}] }
const header: KeyedHeader = { format: "effect4-host-session-v2", version: 2, session: "s", profile: "keyed-v2", ...expected }
const record = (kind: string, fields: Record<string, unknown> = {}): DecisionRecord => ({ kind, version: 2, session: "s", ...fields })
const call = (fiber: number, token: number, callId: number) => record("call", { fiber, token, callId, row: 0, request: callId })
const reply = (fiber: number, token: number, callId: number) => record("reply", { fiber, token, callId, completion: { success: callId } })
const apply = (fiber: number, token: number) => record("apply", { fiber, token })
const valid: KeyedRecording = { header, records: [call(1, 0, 0), call(2, 1, 1), reply(2, 1, 1), reply(1, 0, 0), apply(1, 0), apply(2, 1)] }
describe("projected keyed tape structure", () => {
  test("replies arrive by key; application order remains independent", () => { expect(decodeKeyed(valid, expected)).toEqual(valid) })
  test.each(["fiber", "token", "callId"])("missing %s is not inferred", field => {
    const tape = structuredClone(valid); delete tape.records[2]![field]
    expect(() => decodeKeyed(tape, expected)).toThrow()
  })
  test("duplicate pending reply", () => { expect(() => decodeKeyed({ header, records: [...valid.records.slice(0, 4), valid.records[2]] }, expected)).toThrow() })
  test("application without a stored reply", () => { expect(() => decodeKeyed({ header, records: [call(1, 0, 0), apply(1, 0)] }, expected)).toThrow() })
  test("one key cannot replace another key's payload", () => { expect(() => decodeKeyed({ header, records: [call(1, 0, 0), reply(1, 1, 0)] }, expected)).toThrow() })
  test("legacy format requires explicit migration", () => { expect(() => decodeKeyed({ ...valid, header: { ...header, version: 1 } }, expected)).toThrow() })
  test("table metadata participates in identity", () => { expect(() => decodeKeyed({ ...valid, header: { ...header, table: [{ trailing: ["x"] }] } }, expected)).toThrow() })
  test("pending and unanswered prefixes are accepted", () => { expect(decodeKeyed({ header, records: valid.records.slice(0, 3) }, expected).records).toHaveLength(3) })
  test("unsafe and negative-zero keys refuse", () => {
    for (const n of [-1, -0, NaN, Infinity, Number.MAX_SAFE_INTEGER + 1]) expect(() => decodeKeyed({ header, records: [call(n, 0, 0)] }, expected)).toThrow()
  })
  test("clock and cancellation follow the generated table", () => {
    expect(allows("awaitingAsync", "answer", "terminated")).toBe(true)
    expect(transition("parked", "advanceClock", "idle")).toBe("idle")
    expect(() => transition("terminated", "answer", "idle")).toThrow()
    expect(() => transition("idle", "submit", "idle")).toThrow()
  })
  test("Result uses failure=0/success=1, with value/error alias order", () => {
    expect(valueJson(Result.succeed("ok"))).toEqual({ ctor: 1, args: ["ok"] })
    expect(valueJson(Result.fail(7))).toEqual({ ctor: 0, args: [7] })
  })
})
