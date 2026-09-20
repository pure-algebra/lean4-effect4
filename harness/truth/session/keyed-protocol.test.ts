import { describe, expect, test } from "bun:test"
import { allows, decodeKeyed, hostProtocol, transition, type KeyedHeader, type KeyedRecording, type DecisionRecord } from "./keyed-protocol.ts"
import { KeyedRecorder, valueJson, type KeyedFixture } from "./keyed-recorder.ts"
import { Effect, Fiber, Result } from "effect"
import { ProfileRefusal, Rc112ClockBoundary } from "./clock.ts"
const expected = { program: "two", table: [{}] }
const header: KeyedHeader = { format: "effect4-host-session-v3", version: hostProtocol.version, session: "s", profile: "keyed-v3", ...expected }
const record = (kind: string, fields: Record<string, unknown> = {}): DecisionRecord => ({ kind, version: hostProtocol.version, session: "s", ...fields })
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
  test("decimal clock transport has protocol version 3", () => {
    expect(hostProtocol.version).toBe(3)
    expect(decodeKeyed(valid, expected)).toEqual(valid)
  })
  test.each([1, 2])("legacy version %i requires explicit migration", version => {
    const legacy = { header: { ...header, format: `effect4-host-session-v${version}`,
      version, profile: `keyed-v${version}` }, records: [] }
    expect(() => decodeKeyed(legacy, expected)).toThrow("version 3 required")
  })
  test("version 2 clock records cannot enter a version 3 tape", () => {
    for (const millis of [1, "1"])
      expect(() => decodeKeyed({ header, records: [
        { kind: "advanceClock", version: 2, session: "s", millis }
      ] }, expected)).toThrow("record identity mismatch")
  })
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
  test("clock transport keeps canonical decimal text beyond host integer ranges", () => {
    for (const millis of ["0", "9007199254740993", "4611686018427387904"]) {
      const tape = { header, records: [record("advanceClock", { millis })] }
      expect(decodeKeyed(tape, expected)).toEqual(tape)
    }
    for (const millis of [1, "00", "01", "-1", "+1", "1e3"])
      expect(() => decodeKeyed({ header, records: [record("advanceClock", { millis })] }, expected)).toThrow()
  })
  test("Result uses failure=0/success=1, with value/error alias order", () => {
    expect(valueJson(Result.succeed("ok"))).toEqual({ ctor: 1, args: ["ok"] })
    expect(valueJson(Result.fail(7))).toEqual({ ctor: 0, args: [7] })
  })
})

describe("keyed clock execution", () => {
  const fixture = (plan: KeyedFixture["plan"] = []): KeyedFixture => ({
    name: "clock-order", expression: "", table: [{}], source: null, plan, expected: 7
  })
  const readySignal = () => {
    let signal!: () => void
    const ready = new Promise<void>(resolve => { signal = resolve })
    return { signal, ready }
  }

  test("an advance is recorded before the host call it wakes", async () => {
    const clock = await Rc112ClockBoundary.make()
    const call = { callId: 0, fiber: 0, token: 1, row: 0, request: 7 }
    const recorder = new KeyedRecorder(fixture([call]), "clock-order")
    const started = readySignal()
    const fiber = Effect.runFork(clock.provide(Effect.gen(function* () {
      yield* Effect.sync(started.signal)
      yield* Effect.sleep(1)
      return yield* recorder.external(0, 7, Effect.succeed(7))
    })))
    try {
      await started.ready
      await recorder.advanceClock(clock, "1")
      expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "advanceClock", "call"])
      expect(recorder.records[1]).toMatchObject({ version: 3, millis: "1" })
      expect(clock.now()).toBe(1n)
      await recorder.arrive(call)
      recorder.apply(call)
      expect(await Effect.runPromise(Fiber.join(fiber))).toBe(7)
      expect(recorder.finish().records.map(record => record.kind)).toEqual([
        "evaluate", "advanceClock", "call", "reply", "apply", "flush"
      ])
    } finally {
      await Effect.runPromise(Fiber.interrupt(fiber))
      await clock.dispose()
    }
  })

  test("malformed and overflowing advances neither record nor mutate, and refuse the receipt", async () => {
    for (const millis of ["01", "9007199254740992"]) {
      const clock = await Rc112ClockBoundary.make()
      const recorder = new KeyedRecorder(fixture(), "preflight")
      const before = structuredClone(recorder.records)
      try {
        await expect(recorder.advanceClock(clock, millis)).rejects.toThrow()
        expect(clock.now()).toBe(0n)
        expect(recorder.records).toEqual(before)
        expect(() => recorder.finish()).toThrow()
      } finally {
        await clock.dispose()
      }
    }
  })

  test("a refusal from a woken continuation rejects the advance and prevents a receipt", async () => {
    const clock = await Rc112ClockBoundary.make()
    const recorder = new KeyedRecorder(fixture(), "woken-refusal")
    const started = readySignal()
    const fiber = Effect.runFork(clock.provide(Effect.gen(function* () {
      yield* Effect.sync(started.signal)
      yield* Effect.sleep(1)
      yield* Effect.sleep(Number.MAX_SAFE_INTEGER)
    })))
    try {
      await started.ready
      await expect(recorder.advanceClock(clock, "1")).rejects.toBeInstanceOf(ProfileRefusal)
      expect(clock.now()).toBe(1n)
      expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "advanceClock"])
      expect(() => recorder.finish()).toThrow(ProfileRefusal)
      expect(recorder.records.some(record => record.kind === "flush")).toBe(false)
    } finally {
      await Effect.runPromise(Fiber.interrupt(fiber))
      await clock.dispose()
    }
  })

  test("queued advances validate against their own input clock before recording", async () => {
    const clock = await Rc112ClockBoundary.make()
    const recorder = new KeyedRecorder(fixture(), "queued-advances")
    try {
      await recorder.advanceClock(clock, "9007199254740990")
      const results = await Promise.allSettled([
        recorder.advanceClock(clock, "1"), recorder.advanceClock(clock, "1")
      ])
      expect(results.map(result => result.status)).toEqual(["fulfilled", "rejected"])
      expect(clock.now()).toBe(9007199254740991n)
      expect(recorder.records.filter(record => record.kind === "advanceClock").map(record => record.millis))
        .toEqual(["9007199254740990", "1"])
      expect(() => recorder.finish()).toThrow(ProfileRefusal)
    } finally {
      await clock.dispose()
    }
  })
})
