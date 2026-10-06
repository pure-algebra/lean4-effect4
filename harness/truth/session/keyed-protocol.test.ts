import { describe, expect, test } from "bun:test"
import { allows, decodeKeyed, hostProtocol, transition, type KeyedHeader, type KeyedRecording, type DecisionRecord } from "./keyed-protocol.ts"
import { KeyedRecorder, valueJson, wireValue, type KeyedFixture } from "./keyed-recorder.ts"
import { ArmedDispatchers, ScriptedHost, bindScenario, declareScenario, scenarioEffect, scenarioRef } from "./keyed-bindings.ts"
import { Data, Effect, Fiber, Option, Ref, Result } from "effect"
import { setImmediate as nextTurn } from "node:timers/promises"
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

// The scenarios' half of the recorder (decisions row 254). A fixture is `scripted` or it is not.
describe("scripted recorder", () => {
  const call = { callId: 0, fiber: 1, token: 5, row: 0, request: 7 }
  const fixture = (scripted: boolean): KeyedFixture => ({
    name: "scripted", expression: "", table: [{}], source: null, plan: [call], expected: null, ...(scripted ? { scripted: true as const } : {})
  })
  /** One fiber parked on one call of the recorder. */
  const parked = (recorder: KeyedRecorder, work: Effect.Effect<number> = Effect.succeed(7)) =>
    Effect.runFork(recorder.external(0, 7, work))

  test("an unmarked fixture keeps today's refusals, and it takes no scripted branch", async () => {
    const recorder = new KeyedRecorder(fixture(false), "plain")
    const fiber = parked(recorder)
    // The call is recorded when it starts, with the plan's call id.
    expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "call"])
    expect(() => recorder.apply(call)).toThrow("no stored reply for selected key")
    await expect(recorder.arrive({ fiber: 9, token: 9 })).rejects.toThrow("unknown or duplicate arrival")
    await Effect.runPromise(Fiber.interrupt(fiber))
    // After the cancellation the call is gone: a reply is a refusal of the recorder, no record.
    await expect(recorder.arrive(call)).rejects.toThrow("unknown or duplicate arrival")
    expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "call"])
    expect(recorder.measurements()).toMatchObject({ held: [], retired: [], refusals: [] })
  })

  test("an unmarked fixture refuses an operation that completes after its cancellation", async () => {
    const recorder = new KeyedRecorder(fixture(false), "plain")
    let complete!: (value: number) => void
    const fiber = parked(recorder, Effect.promise(() => new Promise<number>(resolve => { complete = resolve })))
    const arrival = recorder.arrive(call)
    await Effect.runPromise(Fiber.interrupt(fiber))
    complete(7)
    await expect(arrival).rejects.toThrow("operation completed after cancellation; binding cleanup required")
    expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "call"])
  })

  test("a scripted fixture records a call when the script holds it", async () => {
    const recorder = new KeyedRecorder(fixture(true), "scripted")
    const fiber = parked(recorder)
    expect(recorder.records.map(record => record.kind)).toEqual(["evaluate"])
    expect(() => recorder.hold({ fiber: 9, token: 9 })).toThrow("did not start")
    recorder.hold(call)
    expect(() => recorder.hold(call)).toThrow("twice")
    expect(recorder.records.at(-1)).toMatchObject({ kind: "call", callId: 0, fiber: 1, token: 5, row: 0, request: 7 })
    await recorder.arrive(call)
    recorder.apply(call)
    expect(await Effect.runPromise(Fiber.join(fiber))).toBe(7)
    const { held, receipts, applications, retired, refusals } = recorder.measurements()
    expect(held).toEqual([{ ...call, state: "applied", reply: { success: 7 } }])
    expect([receipts.length, applications.length, retired.length, refusals.length]).toEqual([1, 1, 0, 0])
    expect(recorder.snapshot().records.map(record => record.kind)).toEqual(["evaluate", "call", "reply", "apply"])
  })

  test("a late reply is recorded, stored nowhere and predicted as noCall", async () => {
    const recorder = new KeyedRecorder(fixture(true), "scripted")
    parked(recorder)
    recorder.hold(call)
    recorder.cancel(1)
    await recorder.arrive(call)
    recorder.apply(call)
    const { held, receipts, retired, stored, refusals } = recorder.measurements()
    expect(recorder.records.map(record => record.kind)).toEqual(["evaluate", "call", "cancel", "reply", "apply"])
    expect(held).toEqual([{ ...call, state: "retired", kept: false }])
    expect(retired).toEqual([{ call: held[0]!, kept: false }])
    expect([receipts, stored]).toEqual([[], []])
    expect(refusals).toEqual([{ at: 3, row: "submit", reason: "noCall" }, { at: 4, row: "apply", reason: "noCall" }])
  })

  test("a stored reply stays with its retired call, and a second reply is predicted as pendingReply", async () => {
    const recorder = new KeyedRecorder(fixture(true), "scripted")
    parked(recorder)
    recorder.hold(call)
    await recorder.arrive(call)
    await recorder.arrive(call)
    recorder.cancel(1)
    recorder.apply(call)
    const { retired, stored, receipts, refusals } = recorder.measurements()
    expect(retired.map(entry => entry.kept)).toEqual([true])
    expect([stored.length, receipts.length]).toEqual([0, 1])
    expect(refusals).toEqual([{ at: 3, row: "submit", reason: "pendingReply" }, { at: 5, row: "apply", reason: "noCall" }])
  })

  test("a call that the script never held leaves no retired record", async () => {
    const recorder = new KeyedRecorder(fixture(true), "scripted")
    parked(recorder)
    recorder.cancel(1)
    expect(recorder.measurements()).toMatchObject({ held: [], retired: [], live: [] })
    expect(() => recorder.cancel(4)).toThrow("no runtime fiber")
  })

  test("a record is its frame, and a scripted value is the frame's record", () => {
    class Deposit extends Data.TaggedError("Deposit")<{ readonly amount: number }> {}
    expect(valueJson({ status: 200, body: "bob" })).toEqual({ ctor: 0, args: [["body", "status"], ["bob", 200]] })
    expect(valueJson(new Deposit({ amount: 1 }))).toEqual({ ctor: 0, args: [["_tag", "amount"], ["Deposit", 1]] })
    expect(wireValue({ some: { ctor: 0, args: [["id", "name"], [2, "bob"]] } })).toEqual(Option.some({ id: 2, name: "bob" }))
    expect(wireValue(null)).toBeUndefined()
    expect(() => wireValue({ ctor: 1, args: [1] })).toThrow("outside the selected transport profile")
  })
})

// The readers (decisions row 254): each is a note, and each is off unless a run turns it on.
describe("scenario readers", () => {
  test("the cells reader's Ref owns `make` only, and its cell is the pinned one", () => {
    declareScenario("reader/cells", [])
    const host = new ScriptedHost(new KeyedRecorder({ name: "reader/cells", expression: "", table: [], source: null, plan: [], expected: null, scripted: true }, "reader"))
    bindScenario("reader/cells", host)
    const spied = scenarioRef("reader/cells")
    expect(Object.keys(spied)).toEqual(["make"])
    for (const name of Object.keys(Ref) as Array<keyof typeof Ref>) if (name !== "make") expect(spied[name]).toBe(Ref[name])
    const cell = Effect.runSync(spied.make(7))
    expect([host.cells.length, host.cells[0] === (cell as unknown)]).toEqual([1, true])
    expect(Effect.runSync(Ref.updateAndGet(cell, n => n + 1))).toBe(8)
    expect(Ref.getUnsafe(host.cells[0]!)).toBe(8)
    // A faulty Ref, for the red control of the host's measurement, also owns `update`.
    expect(Object.keys(scenarioRef("reader/cells", "drops-assignment"))).toEqual(["make", "update"])
    bindScenario("reader/cells", undefined)
  })

  test("the fibers reader's Effect owns the three fork heads, in both call forms", async () => {
    declareScenario("reader/fibers", [])
    const host = new ScriptedHost(new KeyedRecorder({ name: "reader/fibers", expression: "", table: [], source: null, plan: [], expected: null, scripted: true }, "reader"))
    bindScenario("reader/fibers", host)
    const spied = scenarioEffect("reader/fibers")
    expect(Object.keys(spied).sort()).toEqual(["forkChild", "forkDetach", "forkScoped"])
    for (const name of Object.keys(Effect) as Array<keyof typeof Effect>)
      if (!Object.hasOwn(spied, name)) expect(spied[name]).toBe(Effect[name])
    const options = { startImmediately: true, uninterruptible: "inherit" } as const
    const first = await Effect.runPromise(Effect.flatMap(spied.forkChild(Effect.succeed(1), options), fiber => Effect.map(Fiber.join(fiber), value => [fiber, value] as const)))
    const second = await Effect.runPromise(Effect.flatMap(Effect.succeed(2).pipe(spied.forkDetach(options)), fiber => Effect.map(Fiber.join(fiber), value => [fiber, value] as const)))
    expect([first[1], second[1]]).toEqual([1, 2])
    expect(host.forks.map(fork => fork.id)).toEqual([first[0].id, second[0].id])
    bindScenario("reader/fibers", undefined)
  })

  test("the sleeps reader is off by default, and it lists a sleep from its start to its end", async () => {
    const clock = await Rc112ClockBoundary.make()
    try {
      expect(() => clock.sleeps()).toThrow("off")
      clock.noteSleeps()
      const fiber = Effect.runFork(clock.provide(Effect.sleep(5)))
      expect(clock.sleeps().map(sleep => [sleep.fiber, sleep.wake])).toEqual([[fiber, 5n]])
      await clock.advance("5")
      await Effect.runPromise(Fiber.join(fiber))
      expect(clock.sleeps()).toEqual([])
    } finally {
      await clock.dispose()
    }
  })

  test("the dispatchers reader counts an armed dispatcher until its turn", async () => {
    const dispatchers = new ArmedDispatchers()
    const fiber = Effect.runFork(Effect.andThen(Effect.yieldNow, Effect.succeed(3)), { scheduler: dispatchers.scheduler })
    expect(dispatchers.armed()).toBe(1)
    await dispatchers.idle()
    expect(dispatchers.armed()).toBe(0)
    expect(fiber.pollUnsafe()).toBeDefined()
    await nextTurn()
    expect(dispatchers.armed()).toBe(0)
  })
})
