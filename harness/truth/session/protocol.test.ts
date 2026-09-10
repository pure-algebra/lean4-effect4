import { describe, expect, test } from "bun:test"
import { Effect, Exit, Fiber } from "effect"
import { decode, ProtocolRefusal, type Expected, type Recording } from "./protocol.ts"
import { ScalarRecorder } from "./record.ts"

// Representative decoder fixture. The integration driver supplies the actual Lean view;
// these tests independently mutate every field of this finite expected table.
const expected: Expected = { program: "two", natBound: 8, table: [{
  name: "wait", spelling: "Host.wait", shape: "call", trailing: [], kind: "async",
  request: { _tag: "nat" }, answer: { _tag: "nat" }, error: { _tag: "prod", left: { _tag: "string" }, right: { _tag: "string" } },
  requires: [], cite: "src/Effect4/Program/Profile.lean", typeArgs: [], registration: "external"
}] }
const fresh = async (): Promise<Recording> => {
  const r = new ScalarRecorder("session-A", expected)
  const out = await r.run(Effect.flatMap(r.Host.wait(2), () => r.Host.wait(3)))
  expect(Exit.isSuccess(out.exit) && out.exit.value).toBe(3)
  return out.recording
}
const mutate = (r: Recording, change: (x: any) => void): unknown => { const x = structuredClone(r); change(x); return x }

describe("serial scalar recorder and strict protocol", () => {
  test("two actual Effect calls retain call-start identities", async () => {
    const r = await fresh()
    expect(r.records.map(x => [x.kind, x.callId])).toEqual([["call", 0], ["reply", 0], ["call", 1], ["reply", 1]])
    expect(decode(r, expected)).toEqual(r)
  })
  test("valid pending and completed-call prefixes retain their records", async () => {
    const r = await fresh()
    for (const count of [0, 1, 2, 3]) expect(decode({ ...r, records: r.records.slice(0, count) }, expected).records).toHaveLength(count)
  })
  test("actual typed failure keeps category/tag/message", async () => {
    const r = new ScalarRecorder("failure", expected, 7)
    const out = await r.run(r.Host.wait(7))
    expect(Exit.isFailure(out.exit)).toBe(true)
    expect(out.recording.records[1]).toMatchObject({ completion: { kind: "fail", error: ["Scalar", "selected failure"], diagnostic: { category: "Fail", tag: "Scalar", message: "selected failure" } } })
  })
  test("independent provenance and sequencing mutants refuse", async () => {
    const r = await fresh()
    const mutants: Array<(x: any) => void> = [
      x => x.header.version++, x => x.header.format = "legacy", x => x.header.program = "other",
      x => x.header.profile = "other", x => x.header.session = "", x => x.records[0].session = "other",
      x => x.records[1].session = "other", x => x.records[0].version++, x => x.records[1].version++,
      x => x.records[0].fiber++, x => x.records[0].runtimeFiber++, x => x.records[0].row++,
      x => x.records[0].callId++, x => x.records[1].callId++, x => x.records[1].unexpected = true,
      x => x.records.splice(2, 0, x.records[1]), x => x.records.reverse(),
      x => x.records[1].completion.failed = ["x", "y"],
      x => x.records[1].completion.value = -1, x => x.records[1].completion.value = 1.5,
      x => x.records[1].completion = { kind: "interrupt" },
      x => x.records[1].completion = { kind: "fail", error: ["a", "b"], diagnostic: { category: "Die", tag: "a", message: "b" } },
      x => x.records[1].completion = { kind: "die", message: "a", diagnostic: { category: "Die", message: "b" } }
    ]
    for (const change of mutants) expect(() => decode(mutate(r, change), expected)).toThrow(ProtocolRefusal)
    for (const key of Object.keys(expected.table[0]!)) {
      expect(() => decode(mutate(r, x => delete x.header.table[0][key]), expected)).toThrow("full table mismatch")
      expect(() => decode(mutate(r, x => x.header.table[0][key] = "changed"), expected)).toThrow("full table mismatch")
    }
  })
  test("bound violations are outside-profile; cannot be caught into agreement", async () => {
    const r = await fresh()
    try { decode(mutate(r, x => x.records[0].request = 9), expected); throw Error("accepted") }
    catch (e) { expect(e).toBeInstanceOf(ProtocolRefusal); expect((e as ProtocolRefusal).category).toBe("outsideProfile") }
    const recorder = new ScalarRecorder("outside", expected)
    await expect(recorder.run(Effect.catchCause(recorder.Host.wait(9), () => Effect.succeed(0)))).rejects.toMatchObject({ category: "outsideProfile" })
  })
  test("child-fiber calls cannot borrow the root identity", async () => {
    const recorder = new ScalarRecorder("child", expected)
    await expect(recorder.run(Effect.gen(function* () {
      const fiber = yield* Effect.forkChild(recorder.Host.wait(2))
      return yield* Effect.andThen(Fiber.await(fiber), Effect.succeed(0))
    }))).rejects.toThrow()
  })
})
