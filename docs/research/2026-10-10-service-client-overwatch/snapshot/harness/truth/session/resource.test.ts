import { expect, test } from "bun:test"
import { Cause, Effect, Exit, Fiber } from "effect"
import { ResourceBinding, ResourceHandle, resourceSpent, resourceTarget } from "./resource.ts"

const failure = (exit: Exit.Exit<unknown, unknown>) => Exit.isFailure(exit) ? exit.cause.reasons : []

test("failed use charges state; real scoped finalization closes it once", async () => {
  const binding = new ResourceBinding("failure-owned")
  const result = await binding.run(Effect.scoped(Effect.gen(function* () {
    const r = yield* Effect.acquireRelease(binding.Host.acquire(), r => binding.Host.release(r).pipe(Effect.orDie))
    yield* binding.Host.use(r)
    yield* binding.Host.use(r)
    return yield* binding.Host.use(r)
  })))
  expect(failure(result.exit)).toMatchObject([{ _tag: "Fail", error: resourceSpent }])
  expect(result.state).toEqual({ slots: [false], uses: 3, closes: [1], compensated: [] })
  expect(result.records.filter(x => x.kind === "reply").map(x => x.completion.kind)).toEqual(["success", "success", "success", "fail", "success"])
  expect(result.records[1]).toMatchObject({ completion: { kind: "success", value: 0 } })
})

test("closed use and double release retain category/message without more work", async () => {
  const binding = new ResourceBinding("closed")
  const result = await binding.run(Effect.gen(function* () {
    const r = yield* binding.Host.acquire()
    yield* binding.Host.release(r)
    const used = yield* Effect.exit(binding.Host.use(r))
    const closed = yield* Effect.exit(binding.Host.release(r))
    return [used, closed] as const
  }))
  expect(result.state).toEqual({ slots: [false], uses: 0, closes: [1], compensated: [] })
  expect(Exit.isSuccess(result.exit)).toBe(true)
  if (Exit.isSuccess(result.exit)) {
    expect(failure(result.exit.value[0])).toMatchObject([{ _tag: "Die", defect: "resource used after release" }])
    expect(failure(result.exit.value[1])).toMatchObject([{ _tag: "Die", defect: "resource released twice" }])
  }
  expect(result.records.at(-1)).toMatchObject({ completion: { kind: "die", message: "resource released twice", diagnostic: { category: "Die", message: "resource released twice" } } })
})

test("two independently owned allocations need two completed releases", async () => {
  const binding = new ResourceBinding("two-owned")
  const result = await binding.run(Effect.scoped(Effect.gen(function* () {
    const a = yield* Effect.acquireRelease(binding.Host.acquire(), r => binding.Host.release(r).pipe(Effect.orDie))
    const b = yield* Effect.acquireRelease(binding.Host.acquire(), r => binding.Host.release(r).pipe(Effect.orDie))
    expect(a.index).toBe(0); expect(b.index).toBe(1)
    return yield* binding.Host.use(a)
  })))
  expect(result.state).toEqual({ slots: [false, false], uses: 1, closes: [1, 1], compensated: [] })
})

test("public metadata cannot impersonate a registered object", async () => {
  const binding = new ResourceBinding("identity")
  await expect(binding.run(Effect.gen(function* () {
    const real = yield* binding.Host.acquire()
    const forged = new ResourceHandle(real.session, real.index)
    return yield* Effect.catchCause(binding.Host.use(forged), () => Effect.succeed(0))
  }))).rejects.toThrow("impersonated")
  expect(binding.snapshot()).toEqual({ slots: [true], uses: 0, closes: [0], compensated: [] })
})

test("foreign session and never-acquired handle refuse before mutation", async () => {
  for (const handle of [new ResourceHandle("foreign", 0), new ResourceHandle("selected", 0)]) {
    const binding = new ResourceBinding("selected")
    await expect(binding.run(binding.Host.use(handle))).rejects.toThrow()
    expect(binding.snapshot()).toEqual({ slots: [], uses: 0, closes: [], compensated: [] })
  }
})

test("interrupted pending allocation compensates the later unclaimed object", async () => {
  const binding = new ResourceBinding("late")
  let release!: () => void
  const work = new Promise<void>(resolve => { release = resolve })
  const fiber = Effect.runFork(binding.delayedAcquire(work))
  await Effect.runPromise(Fiber.interrupt(fiber))
  expect(binding.snapshot().slots).toEqual([])
  release()
  await work
  await Promise.resolve()
  expect(binding.snapshot()).toEqual({ slots: [], uses: 0, closes: [], compensated: [{ physicalId: 0, open: false, closes: 1 }] })
  const exit = await Effect.runPromise(Fiber.await(fiber))
  expect(failure(exit).some(Cause.isInterruptReason)).toBe(true)
})


test("a compensated physical allocation does not consume a machine allocation index", async () => {
  const binding = new ResourceBinding("late-then-live")
  let release!: () => void
  const work = new Promise<void>(resolve => { release = resolve })
  const fiber = Effect.runFork(binding.delayedAcquire(work))
  await Effect.runPromise(Fiber.interrupt(fiber))
  release(); await work; await Promise.resolve()
  const result = await binding.run(Effect.gen(function* () {
    const handle = yield* binding.Host.acquire()
    expect(handle.index).toBe(0)
    yield* binding.Host.release(handle)
    return 0
  }))
  expect(result.state.slots).toEqual([false])
  expect(result.state.compensated).toEqual([{ physicalId: 0, open: false, closes: 1 }])
  expect(result.records[1]).toMatchObject({ completion: { kind: "success", value: 0 } })
})
