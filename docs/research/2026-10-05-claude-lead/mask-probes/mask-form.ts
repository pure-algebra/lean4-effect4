// The mask's printed form against the native mask (2026-10-05). Finite host runs on one
// Effect 4 build, not proofs.
// Run: EFFECT_DIR=<an effect package directory> bun run mask-form.ts
//
// `native` is Effect.uninterruptibleMask. `printed` is the form that the second mask note
// proposes to print: the getter is the mask at the constant body that answers its restore,
// the body runs under Effect.uninterruptible, and a restore site is `effect.pipe(saved)`.
import { readFileSync } from "node:fs"
const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Fiber, Deferred, Exit, Cause } = await import(`${dir}/dist/index.js`)

type Restore = (e: any) => any
type Mask = (body: (restore: Restore) => any) => any
const native: Mask = (body) => Effect.uninterruptibleMask(body)
const getter = Effect.uninterruptibleMask((a0: Restore) => Effect.succeed(a0))
const printed: Mask = (body) =>
  Effect.flatMap(getter, (a0: Restore) => Effect.uninterruptible(body(a0)))

const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const exitWord = (exit: any): string =>
  Exit.isSuccess(exit) ? `success(${exit.value})`
    : Cause.hasInterruptsOnly(exit.cause) ? "interrupted" : "failed"

// S1. What the getter answers: the public `interruptible` under an interruptible caller, and
// a function that returns its argument under a masked caller.
const s1 = Effect.gen(function*() {
  const open: Restore = yield* getter
  const masked: Restore = yield* Effect.uninterruptible(getter)
  const probe = Effect.succeed(1)
  return { interruptibleCaller: open === Effect.interruptible, maskedCallerIsIdentity: masked(probe) === probe }
})

// S2. An interruptible caller. The body logs, waits inside a restore site, and logs again.
// The fiber is interrupted while it waits.
const s2 = (mask: Mask) => Effect.gen(function*() {
  const log: Array<string> = []
  const f = yield* Effect.forkChild(mask((restore) => Effect.gen(function*() {
    log.push("body entered")
    yield* Effect.never.pipe(restore)
    log.push("after the wait")
  })))
  yield* settle
  yield* Fiber.interrupt(f)
  log.push(exitWord(yield* Fiber.await(f)))
  return log
})

// S3. A masked caller. The same body waits on a deferred inside a restore site. The fiber is
// interrupted while it waits, and the deferred is then resolved.
const s3 = (mask: Mask) => Effect.gen(function*() {
  const log: Array<string> = []
  const d = yield* Deferred.make()
  const f = yield* Effect.forkChild(Effect.uninterruptible(mask((restore) => Effect.gen(function*() {
    log.push("body entered")
    const v = yield* Deferred.await(d).pipe(restore)
    log.push(`received ${v}`)
    return v
  }))))
  yield* settle
  const stop = yield* Effect.forkChild(Fiber.interrupt(f))
  yield* settle
  log.push(f.pollUnsafe() === undefined ? "still running after the interrupt" : "ended")
  yield* Deferred.succeed(d, 7)
  yield* settle
  log.push(exitWord(yield* Fiber.await(f)))
  yield* Fiber.await(stop)
  return log
})

// S4. An interruptible caller; no restore site. The body yields twice between three logs,
// and the fiber is interrupted after the first.
const s4 = (mask: Mask) => Effect.gen(function*() {
  const log: Array<string> = []
  const f = yield* Effect.forkChild(mask((_restore) => Effect.gen(function*() {
    log.push("one")
    yield* settle
    log.push("two")
    yield* settle
    log.push("three")
    return 3
  })))
  yield* Effect.yieldNow
  const stop = yield* Effect.forkChild(Fiber.interrupt(f))
  log.push(exitWord(yield* Fiber.await(f)))
  yield* Fiber.await(stop)
  return log
})

// S5. Nested masks under an interruptible caller. Inside the inner mask, a wait under the
// inner restore is not interruptible, and a wait under the outer restore is.
const s5 = (mask: Mask, useOuter: boolean) => Effect.gen(function*() {
  const log: Array<string> = []
  const d = yield* Deferred.make()
  const f = yield* Effect.forkChild(mask((outer) => mask((inner) => Effect.gen(function*() {
    log.push("inner body entered")
    const v = yield* Deferred.await(d).pipe(useOuter ? outer : inner)
    log.push(`received ${v}`)
  }))))
  yield* settle
  const stop = yield* Effect.forkChild(Fiber.interrupt(f))
  yield* settle
  log.push(f.pollUnsafe() === undefined ? "still running after the interrupt" : "ended")
  yield* Deferred.succeed(d, 7)
  yield* settle
  log.push(exitWord(yield* Fiber.await(f)))
  yield* Fiber.await(stop)
  return log
})

// S6. A restore that leaves its mask. The mask answers its restore, and a masked child fiber
// applies it to a wait after the mask ended. The child is then interrupted.
const s6 = (mask: Mask) => Effect.gen(function*() {
  const log: Array<string> = []
  const kept: Restore = yield* mask((restore) => Effect.succeed(restore))
  const child = yield* Effect.forkChild(
    Effect.gen(function*() {
      log.push("child entered")
      yield* Effect.never.pipe(kept)
      log.push("child after the wait")
    }),
    { uninterruptible: true }
  )
  yield* settle
  const stop = yield* Effect.forkChild(Fiber.interrupt(child))
  yield* settle
  log.push(child.pollUnsafe() === undefined ? "child still running" : exitWord(child.pollUnsafe()))
  yield* Fiber.await(stop)
  return log
})

// S7. A failure and a defect inside the body leave the caller's interruptibility as it was.
const flagAfter = (mask: Mask, body: any) => Effect.gen(function*() {
  yield* Effect.exit(mask((_restore) => body))
  return yield* Effect.withFiber((fiber: any) => Effect.succeed(fiber.interruptible as boolean))
})
const s7 = (mask: Mask) => Effect.gen(function*() {
  return {
    afterSuccess: yield* flagAfter(mask, Effect.succeed(1)),
    afterFailure: yield* flagAfter(mask, Effect.fail("e")),
    afterDefect: yield* flagAfter(mask, Effect.die("d")),
    maskedAfterSuccess: yield* Effect.uninterruptible(flagAfter(mask, Effect.succeed(1))),
    maskedAfterFailure: yield* Effect.uninterruptible(flagAfter(mask, Effect.fail("e")))
  }
})

// S8. The loop iterations that each form spends, read from the fiber's operation counter.
const counted = (e: any) => Effect.gen(function*() {
  const before: number = yield* Effect.withFiber((fiber: any) => Effect.succeed(fiber.currentOpCount as number))
  yield* e
  const after: number = yield* Effect.withFiber((fiber: any) => Effect.succeed(fiber.currentOpCount as number))
  return after - before
})
const s8 = Effect.gen(function*() {
  const base = yield* counted(Effect.succeed(0))
  return {
    succeedAlone: base,
    getter: (yield* counted(getter)) - base,
    getterMasked: (yield* Effect.uninterruptible(counted(getter))) - base,
    restoreSiteOpen: (yield* counted(Effect.succeed(0).pipe(Effect.interruptible))) - base,
    restoreSiteUnderMask: (yield* Effect.uninterruptible(counted(Effect.succeed(0).pipe(Effect.interruptible)))) - base,
    nativeMask: (yield* counted(native((_r) => Effect.succeed(0)))) - base,
    printedMask: (yield* counted(printed((_r) => Effect.succeed(0)))) - base
  }
})

const both = (name: string, run: (mask: Mask) => any) => Effect.gen(function*() {
  const n = yield* run(native)
  const p = yield* run(printed)
  return { native: n, printed: p, same: JSON.stringify(n) === JSON.stringify(p) }
})

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.s1_getter = yield* s1
  out.s2_interruptibleCaller = yield* both("s2", s2)
  out.s3_maskedCaller = yield* both("s3", s3)
  out.s4_bodyIsMasked = yield* both("s4", s4)
  out.s5_nestedInnerRestore = yield* both("s5i", (m) => s5(m, false))
  out.s5_nestedOuterRestore = yield* both("s5o", (m) => s5(m, true))
  out.s6_restoreLeavesItsMask = yield* both("s6", s6)
  out.s7_flagAfterEachExit = yield* both("s7", s7)
  out.s8_iterations = yield* s8
  return out
})
Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r, null, 1)))
