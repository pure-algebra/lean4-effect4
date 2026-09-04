import { Effect, Exit, Fiber, Option, Result, Scope } from "effect"
import {
  Fibers,
  FibersRows,
  fiberChildrenRoundTrip,
  fiberDaemonSurvives,
  fiberEmptyRace,
  fiberForkInRegion,
  fiberForkJoin,
  fiberForkScopedAwait,
  fiberInterruptAllChildren,
  fiberMaskedRoot,
  fiberRaceAllRoots,
  fibersRoots,
  type FibersService
} from "./fibers-fixture.stub.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the twelve-row fiber profile
 * (`docs/research/2026-09-03-spike-s3-fork-flow.md` §2,
 * `workshop/Deep/fork-lowering.md` §(c)): one method per profile row, each of
 * them the rc.112 call the census row names, over the pinned
 * `effect@4.0.0-rc.112`.
 *
 * Nothing here is simulated. Every method below is a call into
 * `vendor/effect-4.0.0-rc.112/src/`, cited by line at its definition, and the
 * two places where rc.112 has no public surface for what the profile asks for
 * are marked REFUSAL rather than reimplemented:
 *
 *  - `childrenSnapshot` / `awaitChildren` are the two halves of rc.112's fused
 *    `awaitAllChildren`; see the comment on `childrenOf` below.
 *  - `awaitFiber`'s answer loses the interruptor and the defect payload, which
 *    is the loss `ForkFlow.lean:330-338` records for `exitAsValue`.
 *
 * **A fork names a declared root, never a closure.** `fork`, `forkScoped`,
 * `raceAll`, `uninterruptibleIn` and `interruptibleIn` all take a root — the
 * **block id** of a declared root, which is what the L1 lane's synthetic case
 * `Lowering.rootEntryBase + block` is keyed on
 * (`docs/research/2026-09-03-lowering-l1-fiber-profile.md` §3) — and an
 * argument list; `enter` resolves it through the fixture's exported **root
 * table** (`fork-lowering.md` §(b)). A request naming no declared root dies
 * with a defect rather than starting something (§(c) note 4); in Lean the same
 * request is `WithFiberAction.refuse`.
 *
 * **Immediacy is not a request field** (§(c) note 2). Every fork sets
 * `startImmediately: false`, so the child is queued and nothing of it runs
 * yet; which fiber then holds the processor is read off the golden's tape and
 * handed over through `TapeScheduler`'s `armed` hook in `tracer.ts`. This tail
 * installs no scheduler of its own.
 *
 * **Handles.** A fiber never reaches the wire as an object: `registerHandle`
 * brands it and `wire` encodes it as its index in first-seen order, which is
 * the fork order the Lean face numbers children in.
 *
 * Two spellings of `fork-lowering.md` §(c) are wrong against rc.112 and are
 * corrected here, with the correction recorded in
 * `docs/research/2026-09-03-lowering-l2-host-tails.md`:
 *   - there is no `Effect.forkDaemon` at this pin; the daemon fork is
 *     `Effect.forkDetach` (`Effect.ts:17168`, `internal/effect.ts:5287-5311`);
 *   - `Effect.yieldNow` is an Effect *value* (`Effect.ts:2350`), not a call;
 *     the priority-taking form is `Effect.yieldNowWith`
 *     (`Effect.ts:2374`, `internal/effect.ts:982-994`).
 */

// The brand rc.112 stamps on every fiber (`Fiber.ts:24` TypeId). It is a
// string key, not an exported value, so it is written out here.
const FiberTypeId = "~effect/Fiber"
registerHandle((value) => FiberTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "forkJoin"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const stallMs = Number(process.env.EFFECT4_STALL_MS ?? "50")
const sink: Event[] = []

/** The decision tape, in the golden's own spelling: `site:1` for a fork that
 * hands the processor to the run loop, `site:0` for one that does not. The
 * site is the fork's ordinal, which is what the Lean face numbers its forks
 * by (the retired M3 `fiber-tail.ts` used the same convention). */
const tape: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",")
  .filter((entry) => entry.length > 0)
  .map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })

class TapeExhausted extends Error { readonly _tag = "TAPE_EXHAUSTED" }
class TapeSiteMismatch extends Error { readonly _tag = "TAPE_SITE_MISMATCH" }

let cursor = 0
/** Answer the fork at the next site from the tape and record the `decide` row. */
const decide = (): boolean => {
  const entry = tape[cursor]
  if (entry === undefined) throw new TapeExhausted(`fork site ${cursor} past the end of the tape`)
  if (entry[0] !== cursor) throw new TapeSiteMismatch(`wanted site ${cursor}, tape has ${entry[0]}`)
  cursor += 1
  sink.push({ kind: "decide", site: entry[0], branch: entry[1] })
  return entry[1]
}

/** Armed by a `true` decision, consumed by `TapeScheduler.shouldYield`. */
let armed = false
const consumeArmed = (): boolean => {
  if (!armed) return false
  armed = false
  return true
}

/** Queue the child, answer the tape, and on `true` spend one primitive with the
 * scheduler armed so the run loop drains its queue. */
const forkWith = (
  fork: Effect.Effect<Fiber.Fiber<number, number>>
): Effect.Effect<Fiber.Fiber<number, number>> =>
  Effect.gen(function*() {
    const fiber = yield* fork
    if (decide()) {
      armed = true
      yield* Effect.sync(() => {})
    }
    return fiber
  })

/** The traced service, bound once the tracer has wrapped it. A root's body is
 * a program over `Fibers`, so a fork has to hand the same traced service to
 * the child it starts; nothing is provided until then. */
let traced: FibersService | null = null

/**
 * Resolve a fork's `root` field through the fixture's root table
 * (`fork-lowering.md` §(b)) and hand the child the traced service.
 *
 * A request naming no declared root is a **defect**, not a typed failure:
 * nothing in the flow declared it, so a `performCatch` must not catch it
 * (§(c) note 4, `ForkFlow.lean:1466-1478` witness E).
 */
const enter = (root: number, args: ReadonlyArray<unknown>): Effect.Effect<number, number> =>
  Effect.suspend(() => {
    const body = fibersRoots.get(root)
    if (body === undefined) {
      return Effect.die(new Error(`fork: the request names no declared root ${root}`))
    }
    if (traced === null) {
      return Effect.die(new Error("fork: the traced Fibers service is not installed"))
    }
    return Effect.provideService(body(args), Fibers, traced)
  })

/**
 * The region table: a region id names the `Scope` the region's generator
 * opened, which is what `Effect.forkIn` links the child's lifetime to. Regions
 * are opened before the `run` sentinel so only the operations are compared,
 * and a request naming an unopened region dies rather than forking somewhere
 * else (§(c) note 4).
 *
 * `Scope.makeUnsafe` — `Scope.ts:271`, `internal/effect.ts:3915-3922`; the
 * default finalizer strategy is `"sequential"`.
 */
const regions = new Map<number, Scope.Closeable>([[0, Scope.makeUnsafe()]])

/** The ambient `Scope` of the calling fiber, which is what `forkScoped` reads
 * (`internal/effect.ts:5400-5406`: `flatMap(scope, scope => forkIn(...))`).
 * The profile makes `forkScoped` a row of its own precisely because this scope
 * is a fact of the fiber's *context* and not something a request can name
 * (spike S3 §2). */
const ambient = Scope.makeUnsafe()

/**
 * `Exit` to `Result`, the `awaitFiber` answer, and the one loss this row
 * carries: a cause with **no `Fail` reason** — a die, an interrupt — has no
 * `Val` preimage, and `ForkFlow.lean:330-338`'s `exitAsValue` reads it as
 * unit. `Exit.findErrorOption` (`Exit.ts:1283`) is the typed-error projection;
 * `undefined` is what `wire` renders as `"[]"`, i.e. unit, so the failure arm
 * carries the absence rather than inventing a number.
 */
const exitToResult = (exit: Exit.Exit<number, number>): Result.Result<number, number> => {
  // `Exit.isSuccess` — `Exit.ts:393`.
  if (Exit.isSuccess(exit)) return Result.succeed(exit.value)
  const error = Exit.findErrorOption(exit)
  return Result.fail(
    (Option.isSome(error) ? error.value : undefined) as unknown as number
  )
}

/**
 * REFUSAL — rc.112 has **no public surface** for the snapshot half of
 * `awaitAllChildren`.
 *
 * The tracked children live on the fiber *implementation*: the field is
 * `_children` (`internal/effect.ts:534`), the accessor is `children()`
 * (`:703-705`), and `forkUnsafe` populates it only for a non-daemon fork
 * (`:5279-5282`), so a `forkDetach`/`forkIn` child is never tracked. The
 * public `Fiber.Fiber` interface (`Fiber.ts:70-92`) exposes neither the field
 * nor the accessor, and the package's `exports` map sends `./internal/*` to
 * `null`, so `FiberImpl` cannot be imported. The only public combinator is the
 * **fused** `Effect.awaitAllChildren` (`Effect.ts:17207`,
 * `internal/effect.ts:5314-5334`), which snapshots and awaits around one
 * effect and never hands the snapshot out.
 *
 * The read below is therefore of rc.112's own state through a cast — it
 * simulates nothing, and it computes nothing rc.112 does not already hold —
 * and the corresponding Lean rows (`childrenSnapshot`, `awaitChildren`) must
 * be refusals until rc.112 exports the pair.
 */
const childrenOf = (
  fiber: Fiber.Fiber<unknown, unknown>
): ReadonlyArray<Fiber.Fiber<number, number>> => {
  const tracked = (fiber as unknown as {
    readonly _children?: Set<Fiber.Fiber<number, number>> | undefined
  })._children
  return tracked === undefined ? [] : Array.from(tracked)
}

const live: FibersService = {
  /**
   * `forkIn` when the request names a region (`internal/effect.ts:5337-5379`),
   * `forkDetach` when it asks for a daemon (`:5287-5311`), `forkChild`
   * otherwise (`:5228-5261`); all three go through `forkUnsafe`
   * (`:5264-5284`). `daemon` is consulted only when `region` is `none`,
   * because `forkIn` forks a daemon in rc.112 anyway (`:5366`, `daemon = true`)
   * — review finding 14, `fork-lowering.md` §(c) note 1.
   */
  fork: (root, args, daemon, region) => {
    const child = enter(root, args)
    if (Option.isSome(region)) {
      const scope = regions.get(region.value)
      if (scope === undefined) {
        return Effect.die(new Error(`fork: the request names no open region ${region.value}`))
      }
      return forkWith(Effect.forkIn(child, scope, { startImmediately: false }))
    }
    return forkWith(
      daemon
        ? Effect.forkDetach(child, { startImmediately: false })
        : Effect.forkChild(child, { startImmediately: false })
    )
  },
  /**
   * `Effect.forkScoped` — `Effect.ts:17128`, `internal/effect.ts:5400-5406`:
   * `flatMap(scope, scope => forkIn(self, scope, options))`, i.e. `forkIn` on
   * the ambient `Scope` of the calling fiber. A `forkScoped` whose request
   * names a region is refused (`ForkRefusal.scopedNamesRegion`, spike S3 §2),
   * so the two unused request fields are refused here rather than ignored.
   */
  forkScoped: (root, args, daemon, region) => {
    if (Option.isSome(region)) {
      return Effect.die(new Error("forkScoped: the request names a region (scopedNamesRegion)"))
    }
    if (daemon) {
      return Effect.die(new Error("forkScoped: the request asks for a daemon (scopedNamesRegion)"))
    }
    return forkWith(
      Effect.provideService(
        Effect.forkScoped(enter(root, args), { startImmediately: false }),
        Scope.Scope,
        ambient
      )
    )
  },
  // `Fiber.join` — `Fiber.ts:279` = `internal/effect.ts:814-856` (`fiberJoin`):
  // the child's exit continues in this fiber as an *effect*, so a failed child
  // fails the caller. This is the row that carries a real `errorTy`.
  join: (fiber) => Fiber.join(fiber),
  // `Fiber.await` — `Fiber.ts:161-198` (`await_ as await`) =
  // `internal/effect.ts:767-778` (`fiberAwait`): the child's exit continues as
  // a *value*, so this row never fails.
  awaitFiber: (fiber) => Effect.map(Fiber.await(fiber), exitToResult),
  // `Fiber.interrupt` — `Fiber.ts:354` = `internal/effect.ts:857-861`
  // (`fiberInterrupt`): record with the running fiber's id, then await it.
  interruptFiber: (fiber) => Fiber.interrupt(fiber),
  // `Fiber.interruptAll` — `Fiber.ts:527` = `internal/effect.ts:888-901`
  // (`fiberInterruptAll`): record on every target first, then await them all.
  interruptAll: (fibers) => Fiber.interruptAll(fibers),
  // REFUSAL, see `childrenOf`. `Effect.withFiber` — `Effect.ts:2392`.
  childrenSnapshot: Effect.withFiber((self) => Effect.succeed(childrenOf(self))),
  // The exit half of `awaitAllChildren` (`internal/effect.ts:5322-5331`): the
  // children *added since* the snapshot, awaited through `Fiber.awaitAll`
  // (`Fiber.ts:235` = `internal/effect.ts:779-813`). Same refusal.
  awaitChildren: (snapshot) =>
    Effect.withFiber((self) =>
      Effect.asVoid(
        Fiber.awaitAll(childrenOf(self).filter((child) => !snapshot.includes(child)))
      )
    ),
  // `Effect.raceAll` — `Effect.ts:8760` = `internal/effect.ts:1477-1534`: one
  // `callback` over immediate forks of every entrant. An empty entrant list is
  // pending by construction (`len === 0` resumes nobody), which is the
  // `emptyRacePendingUntilInterrupted` shape; no special case is added here.
  raceAll: (entrants) => Effect.raceAll(entrants.map(([root, args]) => enter(root, args))),
  // `Effect.uninterruptible` — `Effect.ts:14306` =
  // `internal/effect.ts:4302-4310`: clears the running fiber's `interruptible`
  // flag and pushes the `setInterruptibleTrue` frame that restores it.
  uninterruptibleIn: (root, args) => Effect.uninterruptible(enter(root, args)),
  // `Effect.interruptible` — `Effect.ts:14199` =
  // `internal/effect.ts:4331-4337`.
  interruptibleIn: (root, args) => Effect.interruptible(enter(root, args)),
  // `Effect.yieldNowWith` — `Effect.ts:2374` = `internal/effect.ts:982-994`:
  // schedules the resume on the fiber's own dispatcher at the given priority
  // and yields. `Effect.yieldNow` (`:997`) is `yieldNowWith(0)` as a value.
  yieldNow: (priority) => Effect.yieldNowWith(priority)
}

const fibersProgram = (
  lowered: (n: number) => Effect.Effect<unknown, number, Fibers>,
  argument: number
) =>
  Effect.gen(function*() {
    const service = traceService(FibersRows, live, sink)
    traced = service
    sink.push({ kind: "phase", phase: "run" })
    return yield* lowered(argument).pipe(Effect.provideService(Fibers, service))
  })

const programs: Record<string, Effect.Effect<unknown, number, never>> = {
  forkJoin: fibersProgram(fiberForkJoin, 7),
  forkScopedAwait: fibersProgram(fiberForkScopedAwait, 11),
  forkInRegion: fibersProgram(fiberForkInRegion, 13),
  daemonSurvives: fibersProgram(fiberDaemonSurvives, 17),
  childrenRoundTrip: fibersProgram(fiberChildrenRoundTrip, 19),
  interruptAllChildren: fibersProgram(fiberInterruptAllChildren, 23),
  raceAllRoots: fibersProgram(fiberRaceAllRoots, 29),
  maskedRoot: fibersProgram(fiberMaskedRoot, 31),
  emptyRace: fibersProgram(fiberEmptyRace, 37)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

/** A run that parks — an empty race, which resumes nobody — evaluates no
 * further primitive, so the op budget cannot fire. The stall deadline turns
 * the park into the same frontier a spent budget writes (`RunOptions.stallMs`
 * in `tracer.ts`). */
const stalls = name === "emptyRace"

const report = await runTraced(
  program as Effect.Effect<unknown, never, never>,
  sink,
  stalls
    ? { budget, maxOpsBeforeYield, armed: consumeArmed, stallMs }
    : { budget, maxOpsBeforeYield, armed: consumeArmed }
)
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  // Every `true` on the tape is one handover, so a run whose tape has one
  // yields by construction and the driver's single-fiber yield check does not
  // apply; a run whose tape has none never hands the processor over.
  expectYields: tape.some(([, branch]) => branch),
  foreign: []
}))
