/**
 * run-truth.ts — the rc.112 face of the truth check.
 *
 * What it is: reads the Lean manifest (`corpus.json`, written by
 * `harness/truth/Truth.lean`), writes one generated module per program under
 * `generated/`, runs each under the pinned `effect@4.0.0-rc.112`, and compares rc.112's exit
 * and observable schedule with the Lean machine's. Writes `result.json` and `result.md`
 * (both GENERATED), prints the table, exits non-zero on any disagreement.
 *
 *     bun run <abs path>/harness/truth/run-truth.ts --manifest <corpus.json> [--out <dir>] [--timeout ms]
 *
 * Run it from `C:\Users\kokok\Dev\effect4-host` (the pinned installation) — `effect` resolves
 * through the `node_modules` junction `harness/truth/node_modules` → that installation's
 * `node_modules`, which `check-truth.ps1` creates; the cwd is not what resolves it.
 *
 * Depends on `effect` (rc.112) and `./prelude.ts` (the atoms; part of the truth claim).
 *
 * How rc.112 is observed — nothing is simulated, every hook is a documented rc.112 seam:
 *  - every primitive a fiber evaluates passes through `Tracer.Tracer`'s optional `context`
 *    hook (`internal/effect.ts:653-655`, installed by `setContext` `:729-730` from the fiber's
 *    context; a child inherits the parent's context, `:5273`), so the hook sees every fiber;
 *  - a fiber's exit fires its observers (`:619-623`); `addObserver` (`:560-573`);
 *  - a park or a yield is a primitive whose `evaluate` returns the `Yield` sentinel
 *    (`core.ts:61`) with `fiber._yielded` a function (`:1128`, `:990`); an exit is the same
 *    sentinel with `_yielded` an `Exit` (`:656-661`);
 *  - a fork's child is in the parent's `_children` set (`:5279-5281`, insertion = fork
 *    order); the hook scans it before the parent's next primitive, which is before
 *    `Fiber.await` registers its resume observer (`:772-774`), so the recorder's exit
 *    observer is registered ahead of the parent's;
 *  - tasks go through the scheduler's dispatcher (`Scheduler.ts:207-212`); the async entry
 *    installs a `MixedScheduler` subclass whose dispatcher records `scheduleTask` and each
 *    task run with the fiber that owns the dispatcher (`currentDispatcher` `:553-555` is
 *    created lazily inside that fiber's primitive).
 * The two entries are rc.112's own: `Effect.runSyncExitWith(context)` (`:5536-5545`) and the
 * `runForkWith` + `addObserver` pair that is `runPromiseExitWith` (`:5494-5505`), with a
 * deadline so a parked program cannot hang the check.
 *
 * Behaviours held:
 *  - honest: the generated module is the manifest's `decl` (or `expr`) verbatim under a fixed
 *    import header; nothing is patched to pass (by construction);
 *  - bounded: the promise entry races a deadline and interrupts the leftover fiber
 *    (`interruptUnsafe`, `:574`) so the process terminates (by construction);
 *  - one alphabet: the compared schedule is `started`, `forked`, `parked`, `resumed`, `ran`,
 *    `exited <kind>` over fiber indices in first-seen order (root `0`, children in fork
 *    order) — `scheduled` rows are recorded on both faces and dropped from the verdict,
 *    because the Lean trace records the fork's scheduling but not the yield's (NOTES.md §5);
 *  - exact where it can be: a success value and a `fail` payload are compared as JSON; a
 *    `die` and an `interrupt` are compared by kind, the payloads shown (the Lean defect
 *    alphabet has no host errors) (by construction, `compareExits`);
 *  - the prelude is checked before any program runs (tested: `selfTest`).
 */
import { Cause, Context, Effect, Exit, Scheduler, Tracer } from "effect"
import * as fs from "node:fs"
import * as path from "node:path"
import { pathToFileURL } from "node:url"
import { selfTestCases } from "./prelude.ts"

// ---- rc.112 keys (internal/core.ts:31-61, internal/effect.ts:492, :3766, Ref.ts:21,
// Deferred.ts:22, Exit.ts:20) ---------------------------------------------------------
const EVALUATE = "~effect/Effect/evaluate"
const IDENTIFIER = "~effect/Effect/identifier"
const YIELD = Symbol.for("effect/Effect/Yield")
const FIBER = "~effect/Fiber"
const EXIT = "~effect/Exit"
const REF = "~effect/Ref"
const DEFERRED = "~effect/Deferred"
const SCOPE = "~effect/Scope"

type Json = null | boolean | number | string | Json[] | { [key: string]: Json }

// ---- manifest -----------------------------------------------------------------------
interface LeanRun {
  outcome: string
  exit: Json
  exitKind: string | null
  fiberCount: number
  fibers: Array<{ id: number; exited: boolean; exit: Json; parkedToken: number | null }>
  events: string[]
  schedule: string[]
  internal: string[]
  frames: number
}
interface Entry {
  name: string
  wellTyped: boolean
  type: { answer: string; error: string; requiresEmpty: boolean } | null
  expr: string | null
  exprRefusal: string | null
  decl: string | null
  run: LeanRun
  runSync: { exit: Json; exitKind: string; sync: boolean }
}
interface Manifest { format: string; fuel: number; programs: Entry[] }

// ---- arguments ----------------------------------------------------------------------
const argv = process.argv.slice(2)
const option = (name: string, fallback: string): string => {
  const index = argv.indexOf(name)
  return index >= 0 && argv[index + 1] !== undefined ? argv[index + 1] : fallback
}
const here = path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1"))
const manifestPath = option("--manifest", path.join(here, "corpus.json"))
const outDir = option("--out", here)
const timeoutMs = Number(option("--timeout", "300"))

// ---- the prelude self-test ----------------------------------------------------------
const selfTest = (): string[] =>
  selfTestCases.flatMap(([name, apply, expected]) => {
    const got = apply()
    return got === expected ? [] : [`${name}: got ${JSON.stringify(got)}, wanted ${JSON.stringify(expected)}`]
  })

// ---- generation ---------------------------------------------------------------------
const importHeader = [
  "// GENERATED by harness/truth/run-truth.ts from harness/truth/corpus.json — do not edit.",
  "// Regenerate: harness/truth/check-truth.ps1",
  "import { Cause, Deferred, Effect, Exit, Fiber, Option, Ref, Scope } from \"effect\"",
  "import { succ, pred, isZero, not, add, lt, eq, pair, fst, snd, incr, double, takeAndBump, zeroWhenPositive, noChange } from \"../prelude.ts\"",
  ""
].join("\n")

/** The module text: the exported declaration verbatim, or `export const main = <expr>` when
 * the manifest has no declaration (ill-typed: `printDecl` refuses, `print` does not). */
const moduleFor = (entry: Entry): { text: string; source: "decl" | "expr" } | null => {
  if (entry.decl !== null) return { text: importHeader + entry.decl, source: "decl" }
  if (entry.expr !== null) return { text: importHeader + `export const main = ${entry.expr}\n`, source: "expr" }
  return null
}

// ---- the recorder -------------------------------------------------------------------
interface FiberLike {
  readonly id: number
  _children?: Set<FiberLike> | undefined
  _yielded?: unknown
  _exit?: unknown
  addObserver(cb: (exit: unknown) => void): () => void
  interruptUnsafe(fiberId?: number): void
}

class Recorder {
  /** rc.112 events, spelled like the manifest's `events` where the counterpart is exact. */
  readonly events: string[] = []
  /** The reduced schedule (`scheduled` rows included; the comparison drops them). */
  readonly schedule: string[] = []
  /** Per-fiber primitive identifiers, recorded, never compared. */
  readonly frames: string[] = []
  readonly index = new Map<object, number>()
  private readonly state = new Map<number, "fresh" | "running" | "parked" | "exited">()
  private readonly current: number[] = []
  private readonly handles = new Map<string, Map<object, number>>()
  /** Events appended after `freeze()` are kept apart (a leftover microtask after
   * `runSyncExit`, the interrupt after the deadline). */
  private frozen = false
  readonly late: string[] = []
  readonly exits = new Map<number, unknown>()

  private push(list: string[], row: string): void {
    if (this.frozen) this.late.push(row)
    else list.push(row)
  }
  freeze(): void { this.frozen = true }

  currentFiber(): number { return this.current[this.current.length - 1] ?? -1 }

  /** A handle's index by kind, first-seen order (the Lean face's allocation index). */
  handle(kind: string, value: object): number {
    let table = this.handles.get(kind)
    if (table === undefined) { table = new Map(); this.handles.set(kind, table) }
    const seen = table.get(value)
    if (seen !== undefined) return seen
    const fresh = table.size
    table.set(value, fresh)
    return fresh
  }

  /** A fiber's index, minting one (and its exit observer) on first sight. */
  see(fiber: FiberLike): number {
    const seen = this.index.get(fiber)
    if (seen !== undefined) return seen
    const idx = this.index.size
    this.index.set(fiber, idx)
    this.state.set(idx, "fresh")
    fiber.addObserver((exit) => {
      this.exits.set(idx, exit)
      this.state.set(idx, "exited")
      this.push(this.events, `exited ${idx} ${JSON.stringify(this.exitJson(exit))}`)
      this.push(this.schedule, `exited ${idx} ${exitKindOf(this.exitJson(exit))}`)
    })
    return idx
  }

  /** New children of `fiber` (insertion order = fork order, `:5279-5281`). */
  scanChildren(fiber: FiberLike, parent: number): void {
    if (fiber._children === undefined) return
    for (const child of fiber._children) {
      if (this.index.has(child)) continue
      const idx = this.see(child)
      this.push(this.events, `forked ${parent}->${idx}`)
      this.push(this.schedule, `forked ${parent} ${idx}`)
    }
  }

  /** The `Tracer.context` hook (`internal/effect.ts:653-655`). */
  context = (primitive: any, fiber: FiberLike): unknown => {
    const idx = this.see(fiber)
    this.scanChildren(fiber, idx)
    const state = this.state.get(idx)
    if (state === "fresh") {
      this.state.set(idx, "running")
      this.push(this.events, `started ${idx}`)
      this.push(this.schedule, `started ${idx}`)
    } else if (state === "parked") {
      this.state.set(idx, "running")
      this.push(this.events, `resumedWith ${idx}`)
      this.push(this.schedule, `resumed ${idx}`)
      this.push(this.events, `started ${idx}`)
      this.push(this.schedule, `started ${idx}`)
    }
    const op = String(primitive[IDENTIFIER] ?? "?")
    this.frames.push(`${idx}:${op}`)
    this.current.push(idx)
    let result: unknown
    try {
      result = primitive[EVALUATE](fiber)
    } finally {
      this.current.pop()
    }
    if (result === YIELD) {
      const yielded = fiber._yielded
      const isExit = typeof yielded === "object" && yielded !== null && EXIT in (yielded as object)
      if (!isExit && this.state.get(idx) === "running") {
        this.state.set(idx, "parked")
        this.push(this.events, `parkedOn ${idx}`)
        this.push(this.schedule, `parked ${idx}`)
      }
    }
    return result
  }

  scheduled(owner: number, priority: number): void {
    this.push(this.events, `scheduledTask owner=${owner} prio=${priority}`)
    this.push(this.schedule, `scheduled ${owner} ${priority}`)
  }
  ran(owner: number): void {
    this.push(this.events, `ranTask owner=${owner}`)
    this.push(this.schedule, `ran ${owner}`)
  }

  // ---- the value wire (NOTES.md §3) --------------------------------------------------
  wire(value: unknown): Json {
    if (value === undefined || value === null) return null
    if (typeof value === "number") {
      if (!Number.isSafeInteger(value)) throw new Error(`not a safe integer: ${value}`)
      return value
    }
    if (typeof value === "boolean" || typeof value === "string") return value
    if (Array.isArray(value)) return value.map((item) => this.wire(item))
    if (typeof value === "object") {
      const record = value as Record<string, unknown>
      if (EXIT in record) return this.exitJson(value)
      if (FIBER in record) return { fiber: this.index.get(value) ?? this.handle("fiber?", value) }
      if (REF in record) return { ref: this.handle("ref", value) }
      if (DEFERRED in record) return { deferred: this.handle("deferred", value) }
      if (SCOPE in record) return { scope: this.handle("scope", value) }
      if (record._tag === "Some") return { some: this.wire(record.value) }
      if (record._tag === "None") return { none: true }
    }
    throw new Error(`no wire form for ${describe(value)}`)
  }

  reasonJson(reason: any): Json {
    switch (reason._tag) {
      case "Fail": return { fail: this.wire(reason.error) }
      case "Die": return { die: Cause.isAsyncFiberError(reason.defect) ? "asyncFiber" : describe(reason.defect) }
      case "Interrupt": {
        const who = reason.fiberId
        if (who === undefined || who === null) return { interrupt: null }
        for (const [fiber, idx] of this.index) if ((fiber as FiberLike).id === who) return { interrupt: idx }
        return { interrupt: `host fiber ${who}` }
      }
      default: return { unknown: String(reason._tag) }
    }
  }

  exitJson(exit: any): Json {
    if (exit._tag === "Success") return { success: this.wire(exit.value) }
    return { failure: { reasons: (exit.cause?.reasons ?? []).map((r: unknown) => this.reasonJson(r)) } }
  }
}

const describe = (value: unknown): string => {
  if (value instanceof Error) return `${value.name}: ${value.message}`
  try { return JSON.stringify(value) ?? String(value) } catch { return String(value) }
}

/** The kind of a wired exit, with the archived tracer's precedence: fail, interrupt, die. */
const exitKindOf = (exit: Json): string => {
  if (exit === null || typeof exit !== "object" || Array.isArray(exit)) return "?"
  if ("success" in exit) return "success"
  const reasons = ((exit.failure as any)?.reasons ?? []) as Array<Record<string, Json>>
  if (reasons.some((r) => "fail" in r)) return "fail"
  if (reasons.some((r) => "interrupt" in r)) return "interrupt"
  if (reasons.some((r) => "die" in r)) return "die"
  return "empty"
}

// ---- the scheduler of the async entry -------------------------------------------------
class TracedScheduler extends Scheduler.MixedScheduler {
  constructor(private readonly recorder: Recorder) { super("async") }
  override makeDispatcher(): Scheduler.SchedulerDispatcher {
    const inner = super.makeDispatcher()
    const owner = this.recorder.currentFiber()
    const recorder = this.recorder
    return {
      scheduleTask(task, priority) {
        recorder.scheduled(owner, priority)
        inner.scheduleTask(() => { recorder.ran(owner); task() }, priority)
      },
      flush() { inner.flush() }
    }
  }
}

const tracedContext = (recorder: Recorder, scheduler?: Scheduler.Scheduler) => {
  const base = Tracer.Tracer.defaultValue()
  const tracer = Tracer.make({ ...base, context: recorder.context as any })
  let context = Context.add(Context.empty(), Tracer.Tracer, tracer)
  if (scheduler !== undefined) context = Context.add(context, Scheduler.Scheduler, scheduler)
  return context
}

const sleep = (ms: number) => new Promise<void>((resolve) => setTimeout(resolve, ms))

// ---- the two entries ------------------------------------------------------------------
interface Observation {
  entry: "runSyncExit" | "runPromiseExit"
  exit: Json | null
  parked: boolean
  schedule: string[]
  events: string[]
  frames: string[]
  late: string[]
  /** `runSyncExit` only: the root's exit if it settled later on the microtask queue. */
  settledLater: Json | null
}

const runSyncEntry = async (main: any): Promise<Observation> => {
  const recorder = new Recorder()
  // `Effect.runSyncExitWith(context)` = `runSyncExitWith` (`internal/effect.ts:5536-5545`):
  // its own `MixedScheduler("sync")`, `runFork`, one flush of the root's dispatcher, then
  // the exit or the `AsyncFiberError` defect.
  const exit = Effect.runSyncExitWith(tracedContext(recorder))(main)
  const wired = recorder.exitJson(exit)
  recorder.freeze()
  await sleep(20)
  const root = [...recorder.index.entries()].find(([, idx]) => idx === 0)?.[0] as FiberLike | undefined
  const rootExit = root !== undefined && recorder.exits.has(0) ? recorder.exitJson(recorder.exits.get(0)) : null
  const settledLater = exitKindOf(wired) === "die" && (wired as any).failure.reasons.some((r: any) => r.die === "asyncFiber")
    ? rootExit
    : null
  return {
    entry: "runSyncExit", exit: wired, parked: false, schedule: recorder.schedule, events: recorder.events,
    frames: recorder.frames, late: recorder.late, settledLater
  }
}

const runPromiseEntry = async (main: any): Promise<Observation> => {
  const recorder = new Recorder()
  const scheduler = new TracedScheduler(recorder)
  // `runPromiseExitWith` (`internal/effect.ts:5494-5505`) is `runForkWith(context)` plus one
  // observer; spelled out here so the deadline can interrupt the leftover fiber (`:574`).
  const fiber = Effect.runForkWith(tracedContext(recorder, scheduler))(main) as unknown as FiberLike
  const settled = new Promise<unknown>((resolve) => fiber.addObserver(resolve))
  const deadline = Symbol("deadline")
  const first = await Promise.race([settled, sleep(timeoutMs).then(() => deadline)])
  recorder.freeze()
  if (first === deadline) {
    fiber.interruptUnsafe()
    await settled
    return {
      entry: "runPromiseExit", exit: null, parked: true, schedule: recorder.schedule, events: recorder.events,
      frames: recorder.frames, late: recorder.late, settledLater: null
    }
  }
  return {
    entry: "runPromiseExit", exit: recorder.exitJson(first), parked: false, schedule: recorder.schedule,
    events: recorder.events, frames: recorder.frames, late: recorder.late, settledLater: null
  }
}

// ---- comparison -----------------------------------------------------------------------
const deepEqual = (a: Json, b: Json): boolean => JSON.stringify(a) === JSON.stringify(b)

const failPayloads = (exit: Json): Json[] =>
  (((exit as any)?.failure?.reasons ?? []) as Array<Record<string, Json>>).filter((r) => "fail" in r).map((r) => r.fail)

/** The Lean verdict of `Api.run`: an exit, a park (frontier with the root parked), or a
 * frontier with the root live and unparked — the compile stopped (`acquireRelease`,
 * `RowKind.program`, or no fuel), which rc.112 can never reproduce. */
const leanVerdict = (run: LeanRun): { kind: string; exit: Json | null; text: string } => {
  if (run.exit !== null) return { kind: exitKindOf(run.exit), exit: run.exit, text: renderExit(run.exit) }
  const root = run.fibers.find((f) => f.id === 0)
  if (root !== undefined && root.parkedToken !== null) return { kind: "parked", exit: null, text: "parked (frontier, root parked)" }
  return { kind: "frontier", exit: null, text: `frontier (${run.outcome}, root live, not parked)` }
}

const renderExit = (exit: Json | null): string => {
  if (exit === null) return "—"
  const kind = exitKindOf(exit)
  if (kind === "success") return `success ${JSON.stringify((exit as any).success)}`
  const reasons = ((exit as any).failure?.reasons ?? []) as Array<Record<string, Json>>
  return `${kind} ${JSON.stringify(reasons)}`
}

interface Comparison { agree: boolean; note: string }

const compareExits = (lean: { kind: string; exit: Json | null }, host: Observation): Comparison => {
  if (lean.kind === "parked") {
    return host.parked
      ? { agree: true, note: `both park (deadline ${timeoutMs} ms on rc.112)` }
      : { agree: false, note: "Lean parks, rc.112 settles" }
  }
  if (lean.kind === "frontier") return { agree: false, note: "Lean has no verdict (compile frontier); rc.112 settles" }
  if (host.parked) return { agree: false, note: "rc.112 parks, Lean settles" }
  const hostKind = exitKindOf(host.exit!)
  if (hostKind !== lean.kind) return { agree: false, note: `kind: Lean ${lean.kind}, rc.112 ${hostKind}` }
  if (lean.kind === "success") {
    const same = deepEqual((lean.exit as any).success, (host.exit as any).success)
    return { agree: same, note: same ? "same value" : "same kind, values differ" }
  }
  if (lean.kind === "fail") {
    const same = deepEqual(failPayloads(lean.exit!), failPayloads(host.exit!))
    return { agree: same, note: same ? "same fail payloads" : "same kind, fail payloads differ" }
  }
  return { agree: true, note: `same kind (${lean.kind}); payloads compared by eye` }
}

const isScheduledRow = (row: string) => row.startsWith("scheduled ")

const compareSchedules = (lean: string[], host: string[]): Comparison => {
  const l = lean.filter((r) => !isScheduledRow(r))
  const h = host.filter((r) => !isScheduledRow(r))
  if (l.length === h.length && l.every((row, i) => row === h[i])) return { agree: true, note: `${l.length} rows` }
  const at = l.findIndex((row, i) => row !== h[i])
  const where = at < 0 ? l.length : at
  return { agree: false, note: `differ at row ${where}: Lean ${JSON.stringify(l[where] ?? "∅")}, rc.112 ${JSON.stringify(h[where] ?? "∅")}` }
}

// ---- main ---------------------------------------------------------------------------
interface Row {
  program: string
  leanExit: string
  hostExit: string
  entry: string
  exitAgree: boolean | null
  scheduleAgree: boolean | null
  runSyncAgree: boolean | null
  notes: string[]
  host: Observation | null
  hostSync: Observation | null
}

const main = async (): Promise<number> => {
  const failures = selfTest()
  if (failures.length > 0) {
    console.error("prelude self-test failed:\n  " + failures.join("\n  "))
    return 2
  }
  const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8")) as Manifest
  if (manifest.format !== "effect4-truth-manifest-v1") {
    console.error(`unexpected manifest format ${manifest.format}`)
    return 2
  }
  const generatedDir = path.join(outDir, "generated")
  fs.mkdirSync(generatedDir, { recursive: true })
  const rows: Row[] = []

  for (const entry of manifest.programs) {
    const notes: string[] = []
    const module = moduleFor(entry)
    if (module === null) {
      rows.push({
        program: entry.name, leanExit: leanVerdict(entry.run).text, hostExit: "not run",
        entry: "—", exitAgree: null, scheduleAgree: null, runSyncAgree: null,
        notes: [`printer refused: ${entry.exprRefusal}`], host: null, hostSync: null
      })
      continue
    }
    if (module.source === "expr") notes.push("ill-typed in Lean (`printDecl` = none); ran the `print` expression")
    const file = path.join(generatedDir, `${entry.name}.ts`)
    fs.writeFileSync(file, module.text)
    let loaded: any
    try {
      loaded = await import(pathToFileURL(file).href)
    } catch (error) {
      rows.push({
        program: entry.name, leanExit: leanVerdict(entry.run).text, hostExit: `module failed to load: ${describe(error)}`,
        entry: "—", exitAgree: false, scheduleAgree: null, runSyncAgree: null, notes, host: null, hostSync: null
      })
      continue
    }
    const program = loaded.main

    // The sync entry always, for the `runSync` column.
    const hostSync = await runSyncEntry(program)
    const leanSyncKind = entry.runSync.exitKind
    const hostSyncKind = exitKindOf(hostSync.exit!)
    let runSyncAgree = leanSyncKind === hostSyncKind
    if (runSyncAgree && leanSyncKind === "success") runSyncAgree = deepEqual((entry.runSync.exit as any).success, (hostSync.exit as any).success)
    if (runSyncAgree && leanSyncKind === "die") {
      const leanAsync = JSON.stringify(entry.runSync.exit).includes("\"asyncFiber\"")
      const hostAsync = JSON.stringify(hostSync.exit).includes("\"asyncFiber\"")
      runSyncAgree = leanAsync === hostAsync
    }
    if (hostSync.settledLater !== null) notes.push(`runSyncExit: AsyncFiberError, then the fiber settled on the microtask queue: ${renderExit(hostSync.settledLater)}`)

    if (hostSync.schedule.length === 0) notes.push("runSyncExit created no fiber: a bare Exit is returned as is (`effectIsExit`, internal/effect.ts:5539)")

    // The fork entry always: `Api.run` is `runFork` (Fibers.lean:339-340, `RunDecision.evaluate`)
    // plus the event loop's flush rounds, so its schedule is compared with this observation.
    const hostFork = await runPromiseEntry(program)
    // The verdict entry for the exit column: the one the Lean verdict names.
    const lean = leanVerdict(entry.run)
    const host = entry.runSync.sync ? hostSync : hostFork
    const exits = compareExits(lean, host)
    notes.push(exits.note)
    if (host !== hostFork) {
      const forkExits = compareExits(lean, hostFork)
      if (!forkExits.agree) notes.push(`runFork entry disagrees too: ${forkExits.note}`)
      else if (!deepEqual(host.exit, hostFork.exit)) notes.push(`runSyncExit and runFork exits differ: ${renderExit(hostFork.exit)}`)
    }
    const schedule = compareSchedules(entry.run.schedule, hostFork.schedule)
    if (!schedule.agree) notes.push(`schedule ${schedule.note}`)
    if (hostFork.parked) notes.push("rc.112: no exit before the deadline; the fiber was then interrupted")
    rows.push({
      program: entry.name, leanExit: lean.text, hostExit: host.parked ? "parked (deadline)" : renderExit(host.exit),
      entry: host.entry, exitAgree: exits.agree, scheduleAgree: schedule.agree, runSyncAgree, notes, host: hostFork, hostSync
    })
  }

  const mark = (b: boolean | null) => (b === null ? "n/a" : b ? "yes" : "NO")
  const table = [
    "| program | Lean exit | rc.112 exit | agree | schedule agree | runSyncExit agree | entry | notes |",
    "|---|---|---|---|---|---|---|---|",
    ...rows.map((r) =>
      `| ${r.program} | ${r.leanExit} | ${r.hostExit} | ${mark(r.exitAgree)} | ${mark(r.scheduleAgree)} | ${mark(r.runSyncAgree)} | ${r.entry} | ${r.notes.join("; ").replace(/\|/g, "\\|")} |`)
  ].join("\n")
  console.log(table)

  const disagreements = rows.filter((r) => r.exitAgree === false || r.scheduleAgree === false)
  const summary = disagreements.length === 0
    ? `PASS: ${rows.length} programs, exits and schedules agree with rc.112`
    : `FAIL: ${disagreements.length} of ${rows.length} programs disagree with rc.112 (${disagreements.map((r) => r.program).join(", ")})`
  console.log(summary)

  const result = {
    format: "effect4-truth-result-v1",
    generated: "GENERATED by harness/truth/run-truth.ts — do not edit",
    manifest: manifestPath,
    effect: JSON.parse(fs.readFileSync(path.join(here, "node_modules", "effect", "package.json"), "utf8")).version,
    bun: typeof Bun !== "undefined" ? Bun.version : null,
    timeoutMs,
    summary,
    rows: rows.map((r) => ({
      ...r,
      host: r.host && { ...r.host },
      hostSync: r.hostSync && { ...r.hostSync }
    }))
  }
  fs.writeFileSync(path.join(outDir, "result.json"), JSON.stringify(result, null, 2) + "\n")
  fs.writeFileSync(path.join(outDir, "result.md"),
    `<!-- GENERATED by harness/truth/run-truth.ts — do not edit. Regenerate: harness/truth/check-truth.ps1 -->\n\n` +
    `effect ${result.effect}, bun ${result.bun}, deadline ${timeoutMs} ms\n\n${table}\n\n${summary}\n`)
  return disagreements.length === 0 ? 0 : 1
}

process.exitCode = await main()
