// The rc.112 face of the adversarial corpus. Round five of spike A0.
//
// It parses `corpus/programs.txt` -- the very text `corpus_dsl.ml` parses -- and interprets
// each step as the rc.112 call the avatar's arm transcribes, emitting the same row alphabet
// (`Effects/Trace.lean`, `git:c407ab7:harness/trace/tracer.ts`). Nothing under `harness/` is imported or
// edited; the wire encoding, the first-seen handle counter, the tape and the stall deadline
// are transcribed here so the two faces are independent implementations of one text.
import * as process from "node:process"
import { readFileSync } from "node:fs"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"

const selected = process.env.EFFECT4_EFFECT_NODE_MODULES ?? process.env.EFFECT4_NODE_MODULES ??
  resolve(dirname(fileURLToPath(import.meta.url)), "../../ts/eff/node_modules")
const nm = selected.startsWith("file:") ? fileURLToPath(selected) : selected
if (JSON.parse(readFileSync(join(nm, "effect/package.json"), "utf8")).version !== "4.0.0-rc.112") {
  throw new Error("The corpus requires effect@4.0.0-rc.112")
}
const { Deferred, Effect, Exit, Fiber, Layer, Context, Ref, Scope, Scheduler } =
  await import(pathToFileURL(join(nm, "effect/dist/index.js")).href)

// --------------------------------------------------------------------- the DSL parser
const parseArg = (t) => {
  const one = (x) => {
    const s = x.trim()
    if (s === "") return { k: "lit", n: 0 }
    if (s[0] === "#") return { k: "local", n: Number(s.slice(1)) }
    if (s[0] === "@") return { k: "global", n: Number(s.slice(1)) }
    return { k: "lit", n: Number(s) }
  }
  return t.includes(",") ? { k: "list", xs: t.split(",").map(one) } : one(t)
}
const parseStep = (t0) => {
  let t = t0.trim()
  let publish = null
  if (t[0] === "@" && t.includes("=")) {
    const i = t.indexOf("=")
    publish = Number(t.slice(1, i))
    t = t.slice(i + 1).trim()
  }
  const words = t.split(" ").filter((w) => w !== "")
  return { publish, op: words[0], args: words.slice(1).map(parseArg) }
}
const parseSteps = (t) => t.split(";").map((p) => p.trim()).filter((p) => p !== "").map(parseStep)

const parsePrograms = (text) => {
  const progs = []
  let cur = null
  for (const raw of text.split("\n")) {
    const line = raw.trim()
    if (line === "" || line.startsWith("#")) continue
    if (line.startsWith("prog ")) {
      if (cur) progs.push(cur)
      cur = { name: line.slice(5).trim(), tape: "", maxops: null, notes: [], roots: [], main: [] }
    } else if (!cur) continue
    else if (line.startsWith("tape ")) cur.tape = line.slice(5).trim()
    else if (line.startsWith("maxops ")) cur.maxops = Number(line.slice(7).trim())
    else if (line.startsWith("note ")) cur.notes.push(line.slice(5).trim())
    else if (line.startsWith("root ")) {
      const rest = line.slice(5).trim()
      const i = rest.indexOf(" ")
      cur.roots.push([Number(rest.slice(0, i)), parseSteps(rest.slice(i + 1))])
    } else if (line.startsWith("main ")) cur.main = parseSteps(line.slice(5).trim())
    else throw new Error(`unknown corpus line: ${line}`)
  }
  if (cur) progs.push(cur)
  return progs
}

// ------------------------------------------------------------------------- the wire
const handles = new WeakMap()
let nextHandle = 0
const handleIndex = (o) => {
  const seen = handles.get(o)
  if (seen !== undefined) return seen
  const fresh = nextHandle++
  handles.set(o, fresh)
  return fresh
}
const objOfHandle = new Map()
const remember = (o) => { const h = handleIndex(o); objOfHandle.set(h, o); return h }

const wire = (v) => {
  if (v === undefined || v === null) return "[]"
  if (typeof v === "number") return String(v)
  if (typeof v === "boolean") return v ? "true" : "false"
  if (typeof v === "string") return JSON.stringify(v)
  if (Array.isArray(v)) return v.reduceRight((acc, x) => `[${wire(x)}, ${acc}]`, "[]")
  if (typeof v === "object") {
    if (v.__pair) return `[${wire(v.a)}, ${wire(v.b)}]`
    if (v.__none) return `{"none":true}`
    if (v.__some !== undefined) return `{"some":${wire(v.__some)}}`
    if (handles.has(v)) return String(handleIndex(v))
  }
  return String(v)
}
const pair = (a, b) => ({ __pair: true, a, b })
const none = { __none: true }
const some = (x) => ({ __some: x })

const rows = []
const op = (name, request) => rows.push(`op\t${name}\t${wire(request)}`)
const answer = (name, value) => rows.push(`answer\t${name}\t${wire(value)}`)
const failed = (name, error) => rows.push(`failed\t${name}\t${wire(error)}`)

const outcomeWire = (exit) => {
  if (exit._tag === "Success") return `{"success":${wire(exit.value)}}`
  const reasons = exit.cause?.reasons ?? []
  const fail = reasons.find((r) => r._tag === "Fail")
  if (fail !== undefined) return `{"failure":${wire(fail.error)}}`
  if (reasons.some((r) => r._tag === "Interrupt")) return `{"interrupted":true}`
  const die = reasons.find((r) => r._tag === "Die")
  if (die !== undefined) return `{"defect":${JSON.stringify(String(die.defect))}}`
  throw new Error("no Fail, Die or Interrupt reason")
}

// ------------------------------------------------------------------- the shared stores
const started = []
const cleanups = []
const globals = new Array(64).fill(undefined)

class L0 extends Context.Service()("A0L0") {}
class L1 extends Context.Service()("A0L1") {}
class L2 extends Context.Service()("A0L2") {}
const layerCounts = new Map()
const scopeOfService = new WeakMap()
const layerReleaseLog = []
const construct = (base) =>
  Effect.gen(function* () {
    const layerScope = yield* Effect.scope
    layerCounts.set(base, (layerCounts.get(base) ?? 0) + 1)
    const service = yield* Ref.make(base)
    scopeOfService.set(service, layerScope)
    yield* Scope.addFinalizerExit(layerScope, () =>
      Effect.sync(() => { layerReleaseLog.push(service) }))
    return service
  })
const layer0 = Layer.effect(L0, construct(0))
const layer1 = Layer.effect(L1, construct(1))
const layer2 = Layer.effect(L2, construct(2))
const layer3 = Layer.fresh(layer1)
const declaredLayers = [
  { layer: layer0, tag: L0 }, { layer: layer1, tag: L1 },
  { layer: layer2, tag: L2 }, { layer: layer3, tag: L1 }
]
const memoMap = Layer.makeMemoMapUnsafe()
const layerRoot = Scope.makeUnsafe()

// The scope family's own bookkeeping (`git:c407ab7:harness/trace/scope-tail.ts`).
const scopeRunLog = new WeakMap()
const scopeRegistered = new WeakMap()

// ------------------------------------------------------------------------ the tape
let tapeEntries = []
let cursor = 0
let armed = false
const decide = () => {
  const e = tapeEntries[cursor]
  if (e === undefined) throw new Error(`TAPE_EXHAUSTED at site ${cursor}`)
  if (e[0] !== cursor) throw new Error(`TAPE_SITE_MISMATCH at ${cursor}`)
  cursor += 1
  rows.push(`decide\t${e[0]}\t${e[1] ? "true" : "false"}`)
  return e[1]
}
class TapeScheduler extends Scheduler.MixedScheduler {
  shouldYield(fiber) {
    if (armed) { armed = false; return true }
    return super.shouldYield(fiber)
  }
}

// ----------------------------------------------------------------- ops with no rc.112 surface
const UNSUPPORTED = new Set(["childrenSnapshot", "awaitChildren", "refuse"])

// ------------------------------------------------------------------- the interpreter
const AVATAR_BODIES = {
  0: () => Effect.succeed(11), 1: () => Effect.succeed(22),
  2: () => Effect.fail(1), 3: () => Effect.fail(2), 4: () => Effect.never,
  // Body 6 completes the Deferred at handle 0 with 42, as `fibers_fixture.ml`'s does.
  6: () => Effect.flatMap(
    Effect.suspend(() => {
      const d = objOfHandle.get(0)
      op("succeed", pair(0, 42))
      return Effect.tap(Deferred.succeed(d, 42), (ok) => Effect.sync(() => answer("succeed", ok)))
    }), () => Effect.succeed(0))
}

const toTree = (steps) => {
  const out = []
  let i = 0
  const walk = (stop) => {
    const block = []
    while (i < steps.length) {
      const st = steps[i]
      if (st.op === "unmask") { if (stop) { i += 1; return block } }
      if (st.op === "mask") { const at = i; i += 1; block.push({ kind: "mask", at, body: walk(true) }); continue }
      block.push({ kind: "step", at: i, st }); i += 1
    }
    return block
  }
  const r = walk(false)
  return r.length ? r : out
}

const makeBody = (prog, code) => {
  const declared = prog.roots.find(([c]) => c === code)
  const core = declared === undefined
    ? (AVATAR_BODIES[code] ?? (() => Effect.never))()
    : Effect.suspend(() => runBlock(toTree(declared[1]), new Array(declared[1].length + 1)))
  return Effect.onExit(
    Effect.flatMap(Effect.sync(() => { started.push(code) }), () => core),
    () => Effect.sync(() => { cleanups.push(code) }))
}

let CURRENT = null

const vof = (slots, a) => {
  if (a.k === "lit") return a.n
  if (a.k === "local") return slots[a.n]
  if (a.k === "global") return globals[a.n]
  return a.xs.map((x) => vof(slots, x))
}
const iof = (slots, a) => { const v = vof(slots, a); return typeof v === "number" ? v : handleIndex(v) }
const objof = (slots, a) => {
  const v = vof(slots, a)
  return typeof v === "number" ? objOfHandle.get(v) : v
}
const listof = (slots, a) => {
  const v = vof(slots, a)
  return (Array.isArray(v) ? v : [v]).map((x) => (typeof x === "number" ? objOfHandle.get(x) : x))
}
const intsof = (slots, a) => {
  const v = vof(slots, a)
  return (Array.isArray(v) ? v : v === undefined ? [] : [v]).map((x) => Number(x))
}

const runStep = (st, slots) =>
  Effect.gen(function* () {
    const a = (i) => st.args[i]
    const o = st.op
    let value
    switch (o) {
      case "fork":
      case "forkDetach": {
        const code = iof(slots, a(0))
        op(o === "fork" ? "fork" : "forkDetach", code)
        const body = makeBody(CURRENT, code)
        const fiber = o === "fork"
          ? yield* Effect.forkChild(body, { startImmediately: false })
          : yield* Effect.forkDetach(body, { startImmediately: false })
        const branch = decide()
        const h = remember(fiber)
        answer(o === "fork" ? "fork" : "forkDetach", h)
        if (branch) { armed = true; yield* Effect.sync(() => {}) }
        value = fiber
        break
      }
      case "join": {
        const f = objof(slots, a(0)); op("join", handleIndex(f))
        value = yield* Effect.tapError(Effect.tap(Fiber.join(f), (v) => Effect.sync(() => answer("join", v))),
          (e) => Effect.sync(() => failed("join", e)))
        break
      }
      case "awaitValue": case "awaitError": {
        const f = objof(slots, a(0)); op(o, handleIndex(f))
        const exit = yield* Fiber.await(f)
        if (o === "awaitValue") value = exit._tag === "Success" ? some(exit.value) : none
        else {
          const reasons = exit._tag === "Success" ? [] : (exit.cause?.reasons ?? [])
          const fail = reasons.find((r) => r._tag === "Fail")
          value = fail === undefined ? none : some(fail.error)
        }
        answer(o, value)
        break
      }
      case "interrupt": {
        const f = objof(slots, a(0)); op("interrupt", handleIndex(f))
        yield* Fiber.interrupt(f); answer("interrupt", undefined); value = undefined
        break
      }
      case "interruptAll": {
        const fs = listof(slots, a(0)); op("interruptAll", fs.map(handleIndex))
        yield* Fiber.interruptAll(fs); answer("interruptAll", undefined); value = undefined
        break
      }
      case "awaitAll": {
        const fs = listof(slots, a(0)); op("awaitAll", fs.map(handleIndex))
        const exits = yield* Fiber.awaitAll(fs)
        value = exits.map((e) => (Exit.isSuccess(e) ? e.value : none))
        answer("awaitAll", value)
        break
      }
      case "raceAll": {
        const codes = st.args.length === 0 ? [] : intsof(slots, a(0)); op("raceAll", codes)
        const entrants = codes.map((c) => makeBody(CURRENT, c))
        value = yield* Effect.tapError(
          Effect.tap(entrants.length === 0 ? Effect.never : Effect.raceAll(entrants),
            (v) => Effect.sync(() => answer("raceAll", v))),
          (e) => Effect.sync(() => failed("raceAll", e)))
        break
      }
      case "yield": op("yield", undefined); yield* Effect.yieldNow; answer("yield", undefined); value = undefined; break
      case "never": yield* Effect.never; value = undefined; break
      case "started": op("started", undefined); value = started.slice(); answer("started", value); break
      case "cleanups": op("cleanups", undefined); value = cleanups.slice(); answer("cleanups", value); break
      case "refMake": { const n = iof(slots, a(0)); op("make", n); const r = yield* Ref.make(n); value = r; answer("make", remember(r)); break }
      case "refGet": { const r = objof(slots, a(0)); op("get", handleIndex(r)); value = yield* Ref.get(r); answer("get", value); break }
      case "refSet": { const r = objof(slots, a(0)); const n = iof(slots, a(1)); op("set", pair(handleIndex(r), n)); yield* Ref.set(r, n); value = undefined; answer("set", undefined); break }
      case "refUpdate": { const r = objof(slots, a(0)); const n = iof(slots, a(1)); op("update", pair(handleIndex(r), n)); yield* Ref.update(r, (c) => c + n); value = undefined; answer("update", undefined); break }
      case "refModify": { const r = objof(slots, a(0)); const n = iof(slots, a(1)); op("modify", pair(handleIndex(r), n)); value = yield* Ref.modify(r, (c) => [c, c + n]); answer("modify", value); break }
      case "refGetAndSet": { const r = objof(slots, a(0)); const n = iof(slots, a(1)); op("getAndSet", pair(handleIndex(r), n)); value = yield* Ref.getAndSet(r, n); answer("getAndSet", value); break }
      case "refTryTake": {
        const r = objof(slots, a(0)); const n = iof(slots, a(1)); op("tryTake", pair(handleIndex(r), n))
        value = yield* Ref.modify(r, (c) => (c >= n ? [pair(true, c - n), c - n] : [pair(false, "underflow"), c]))
        answer("tryTake", value); break
      }
      case "defMake": { op("make", undefined); const d = yield* Deferred.make(); value = d; answer("make", remember(d)); break }
      case "defSucceed": { const d = objof(slots, a(0)); const n = iof(slots, a(1)); op("succeed", pair(handleIndex(d), n)); value = yield* Deferred.succeed(d, n); answer("succeed", value); break }
      case "defFail": { const d = objof(slots, a(0)); const n = iof(slots, a(1)); op("fail", pair(handleIndex(d), n)); value = yield* Deferred.fail(d, n); answer("fail", value); break }
      case "defIsDone": { const d = objof(slots, a(0)); op("isDone", handleIndex(d)); value = yield* Deferred.isDone(d); answer("isDone", value); break }
      case "defPoll": {
        const d = objof(slots, a(0)); op("poll", handleIndex(d))
        const p = yield* Deferred.poll(d)
        value = p._tag === "None" ? none
          : some(p.value._tag === "Success" ? pair(true, p.value.value) : pair(false, (p.value.cause?.reasons ?? []).find((r) => r._tag === "Fail")?.error))
        answer("poll", value); break
      }
      case "defAwaitValue": case "defAwaitError": {
        const d = objof(slots, a(0)); const name = o === "defAwaitValue" ? "awaitValue" : "awaitError"
        op(name, handleIndex(d))
        const e = o === "defAwaitValue" ? Deferred.await(d) : Effect.flip(Deferred.await(d))
        value = yield* Effect.tapError(Effect.tap(e, (v) => Effect.sync(() => answer(name, v))),
          (err) => Effect.sync(() => failed(name, err)))
        break
      }
      case "scopeMake": {
        op("make", undefined)
        const s = Scope.makeUnsafe(); scopeRunLog.set(s, []); scopeRegistered.set(s, new Map())
        value = s; answer("make", remember(s)); break
      }
      case "scopeAdd": {
        const s = objof(slots, a(0)); const key = iof(slots, a(1)); op("addFinalizer", pair(handleIndex(s), key))
        const ran = scopeRunLog.get(s) ?? []; const before = ran.length
        const fin = () => Effect.sync(() => { ran.push(key) })
        scopeRegistered.get(s)?.set(key, fin)
        yield* Scope.addFinalizerExit(s, fin)
        value = ran.length === before; answer("addFinalizer", value); break
      }
      case "scopeRemove": {
        const s = objof(slots, a(0)); const key = iof(slots, a(1)); op("remove", pair(handleIndex(s), key))
        yield* Effect.sync(() => {
          const fin = scopeRegistered.get(s)?.get(key); const state = s.state
          if (fin === undefined || state._tag !== "Open") return
          if (state.finalizer === fin) { state.finalizerKey = undefined; state.finalizer = undefined; return }
          const table = state.finalizers; if (table === undefined) return
          for (const [k, e] of table) if (e === fin) { table.delete(k); return }
        })
        value = undefined; answer("remove", undefined); break
      }
      case "scopeClose": {
        const s = objof(slots, a(0)); op("close", handleIndex(s))
        const ran = scopeRunLog.get(s) ?? []; const before = ran.length
        yield* Scope.close(s, Exit.void)
        value = ran.slice(before); answer("close", value); break
      }
      case "layerBuild": {
        const k = iof(slots, a(0)); op("build", k)
        const entry = declaredLayers[k]
        const context = yield* Layer.buildWithMemoMap(entry.layer, memoMap, layerRoot)
        const service = Context.get(context, entry.tag)
        value = service; answer("build", remember(service)); break
      }
      case "layerProvideCount": { const b = iof(slots, a(0)); op("provideCount", b); value = layerCounts.get(b) ?? 0; answer("provideCount", value); break }
      case "layerScopeOf": { const sv = objof(slots, a(0)); op("scopeOf", handleIndex(sv)); const sc = scopeOfService.get(sv); value = sc; answer("scopeOf", remember(sc)); break }
      case "layerClose": {
        op("close", undefined); const before = layerReleaseLog.length
        yield* Scope.close(layerRoot, Exit.void)
        value = layerReleaseLog.slice(before).map(handleIndex); answer("close", value); break
      }
      case "succeed": value = iof(slots, a(0)); break
      case "failWith": yield* Effect.fail(iof(slots, a(0))); value = undefined; break
      case "ret": value = vof(slots, a(0)); break
      default: throw new Error(`unknown corpus op ${o}`)
    }
    slots[st.__at] = value
    if (st.publish !== null) globals[st.publish] = value
    return value
  })

const runBlock = (tree, slots) =>
  Effect.gen(function* () {
    let last
    for (const node of tree) {
      if (node.kind === "mask") {
        last = yield* Effect.uninterruptible(runBlock(node.body, slots))
      } else {
        node.st.__at = node.at
        last = yield* runStep(node.st, slots)
      }
    }
    return last
  })

// -------------------------------------------------------------------------- the run
const text = readFileSync(process.env.EFFECT4_CORPUS ?? "corpus/programs.txt", "utf8")
const programs = parsePrograms(text)
const name = process.env.EFFECT4_PROGRAM
const prog = programs.find((p) => p.name === name)
if (prog === undefined) { process.stderr.write(`unknown corpus program ${name}\n`); process.exit(2) }
const used = new Set()
const collect = (steps) => steps.forEach((s) => used.add(s.op))
collect(prog.main); prog.roots.forEach(([, s]) => collect(s))
for (const u of used) if (UNSUPPORTED.has(u)) {
  process.stderr.write(`no rc.112 surface for ${u} in ${name}\n`); process.exit(2)
}
CURRENT = prog
tapeEntries = (prog.tape === "" ? Array.from({ length: 32 }, (_, i) => `${i}:0`) : prog.tape.split(","))
  .filter((e) => e.length > 0).map((e) => { const [s, b] = e.split(":"); return [Number(s), b === "1"] })

const main = Effect.suspend(() => runBlock(toTree(prog.main), new Array(prog.main.length + 1))).pipe(
  Effect.provideService(Scheduler.MaxOpsBeforeYield, prog.maxops ?? 1000000))
const fiber = Effect.runFork(main, { scheduler: new TapeScheduler() })
const settled = new Promise((resolve) => fiber.addObserver(resolve))
const stalled = Symbol("stalled")
const deadline = new Promise((resolve) => setTimeout(() => resolve(stalled), Number(process.env.EFFECT4_STALL_MS ?? "300")))
const first = await Promise.race([settled, deadline])
if (first === stalled) rows.push("frontier")
else rows.push(`done\t${outcomeWire(first)}`)

console.log("format\teffect4-trace-v1")
console.log("face\trc112")
console.log(`program\tcorpus.${name}`)
console.log(`tape\t${prog.tape}`)
for (const r of rows) console.log(r)
