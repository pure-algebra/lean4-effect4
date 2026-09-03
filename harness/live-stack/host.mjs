// Finite source observations for E4-RUN-CE-024, not a Lean/JavaScript simulation.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { createHash } from "node:crypto"
import fs from "node:fs"
import path from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..")
const modules = fs.realpathSync(process.env.EFFECT4_EFFECT_NODE_MODULES ?? path.join(root, "node_modules"))
const effectRoot = path.join(modules, "effect")
const workRoot = path.join(root, ".lake/live-stack/host")
fs.mkdirSync(workRoot, { recursive: true })
const work = fs.mkdtempSync(path.join(workRoot, "run-"))
const sha = (bytes) => createHash("sha256").update(bytes).digest("hex")
const fileSha = (file) => sha(fs.readFileSync(file))
const readJson = (file) => JSON.parse(fs.readFileSync(file, "utf8"))
const pinFile = path.join(root, "harness/fiber-supervision/host-pin.json")
const pin = readJson(pinFile)
const logs = []
const report = { schema: "effect4-live-stack-host-v1", startedAt: new Date().toISOString(), work, commands: logs }

function command(name, executable, args, cwd = work, expectSuccess = true) {
  const result = spawnSync(executable, args, { cwd, encoding: "utf8", timeout: 60000, maxBuffer: 16 * 1024 * 1024 })
  const record = { name, executable, args, cwd, status: result.status, signal: result.signal,
    stdout: result.stdout ?? "", stderr: result.stderr ?? "", error: result.error?.message ?? null }
  logs.push(record)
  fs.writeFileSync(path.join(work, `${name}.json`), JSON.stringify(record, null, 2) + "\n")
  assert.equal(result.error, undefined, `${name}: child process error`)
  assert.equal(result.signal, null, `${name}: child process signal`)
  if (expectSuccess) assert.equal(result.status, 0, `${name}: ${record.stdout}\n${record.stderr}`)
  return record
}

function packageTree(directory) {
  const files = []
  function visit(relative = "") {
    for (const entry of fs.readdirSync(path.join(directory, relative), { withFileTypes: true })) {
      const child = path.join(relative, entry.name)
      assert(!entry.isSymbolicLink(), `unexpected package symlink: ${child}`)
      if (entry.isDirectory()) visit(child)
      else if (entry.isFile()) files.push(child.split(path.sep).join("/"))
      else assert.fail(`unsupported package entry: ${child}`)
    }
  }
  visit()
  assert(files.length > 0, `empty package: ${directory}`)
  files.sort()
  return { fileCount: files.length, sha256: sha(files.map(file => `${file}\0${fileSha(path.join(directory, file))}\n`).join("")) }
}

const platform = `${process.platform}-${process.arch}`
const compilerPackage = path.join(modules, "@typescript", `typescript-${platform}`)
const diagnosticPackage = path.join(modules, "@effect", `tsgo-${platform}`)
const compiler = path.join(compilerPackage, "lib", process.platform === "win32" ? "tsc.original.exe" : "tsc.original")
const diagnostic = path.join(diagnosticPackage, "artifacts/typescript", pin.typescriptVersion, process.platform === "win32" ? "tsc.exe" : "tsc")
const diagnosticCLI = path.join(modules, "@effect/tsgo/dist/effect-tsgo.cjs")

function identities() {
  const effect = packageTree(effectRoot)
  assert.equal(readJson(path.join(effectRoot, "package.json")).version, pin.effectVersion)
  assert.equal(effect.fileCount, pin.effectFileCount)
  assert.equal(effect.sha256, pin.effectTreeSha256)
  for (const name of ["typescript", `@typescript/typescript-${platform}`]) {
    assert.equal(readJson(path.join(modules, name, "package.json")).version, pin.typescriptVersion)
  }
  for (const name of ["@effect/tsgo", `@effect/tsgo-${platform}`]) {
    assert.equal(readJson(path.join(modules, name, "package.json")).version, pin.diagnosticVersion)
  }
  const source = {}
  for (const name of ["effect", "core"]) {
    const relative = `src/internal/${name}.ts`
    const installed = fs.readFileSync(path.join(effectRoot, relative))
    assert.deepEqual(installed, fs.readFileSync(path.join(root, "vendor", `effect-${pin.effectVersion}`, relative)))
    source[relative] = sha(installed)
    source[`dist/internal/${name}.js`] = fileSha(path.join(effectRoot, `dist/internal/${name}.js`))
  }
  return { pin: { sha256: fileSha(pinFile), ...pin }, effect, source,
    tools: { compiler: fileSha(compiler), diagnostic: fileSha(diagnostic), diagnosticCLI: fileSha(diagnosticCLI),
      node: fileSha(process.execPath), compilerPackage: packageTree(compilerPackage),
      typescriptPackage: packageTree(path.join(modules, "typescript")),
      diagnosticPackage: packageTree(diagnosticPackage), diagnosticWrapper: packageTree(path.join(modules, "@effect/tsgo")) },
    harness: Object.fromEntries(["public.ts", "host.mjs"].map(name => [name, fileSha(path.join(root, "harness/live-stack", name))])) }
}

// Deliberately wrong extension: search ignores frames pushed by a hook until
// it has selected an answer from the detached original stack.
// This function is compiled in an isolated module before the unchanged detector runs.
function delayedPush(fiber, slots, original) {
  return function(symbol) {
    if (this._deferredInterrupt) return original.call(this, symbol)
    const detached = this._stack.splice(0)
    while (detached.length > 0) {
      const frame = detached.pop()
      const replacement = frame[slots.contAll]?.(this)
      if (replacement) {
        replacement[symbol] = replacement
        this._stack.unshift(...detached)
        return replacement
      }
      if (frame[symbol]) {
        this._stack.unshift(...detached)
        return frame
      }
    }
    return undefined
  }.bind(fiber)
}

function scheduler() {
  const queue = []
  const choices = []
  let ordinal = 0
  const flush = () => {
    let steps = 0
    while (queue.length > 0) {
      assert(++steps <= 10000, "scheduler did not quiesce")
      queue.sort((a, b) => a.priority - b.priority || a.ordinal - b.ordinal)
      const next = queue.shift()
      choices.push({ action: "run", priority: next.priority, ordinal: next.ordinal })
      next.task()
    }
  }
  return { executionMode: "sync", choices, queue,
    shouldYield() { choices.push({ action: "yield", answer: false }); return false },
    makeDispatcher() {
      return { flush, scheduleTask(task, priority) {
        choices.push({ action: "schedule", priority, ordinal })
        queue.push({ task, priority, ordinal: ordinal++ })
      } }
    }, flush }
}

function causeView(cause) {
  if (cause === undefined) return null
  assert(Array.isArray(cause.reasons), "missing ordered cause reasons")
  return cause.reasons.map(reason => {
    assert(reason.annotations instanceof Map, "missing ordered annotations")
    const annotations = [...reason.annotations.entries()]
    assert.equal(annotations.length, 0, "fixture unexpectedly acquired annotations outside its observation profile")
    switch (reason._tag) {
      case "Interrupt": return { tag: "Interrupt", fiberId: reason.fiberId ?? null, annotations }
      case "Fail": return { tag: "Fail", error: reason.error, annotations }
      case "Die": return { tag: "Die", defect: String(reason.defect), annotations }
      default: assert.fail(`unknown cause reason ${reason._tag}`)
    }
  })
}

const interrupt = [{ tag: "Interrupt", fiberId: 17, annotations: [] }]
const bodyFailure = [{ tag: "Fail", error: "body", annotations: [] }]
function exitView(exit) {
  if (exit === undefined) return { tag: "Pending" }
  if (exit._tag === "Success") return { tag: "Success", value: exit.value ?? null }
  assert.equal(exit._tag, "Failure")
  return { tag: "Failure", cause: causeView(exit.cause) }
}

async function main() {
  report.before = identities()
  report.host = { node: process.version, executable: process.execPath, platform: process.platform, arch: process.arch, modules }
  assert.equal(command("compiler-version", compiler, ["--version"]).stdout.trim(), `Version ${pin.typescriptVersion}`)
  report.diagnosticVersion = command("diagnostic-version", process.execPath, [diagnosticCLI, "--version"]).stdout.trim()
  assert(report.diagnosticVersion.includes(pin.diagnosticVersion), "diagnostic runtime version mismatch")
  assert.equal(command("diagnostic-binary-version", diagnostic, ["--version"]).stdout.trim(),
    `Version ${pin.typescriptVersion}+effect-tsgo.${pin.diagnosticVersion}`)
  const publicSource = fs.readFileSync(path.join(root, "harness/live-stack/public.ts"), "utf8")
  const input = path.join(work, "public.ts")
  fs.writeFileSync(input, publicSource)
  fs.writeFileSync(path.join(work, "package.json"), '{"type":"module"}\n')
  fs.symlinkSync(modules, path.join(work, "node_modules"), "dir")
  const config = { compilerOptions: { target: "ES2022", lib: ["ES2022", "DOM", "ESNext.Disposable"], module: "NodeNext", moduleResolution: "NodeNext", strict: true,
    noEmitOnError: true, skipLibCheck: false, types: [], outDir: "emitted",
    plugins: [{ name: "@effect/language-service" }] }, files: ["public.ts"] }
  fs.writeFileSync(path.join(work, "tsconfig.json"), JSON.stringify(config, null, 2) + "\n")
  const compileArgs = ["-p", path.join(work, "tsconfig.json"), "--pretty", "false"]
  command("type-positive", compiler, compileArgs)
  const discovered = command("type-discovery", compiler, [...compileArgs, "--listFilesOnly"]).stdout.trim().split(/\r?\n/)
  assert(discovered.includes(input), "public program was not analyzed")
  assert(discovered.some(file => file.includes("/effect/dist/Effect.d.ts")), "Effect declarations were not analyzed")
  assert.deepEqual(discovered.filter(file => file.startsWith(work + path.sep)), [input])
  report.types = { filesAnalyzed: discovered.length, localFiles: ["public.ts"], sourceSha256: sha(publicSource), direct: true }
  const emitted = path.join(work, "emitted/public.js")
  const positiveOutput = fileSha(emitted)
  fs.writeFileSync(input, publicSource + '\nconst liveStackTypeErrorControl: number = "wrong"\n')
  const negative = command("type-negative", compiler, compileArgs, work, false)
  assert.notEqual(negative.status, 0, "compiler accepted a wrong assignment")
  const typeErrors = (negative.stdout + negative.stderr).split(/\r?\n/).filter(line => /error TS\d+:/.test(line))
  assert.equal(typeErrors.length, 1, "type control failed outside its one intended diagnostic")
  assert.match(typeErrors[0], /public\.ts.*error TS2322:/)
  assert.equal(fileSha(emitted), positiveOutput, "noEmitOnError overwrote the accepted output")
  fs.writeFileSync(input, publicSource)
  command("type-restored", compiler, compileArgs)
  assert.equal(fileSha(emitted), positiveOutput)
  assert.equal(fs.readFileSync(input, "utf8"), publicSource)
  // The pinned wrapper sends this request after chmod. Invoke its existing
  // executable directly so a read-only gate never changes the installation.
  const diagnosticRequest = { cwd: work, project: path.join(work, "tsconfig.json"), format: "json", strict: true, progress: false, listFiles: true }
  const diagnosticRecord = command("diagnostics", diagnostic, ["--effect-cli-diagnostics", JSON.stringify(diagnosticRequest)])
  const diagnostics = JSON.parse(diagnosticRecord.stdout)
  assert.equal(diagnostics.summary?.errors, 0)
  assert.equal(diagnostics.summary?.warnings, 0)
  assert.equal(diagnostics.summary?.filesChecked, 1)
  assert.equal(diagnostics.files?.length, 1)
  assert(diagnostics.files.every(file => file.detectedEffect === "v4" && file.supportedEffect === "v4"))
  report.types.diagnostics = diagnostics
  report.types.emittedSha256 = fileSha(emitted)
  const candidate = path.join(work, "delayed-push.mjs")
  fs.writeFileSync(candidate, `export default ${delayedPush.toString()}\n`)
  command("candidate-compile", process.execPath, ["--check", candidate])
  const [{ begin }, { default: installCandidate }, core, internal, Cause, Context, Effect] = await Promise.all([
    import(pathToFileURL(emitted).href), import(pathToFileURL(candidate).href),
    ...["internal/core", "internal/effect", "Cause", "Context", "Effect"].map(name => import(pathToFileURL(path.join(effectRoot, `dist/${name}.js`)).href))
  ])
  const prototype = Object.getOwnPropertyDescriptors(internal.FiberImpl.prototype)
  const frameView = frame => ({ op: frame[core.identifier] ?? "replacement", value: typeof frame[core.args] === "boolean" ? frame[core.args] : null,
    arms: [core.contA, core.contE, core.contAll].map(slot => typeof frame[slot] === "function") })
  function snapshot(test, scheduling, stage) {
    return { stage, outcome: exitView(test.fiber.pollUnsafe()), events: [...test.events],
      stack: test.fiber._stack.map(frameView), interruptible: test.fiber.interruptible,
      pending: causeView(test.fiber._interruptedCause), deferred: test.fiber._deferredInterrupt,
      scheduler: { pending: scheduling.queue.length, choices: [...scheduling.choices] } }
  }
  function runPublic(masked, cancellation, ordinaryFinalizer, mutation) {
    const scheduling = scheduler()
    const test = begin(masked, cancellation, scheduling, ordinaryFinalizer)
    assert(!Object.hasOwn(test.fiber, "getCont"), "unexpected pre-existing fiber override")
    const original = test.fiber.getCont
    const prefixes = [snapshot(test, scheduling, "after-start")]
    if (mutation) test.fiber.getCont = installCandidate(test.fiber, core, original)
    let cleaned = false
    try {
      test.replyFirst(); scheduling.flush()
      prefixes.push(snapshot(test, scheduling, "after-first-reply"))
      test.fiber.interruptUnsafe(17); scheduling.flush()
      prefixes.push(snapshot(test, scheduling, "after-interruption"))
      test.replySecond(); scheduling.flush()
      prefixes.push(snapshot(test, scheduling, "after-late-second-reply"))
      assert.notEqual(test.fiber.pollUnsafe(), undefined, "test fiber leaked after late reply")
      assert.equal(scheduling.queue.length, 0)
      cleaned = true
      return { masked, cancellation, ordinaryFinalizer, mutation, decisions: ["no scheduler yields", "reply first with 42", "interrupt by 17", "reply second with 7"], prefixes, completed: true }
    } finally {
      if (mutation) delete test.fiber.getCont
      assert.equal(test.fiber.getCont, original)
      assert.deepEqual(Object.getOwnPropertyDescriptors(internal.FiberImpl.prototype), prototype)
      if (!cleaned) {
        // Restore source behavior before releasing either externally controlled callback.
        test.replyFirst(); test.replySecond(); scheduling.flush()
        assert.notEqual(test.fiber.pollUnsafe(), undefined, "cleanup could not complete test fiber")
      }
    }
  }
  function acceptPublic(run) {
    assert.deepEqual(run.prefixes.map(p => p.stage), ["after-start", "after-first-reply", "after-interruption", "after-late-second-reply"])
    const [start, first, interrupted, late] = run.prefixes
    const events = ["register:first", ...(run.ordinaryFinalizer ? ["finalize:first"] : []), "between:42", "register:second"]
    assert.deepEqual(start.events, ["register:first"])
    assert.deepEqual(start.outcome, { tag: "Pending" })
    assert.deepEqual(first.events, events)
    assert.deepEqual(first.outcome, { tag: "Pending" })
    assert.deepEqual(interrupted.events, events)
    assert.deepEqual(interrupted.outcome, run.masked ? { tag: "Pending" } : { tag: "Failure", cause: interrupt }, "wrong interruption prefix")
    assert.equal(first.interruptible, !run.masked, "wrong mask at second callback")
    assert.deepEqual(late.events, events)
    assert.deepEqual(late.outcome, { tag: "Failure", cause: interrupt })
    assert.equal(late.stack.length, 0)
    for (const prefix of run.prefixes) assert.equal(prefix.scheduler.pending, 0)
    return true
  }
  report.public = []
  for (const ordinaryFinalizer of [false, true]) {
    for (const masked of [false, true]) {
      for (const cancellation of ordinaryFinalizer ? [false] : [false, true]) {
        const before = runPublic(masked, cancellation, ordinaryFinalizer, false)
        assert(acceptPublic(before))
        const wrong = runPublic(masked, cancellation, ordinaryFinalizer, true)
        const discriminates = !ordinaryFinalizer && !masked && cancellation
        let rejection = null
        if (discriminates) {
          assert.deepEqual(wrong.prefixes[2].outcome, { tag: "Pending" })
          assert.notDeepEqual(wrong.prefixes[2].outcome, before.prefixes[2].outcome)
          assert.deepEqual(wrong.prefixes[3].outcome, before.prefixes[3].outcome, "eventual exits must coincide in this witness")
          try { acceptPublic(wrong) } catch (error) { rejection = error.message }
          assert(rejection, "unchanged detector accepted the delayed-push candidate")
          assert.match(rejection, /^wrong interruption prefix/, "candidate failed outside the intended detector")
        } else {
          assert(acceptPublic(wrong))
          assert.deepEqual(wrong.prefixes, before.prefixes, "control changed under the isolated candidate")
        }
        const restored = runPublic(masked, cancellation, ordinaryFinalizer, false)
        assert(acceptPublic(restored))
        assert.deepEqual(restored.prefixes, before.prefixes)
        report.public.push({ before, wrong, rejection, restored })
      }
    }
  }
  assert.equal(report.public.length, 6)
  assert.equal(report.public.filter(item => item.rejection !== null).length, 1)
  report.afterPublicMutation = identities()
  assert.deepEqual(report.afterPublicMutation, report.before)

  report.constructedDeferred = []
  for (const masked of [true, false]) {
    const fiber = new internal.FiberImpl(Context.empty(), !masked)
    const handlerEvents = []
    const handler = Effect.catchCause(Effect.fail("body"), () => { handlerEvents.push("handler-ran"); return Effect.succeed("caught") })
    fiber._stack.push(handler)
    fiber._interruptedCause = Cause.interrupt(17)
    fiber._deferredInterrupt = true
    const calls = []
    const original = fiber.getCont
    fiber.getCont = function(slot) {
      assert.equal(slot, core.contE)
      const before = { deferred: this._deferredInterrupt, interruptible: this.interruptible, pending: causeView(this._interruptedCause), stack: this._stack.map(frameView) }
      const answer = original.call(this, slot)
      const selected = answer === undefined ? "empty" : answer === handler ? "handler" : before.deferred ? "deferred" : "unexpected"
      calls.push({ before, selected, after: { deferred: this._deferredInterrupt, interruptible: this.interruptible,
        pending: causeView(this._interruptedCause), stack: this._stack.map(frameView) } })
      return answer
    }
    const returned = core.exitFailCause(Cause.fail("body"))[core.evaluate](fiber)
    const observed = { masked, reachability: "constructed internal state; public-program reachability not established", calls, handlerEvents,
      returned: returned === core.Yield ? { tag: "Yield" } : exitView(returned), yielded: exitView(fiber._yielded),
      remaining: fiber._stack.map(frameView), pending: causeView(fiber._interruptedCause), deferred: fiber._deferredInterrupt }
    assert.deepEqual(calls.map(call => call.selected), masked ? ["deferred"] : ["deferred", "handler", "empty"])
    assert.deepEqual(handlerEvents, [])
    assert.equal(observed.deferred, false)
    assert.deepEqual(observed.pending, interrupt)
    assert.equal(observed.remaining.length, masked ? 1 : 0)
    assert.deepEqual(observed.returned, masked ? { tag: "Failure", cause: interrupt } : { tag: "Yield" })
    assert.deepEqual(observed.yielded, masked ? { tag: "Pending" } : { tag: "Failure", cause: bodyFailure })
    delete fiber.getCont
    // These raw fibers never parked a callback. Clear the raw evaluator's yield
    // marker before normal evaluation, which otherwise expects a cancel function.
    fiber._yielded = undefined
    fiber._stack.length = 0
    fiber.evaluate(core.exitSucceed(undefined))
    assert.equal(fiber.pollUnsafe()?._tag, "Success")
    observed.completed = true
    report.constructedDeferred.push(observed)
  }
  assert.deepEqual(Object.getOwnPropertyDescriptors(internal.FiberImpl.prototype), prototype)
  report.after = identities()
  assert.deepEqual(report.after, report.before)
  report.result = { publicConfigurations: 6, publicExecutions: 18, checkpoints: 72, delayedPushRejected: 1,
    positiveAndRestoredControls: 12, candidateControls: 5, constructedDeferredCases: 2,
    allPublicFibersCompleted: true, sourceAndToolsUnchanged: true,
    scope: "finite pinned TypeScript source observations; no universal source relation or Lean-to-JavaScript simulation" }
}

try {
  await main()
  report.finishedAt = new Date().toISOString()
  fs.writeFileSync(path.join(work, "evidence.json"), JSON.stringify(report, null, 2) + "\n")
  process.stdout.write(JSON.stringify(report) + "\n")
} catch (error) {
  report.failure = { message: error.message, stack: error.stack }
  fs.writeFileSync(path.join(work, "evidence.json"), JSON.stringify(report, null, 2) + "\n")
  process.stderr.write(JSON.stringify(report) + "\n")
  process.exitCode = 1
}
