import assert from "node:assert/strict"
import { createHash } from "node:crypto"
import { mkdir, readFile, writeFile } from "node:fs/promises"
import path from "node:path"
import { spawnSync } from "node:child_process"
import { fileURLToPath } from "node:url"

const defaultRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..")
const expected = [
  "popLive", "getContLive", "popLive_eq_popFrom", "getContLive_eq_getCont",
  "getContLive_false_eq_getCont", "getContLive_deferred_kept",
  "getContLive_deferred_discarded", "getContLive_while"
].map(name => `Effect4.FrameFiber.${name}`).sort()
const digest = bytes => createHash("sha256").update(bytes).digest("hex")

/** A fresh compiled census and proof-erased call-graph check. Full mode always
 * builds its target; controls-only is a separately labeled development check. */
export async function inspectCompiled({ root = defaultRoot, controlsOnly = false } = {}) {
  root = path.resolve(root)
  const output = path.join(root, ".lake/live-stack/inspection")
  await mkdir(output, { recursive: true })
  const sources = [
    ...(!controlsOnly ? ["Effect4/Runtime/LiveStack.lean"] : []),
    "Effect4/Runtime/Runtime.lean", "Effect4/Semantics/Cause.lean", "Effect4/Semantics/Exit.lean",
    "Effect4.lean", "Effect4Test.lean",
    "harness/live-stack/Inspect.lean", "harness/live-stack/inspect.mjs", "lean-toolchain", "lakefile.toml"
  ]
  const before = Object.fromEntries(await Promise.all(sources.map(async name => [name, digest(await readFile(path.join(root, name)))])))
  const env = { ...process.env }
  delete env.EFFECT4_LIVE_STACK_INSPECT_CONTROLS_ONLY
  if (controlsOnly) env.EFFECT4_LIVE_STACK_INSPECT_CONTROLS_ONLY = "1"
  const commands = []
  async function run(args, label, input) {
    const started = Date.now()
    const result = spawnSync("lake", args, {
      // A concurrent package build can occupy the available cores. The
      // command remains bounded; a timeout is never a successful inspection.
      cwd: root, env, encoding: "utf8", timeout: 300000,
      maxBuffer: 32 * 1024 * 1024, input
    })
    const stdout = result.stdout ?? ""
    const stderr = result.stderr ?? ""
    await writeFile(path.join(output, `${label}.stdout.log`), stdout)
    await writeFile(path.join(output, `${label}.stderr.log`), stderr)
    commands.push({ command: ["lake", ...args], exitCode: result.status, elapsedMs: Date.now() - started, stdoutSha256: digest(stdout), stderrSha256: digest(stderr) })
    assert.ifError(result.error)
    assert.equal(result.status, 0, `Compiled inspection command failed: lake ${args.join(" ")}\n${stdout}\n${stderr}`)
    return stdout
  }
  let stdout
  if (controlsOnly) {
    // The unchanged walker can be developed while the independent production
    // implementation is still red. This does not emit a full-mode receipt.
    const source = await readFile(path.join(root, "harness/live-stack/Inspect.lean"), "utf8")
    const importLine = "import Effect4.Runtime.LiveStack\n"
    assert.equal(source.split(importLine).length, 2, "Expected exactly one target import")
    stdout = await run(["env", "lean", "--stdin"], "controls", source.replace(importLine, "import Effect4.Runtime.Runtime\n"))
  } else {
    await run(["build", "Effect4.Runtime.LiveStack"], "build")
    stdout = await run(["env", "lean", "harness/live-stack/Inspect.lean"], "inspection")
  }
  const candidates = stdout.split(/\r?\n/).filter(line => line.startsWith("{"))
    .map(line => JSON.parse(line)).filter(value => value.kind === "live-stack-inspection")
  assert.equal(candidates.length, 1, "Expected exactly one compiled inspection receipt")
  const result = candidates[0]
  assert.equal(result.mode, controlsOnly ? "controls-only" : "full")
  assert.equal(result.safetyControls.accepted, result.safetyControls.restored)
  const suffixDecoy = result.safetyControls.authoredUnsafeSuffix
  for (const key of ["unsafe", "sourceRange", "safeParent", "rejected"]) {
    assert.equal(suffixDecoy[key], true, `Unsafe-suffix control did not establish ${key}`)
  }
  const importRequirements = {
    "Effect4.lean": ["Effect4.Runtime.LiveStack"],
    "Effect4Test.lean": ["Effect4Test.Runtime.LiveStackContract", "Effect4Test.Runtime.LiveStackAxiomReport", "Effect4Test.Counterexamples.Runtime.LiveStack"]
  }
  assert.deepEqual(result.rootImports.map(row => row.source).sort(), Object.keys(importRequirements).sort())
  for (const row of result.rootImports) {
    const required = importRequirements[row.source]
    assert.equal(row.parser, "Lean.Parser.parseHeader")
    assert.deepEqual(row.required, required)
    assert.equal(row.restored, true)
    for (const name of required) assert.equal(row.observedImports.filter(value => value === name).length, 1)
    assert.deepEqual(row.commentedOutControls.map(control => control.omitted), required)
    for (const control of row.commentedOutControls) {
      assert.equal(control.parsed, true)
      assert.equal(control.rejected, true)
      assert.deepEqual(control.observedImports, row.observedImports.filter(name => name !== control.omitted))
    }
  }
  for (const name of ["missingRootRejected", "missingHelperRejected", "opaqueHelperRejected"]) {
    assert.equal(result.controls[name], true, `${name}: missing fail-closed receipt`)
  }
  for (const name of ["accepted", "restored"]) {
    assert.ok(result.controls[name].visited.length > 0, `${name}: empty graph`)
    assert.deepEqual(result.controls[name].violations, [], `${name}: unexpected legacy call`)
  }
  for (const name of ["indirectRejected", "untakenFallbackRejected"]) {
    const graph = result.controls[name]
    assert.ok(graph.violations.length > 0, `${name}: missing intended rejection`)
    assert.ok(graph.edges.some(([from]) => from === graph.root), `${name}: missing transitive first edge`)
    assert.ok(!graph.edges.some(([from, to]) => from === graph.root && graph.violations.includes(to)), `${name}: direct call does not test transitivity`)
  }
  if (!controlsOnly) {
    assert.equal(result.lean, "4.33.1", "Inspection compiler differs from the frozen contract")
    assert.deepEqual([...result.authoredPublic].sort(), expected)
    assert.ok(result.declarations.length >= expected.length, "Empty or incomplete owned declaration census")
    assert.ok(result.irDeclarations.length > 0, "Empty compiled IR census")
    assert.deepEqual(result.roots.map(row => row.root).sort(), expected.filter(name => /\.(popLive|getContLive)$/.test(name)))
    for (const graph of result.roots) {
      assert.ok(graph.visited.length > 0, `Empty graph for ${graph.root}`)
      assert.deepEqual(graph.violations, [])
    }
    assert.equal(result.restoredProduction, true)
  }
  const after = Object.fromEntries(await Promise.all(sources.map(async name => [name, digest(await readFile(path.join(root, name)))])))
  assert.deepEqual(after, before, "Inspection inputs changed during the check; rerun the saved source")
  const receipt = { ...result, sourceSha256: before, commands }
  await writeFile(path.join(output, controlsOnly ? "controls.json" : "receipt.json"), `${JSON.stringify(receipt, null, 2)}\n`)
  return receipt
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2)
  assert.ok(args.length === 0 || args.length === 1 && args[0] === "--controls-only", "Usage: node harness/live-stack/inspect.mjs [--controls-only]")
  try {
    console.log(JSON.stringify(await inspectCompiled({ controlsOnly: args[0] === "--controls-only" })))
  } catch (error) {
    console.error(error.stack ?? error)
    process.exitCode = 1
  }
}
