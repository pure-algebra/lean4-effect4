import assert from "node:assert/strict"
import { createHash } from "node:crypto"
import { spawn } from "node:child_process"
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises"
import path from "node:path"
import { fileURLToPath } from "node:url"

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..")
const args = process.argv.slice(2)
assert(args.every(arg => ["--write", "--repository"].includes(arg)) && new Set(args).size === args.length,
  "Usage: node scripts/check-live-stack.mjs [--write] [--repository]")
const sha = bytes => createHash("sha256").update(bytes).digest("hex")
const text = relative => readFile(path.join(root, relative), "utf8")
const hash = async relative => sha(await readFile(path.join(root, relative)))
const stable = value => Array.isArray(value) ? value.map(stable) :
  value !== null && typeof value === "object" ? Object.fromEntries(Object.keys(value).sort().map(key => [key, stable(value[key])])) : value
const encode = value => JSON.stringify(stable(value), null, 2) + "\n"
await mkdir(path.join(root, ".lake/live-stack/check"), { recursive: true })
const work = await mkdtemp(path.join(root, ".lake/live-stack/check/run-"))
const commands = []
const receipt = { schema: "effect4-live-stack-check-v1", work, commands }

async function run(label, executable, arguments_, { allowFailure = false, timeout = 600000 } = {}) {
  const result = await new Promise((resolve, reject) => {
    const child = spawn(executable, arguments_, { cwd: root, env: process.env, stdio: ["ignore", "pipe", "pipe"] })
    let stdout = "", stderr = "", expired = false
    const timer = setTimeout(() => { expired = true; child.kill("SIGTERM") }, timeout)
    child.stdout.setEncoding("utf8").on("data", part => { stdout += part })
    child.stderr.setEncoding("utf8").on("data", part => { stderr += part })
    child.on("error", error => { clearTimeout(timer); reject(error) })
    child.on("close", (exitCode, signal) => { clearTimeout(timer); resolve({ exitCode, signal, expired, stdout, stderr }) })
  })
  await writeFile(path.join(work, `${label}.stdout.log`), result.stdout)
  await writeFile(path.join(work, `${label}.stderr.log`), result.stderr)
  commands.push({ label, command: [executable, ...arguments_], exitCode: result.exitCode,
    signal: result.signal, expired: result.expired, stdoutSha256: sha(result.stdout), stderrSha256: sha(result.stderr) })
  assert(!result.expired && result.signal === null, `${label}: interrupted or timed out`)
  if (!allowFailure) assert.equal(result.exitCode, 0, `${label} failed:\n${result.stdout}\n${result.stderr}`)
  return result
}

function oneJson(result, label) {
  assert(result.stdout.trim().startsWith("{"), `${label}: expected one JSON receipt`)
  const value = JSON.parse(result.stdout)
  assert(value !== null && typeof value === "object" && !Array.isArray(value), `${label}: expected an object`)
  return value
}

const registerPath = "test/counterexamples/REGISTER.md"
const registerIds = ["E4-RUN-CE-022", "E4-RUN-CE-023", "E4-RUN-CE-024"]
function checkRegister(source) {
  const rows = source.split(/\r?\n/).filter(row => registerIds.some(id => row.startsWith(`| \`${id}\` |`)))
  assert.deepEqual(rows.map(row => row.split("`")[1]), registerIds, "Missing, repeated or reordered live-stack counterexample record")
  const sha256 = sha(rows.join("\n") + "\n")
  assert.equal(sha256, "b08db2e0ed9261988848e07f0f28897e33f1a52de16813466d816797468d0579", "Frozen live-stack counterexample record changed")
  return { path: registerPath, ids: registerIds, rows, sha256 }
}

function checkDefaultBuild(result, knownRed) {
  assert.equal(result.exitCode, 1, "Expected an ordinary declared-red build failure")
  const output = `${result.stdout}\n${result.stderr}`.replace(/\x1b\[[0-9;]*m/g, "")
  const summary = output.split("Some required targets logged failures:")
  assert.equal(summary.length, 2, "Missing or ambiguous failing-target summary")
  const failing = [...summary[1].matchAll(/^- (Effect4\S*)$/gm)].map(row => row[1]).sort()
  assert.equal(new Set(failing).size, failing.length, "Repeated failing target")
  const consequentialRoot = failing.includes("Effect4Test")
  assert.deepEqual(failing.filter(name => name !== "Effect4Test"), knownRed, "Unexpected package-build failure")
  const rootErrors = [...output.matchAll(/^error: Effect4Test\.lean:\d+:\d+: (.*)$/gm)].map(row => row[1])
  const expectedRootErrors = knownRed.map(module =>
    `Effect4 module-closure gate: ${path.join(root, module.replaceAll(".", "/") + ".lean")} is not reachable from the Effect4Test audit root`)
  if (consequentialRoot) {
    assert.equal(rootErrors.length, 1, "Unexpected root diagnostic count")
    assert(expectedRootErrors.includes(rootErrors[0]), "Root failed for a reason other than the declared-red module closure")
  } else assert.equal(rootErrors.length, 0, "Unreported root failure")
  const compilerCodes = [...output.matchAll(/^error: Lean exited with code (\d+)$/gm)].map(row => Number(row[1]))
  assert.equal(compilerCodes.length, failing.length, "Missing compiler exit status")
  assert(compilerCodes.every(code => code === 1), "A compiler was interrupted rather than reporting a declared-red error")
  return { defaultBuild: "declared-red", failing, consequentialRoot }
}

try {
  const frozen = "test/contracts/live-stack.contract.md"
  assert.equal(await hash(frozen), "4d1a61f10b29bc8a38042c0f9f887b27397c8020da5631a1c0b39809499cf7d3", "Frozen contract changed")
  assert.equal(await hash("docs/LIVE-STACK-DAG.md"), "b59daa2fa781a91d3bc36f0e8e91acafcb0f2dd214d92d003d68a1ed8bd0b0a0", "Frozen graph changed")
  const hashes = [...(await text(frozen)).matchAll(/^\| `([^`]+)` \| `([a-f0-9]{64})` \|$/gm)]
  assert.equal(hashes.length, 16, "Missing or ambiguous frozen input inventory")
  for (const [, file, expected] of hashes) assert.equal(await hash(file), expected, `Frozen source changed: ${file}`)
  const inputs = [...hashes.map(row => row[1]), frozen, "docs/LIVE-STACK-DAG.md", "Effect4/Runtime/LiveStack.lean",
    "harness/live-stack/public.ts", "harness/live-stack/host.mjs", "harness/live-stack/Inspect.lean",
    "harness/live-stack/inspect.mjs", "scripts/check-live-stack.mjs", "scripts/test-live-stack-mutations.mjs",
    "Effect4.lean", "Effect4Test.lean", "test/fixtures/trust-gate/known-red.txt"]
  const snapshot = async () => Object.fromEntries(await Promise.all([...new Set(inputs)].sort().map(async file => [file, await hash(file)])))
  const before = await snapshot()
  const registerSource = await text(registerPath)
  const counterexamples = checkRegister(registerSource)
  for (const row of counterexamples.rows) {
    assert.throws(() => checkRegister(registerSource.replace(row, "")), /counterexample record/)
    assert.throws(() => checkRegister(registerSource + "\n" + row), /counterexample record/)
    assert.throws(() => checkRegister(registerSource.replace(row, row.replace("SEEDED", "MOVED"))), /counterexample record/)
  }
  assert.deepEqual(checkRegister(registerSource + "\nUnrelated registration text.\n"), counterexamples)
  const knownRed = (await text("test/fixtures/trust-gate/known-red.txt")).split(/\r?\n/).filter(line => line && !line.startsWith("#")).sort()
  // The declared red set belongs to other packets; this gate only requires that no
  // live-stack module is declared red. (The two historical orphans it used to
  // expect there, the binary race contract and the byte parser contract, were
  // retired with their lanes on 2026-09-04, and the list is empty.)
  assert(!knownRed.some(module => module.includes("LiveStack")), "A live-stack module is declared red")
  await run("narrow-build", "lake", ["build", "Effect4Test.Runtime.LiveStackContract", "Effect4Test.Runtime.LiveStackAxiomReport", "Effect4Test.Counterexamples.Runtime.LiveStack"])
  const axiomResult = await run("fresh-axioms", "lake", ["env", "lean", "Effect4Test/Runtime/LiveStackAxiomReport.lean"])
  const proofs = [...axiomResult.stdout.matchAll(/'([^']+)' depends on axioms: \[([^\]]*)\]/g)]
    .map(([, name, list]) => ({ name, axioms: list.split(",").map(x => x.trim()).filter(Boolean).sort() }))
  assert.equal(proofs.length, 8)
  for (const proof of proofs) assert(proof.axioms.every(name => ["propext", "Quot.sound"].includes(name)), `${proof.name}: unexpected proof dependency`)
  for (const name of ["FramesContract", "FramesAxiomReport"]) {
    await run(`old-${name}`, "lake", ["env", "lean", `Effect4Test/Runtime/${name}.lean`])
  }
  await run("old-counterexamples", "lake", ["env", "lean", "Effect4Test/Counterexamples/Runtime/Frames.lean"])
  const inspection = oneJson(await run("inspection", process.execPath, ["harness/live-stack/inspect.mjs"]), "inspection")
  assert.equal(inspection.mode, "full")
  assert.equal(inspection.authoredPublic.length, 8)
  assert.deepEqual(proofs.map(row => row.name).sort(), [...inspection.authoredPublic].sort())
  const requiredImports = {
    "Effect4.lean": ["Effect4.Runtime.LiveStack"],
    "Effect4Test.lean": ["Effect4Test.Runtime.LiveStackContract", "Effect4Test.Runtime.LiveStackAxiomReport", "Effect4Test.Counterexamples.Runtime.LiveStack"]
  }
  assert.deepEqual(inspection.rootImports.map(row => row.source).sort(), Object.keys(requiredImports).sort())
  for (const row of inspection.rootImports) {
    assert.equal(row.parser, "Lean.Parser.parseHeader")
    assert.deepEqual(row.required, requiredImports[row.source])
    assert.equal(inspection.sourceSha256[row.source], before[row.source])
    for (const name of row.required) assert.equal(row.observedImports.filter(value => value === name).length, 1)
    assert.deepEqual(row.commentedOutControls.map(control => control.omitted), row.required)
    for (const control of row.commentedOutControls) {
      assert.equal(control.parsed, true)
      assert.equal(control.rejected, true)
      assert.deepEqual(control.observedImports, row.observedImports.filter(name => name !== control.omitted))
    }
    assert.equal(row.restored, true)
  }
  for (const key of ["unsafe", "sourceRange", "safeParent", "rejected"]) {
    assert.equal(inspection.safetyControls.authoredUnsafeSuffix[key], true)
  }
  const mutations = oneJson(await run("mutations", process.execPath, ["scripts/test-live-stack-mutations.mjs"], { timeout: 600000 }), "mutations")
  assert.equal(mutations.status, "passed")
  assert.equal(mutations.summary.independentCandidatesCompiled, 13)
  assert.equal(mutations.summary.wrongCandidatesRejected, 6)
  assert.equal(mutations.summary.cleanAndRestoredCandidatesAccepted, 7)
  assert.equal(mutations.summary.fullResultChecks, 286)
  assert.equal(mutations.summary.unchangedDetector, true)
  assert.equal(mutations.summary.unchangedSource, true)
  assert.equal(mutations.candidates.length, 13)
  assert.equal(new Set(mutations.candidates.map(row => row.id)).size, 13)
  for (const row of mutations.candidates) {
    assert.equal(row.compiledBeforeDetection, true)
    assert.equal(row.executionExitCode, 0)
    assert.equal(row.detectorSha256, mutations.detectorSha256)
    assert.equal(row.cases.length, 22)
    assert.equal(row.semanticRejection, row.kind === "deliberately-wrong")
  }
  const host = oneJson(await run("host", process.execPath, ["harness/live-stack/host.mjs"]), "host")
  assert.equal(host.result.delayedPushRejected, 1)
  assert.equal(host.result.publicExecutions, 18)
  assert.equal(host.result.allPublicFibersCompleted, true)
  const whole = await run("package-build", "lake", ["build"], { allowFailure: true, timeout: 600000 })
  receipt.repository = checkDefaultBuild(whole, knownRed)
  assert.throws(() => checkDefaultBuild({ ...whole, stdout: whole.stdout + "\nerror: Effect4Test.lean:1:1: unrelated root failure\n" }, knownRed), /root diagnostic|root failure/)
  assert.throws(() => checkDefaultBuild({ ...whole, stdout: whole.stdout + "\nerror: Lean exited with code 143\n" }, knownRed), /compiler/)
  if (args.includes("--repository")) {
    const checks = {}
    for (const [label, script] of [["trust", "test-trust-gate.sh"], ["fiber-assurance", "check-fiber-assurance.sh"], ["citations", "check-internal-citations.sh"]]) {
      const result = await run(label, "bash", [`scripts/${script}`], { allowFailure: true, timeout: 1200000 })
      checks[label] = result.exitCode
    }
    receipt.repository.additionalChecks = checks
  }
  assert.deepEqual(await snapshot(), before, "Checked source changed during verification")
  assert.deepEqual(checkRegister(await text(registerPath)), counterexamples, "Checked counterexample record changed during verification")
  const projection = {
    schema: "effect4-live-stack-assurance-v1", freezeCommit: "8323eaf15260a270f2be6c2e180289519a2b0319",
    generator: "scripts/check-live-stack.mjs", regeneration: "node scripts/check-live-stack.mjs --write",
    sourceSha256: before, authoredPublic: inspection.authoredPublic, declarations: inspection.declarations,
    irDeclarations: inspection.irDeclarations, executableRoots: inspection.roots, proofs, counterexamples,
    rootImports: inspection.rootImports, inspectionControls: inspection.controls,
    safetyControls: inspection.safetyControls,
    hostProfile: { pin: host.before.pin, node: host.host.node, platform: host.host.platform, arch: host.host.arch },
    hostResults: host.result, hostObservations: host.public.map(({ before, wrong, restored, rejection }) =>
      ({ before, wrong, restored, rejected: rejection !== null })),
    constructedDeferred: host.constructedDeferred,
    mutationEvidence: { summary: mutations.summary, detectorSha256: mutations.detectorSha256,
      candidates: mutations.candidates.map(({ id, kind, candidateSha256, failures, cases, semanticRejection,
        classification, fault, requiredDiscriminators, restoredControl }) =>
        ({ id, kind, candidateSha256, failures, cases, semanticRejection,
          classification, fault, requiredDiscriminators, restoredControl })) },
    requiredOpen: ["source-state reachability", "Lean-JavaScript execution simulation", "AsyncFinalizer primitive extension",
      "executing finalizer and scheduler relation", "compiler correctness", "default-runtime adoption", "repository-wide trust closure"]
  }
  receipt.mutations = mutations
  receipt.inspection = inspection
  receipt.host = { work: host.work, results: host.result }
  const output = "generated/live-stack-assurance.json"
  if (args.includes("--write")) await writeFile(path.join(root, output), encode(projection))
  else assert.equal(await text(output), encode(projection), `Stale ${output}; regenerate with --write and review`)
  receipt.projection = { path: output, sha256: sha(encode(projection)) }
  const additional = receipt.repository.additionalChecks
  receipt.status = additional && Object.values(additional).some(code => code !== 0) ? "local-pass-repository-open" : "local-pass"
  await writeFile(path.join(work, "receipt.json"), encode(receipt))
  console.log(JSON.stringify(receipt))
  if (receipt.status !== "local-pass") process.exitCode = 1
} catch (error) {
  receipt.status = "failed"
  receipt.failure = String(error.stack ?? error)
  await writeFile(path.join(work, "receipt.json"), encode(receipt))
  console.error(JSON.stringify(receipt))
  process.exitCode = 1
}
