#!/usr/bin/env node
// Independent, finite semantic negatives for the frozen live-stack packet.
// No production file is patched. Every candidate is compiled before the
// byte-identical detector applies the breaker's complete literal records.
import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import { delimiter, dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const digest = (bytes) => createHash("sha256").update(bytes).digest("hex");
const frozenFiles = {
  "Effect4/Semantics/Cause.lean": "fc7d008f2955a5ea812717a77e2f3e3d187980c924fc0cb25d5014644c7f7196",
  "Effect4/Semantics/Exit.lean": "a4a4c024ad54a8ab6e52acc1493183349bb532e668af0ed7c2512fa134161383",
  "Effect4/Runtime/Runtime.lean": "fa73134f37da77489bfc4bb14776d32a482171d0f43c9fcc3e26bd811075ccd4",
  "Effect4Test/Runtime/LiveStackContract.lean": "3b48462973b45a09b9fa95e4cf567372dffd6166b7a787548e8af51827a9254a",
  "Effect4Test/Runtime/LiveStackAxiomReport.lean": "e7a84c14d4262bfd7b6936eeedee531330aacc7c991141d2b1d196cd701a6a76",
  "Effect4Test/Counterexamples/Runtime/LiveStack.lean": "af2e8579e456fbf556c2261de7f64433d6be3fe62cb019399a3c58f9cf72075c",
  "test/contracts/live-stack.contract.md": "0c9b3bd3b8d6b881032f7de53445d27c0261415be64cf1358b33afa134563460",
  "docs/LIVE-STACK-DAG.md": "b59daa2fa781a91d3bc36f0e8e91acafcb0f2dd214d92d003d68a1ed8bd0b0a0",
  "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
};
const snapshotModules = [
  "Effect4/Semantics/Cause.lean",
  "Effect4/Semantics/Exit.lean",
  "Effect4/Runtime/Runtime.lean",
  "Effect4/Runtime/LiveStack.lean",
  "Effect4Test/Runtime/LiveStackContract.lean",
];
const popNames = [
  "empty-keeps-all-other-fields",
  "value-keeps-body-name-and-suffix",
  "failure-without-skip-keeps-handler",
  "mask-stops-skip-after-earlier-handler",
  "restoring-mask-substitutes-exact-cause",
  "restoring-mask-starts-skip",
  "finalizer-masks-before-discard-test",
  "interruptible-finalizer-does-not-stop-skip",
  "already-masked-finalizer-pushes-nothing",
  "duplicate-passed-frames-stay-ordered",
  "non-frame-thunk-is-passed-not-executed",
  "model-contAll-finalizer",
  "model-contAll-mask",
];
const entryNames = [
  "plain-entry-finalizer",
  "deferred-value-keeps-entire-stack",
  "deferred-failure-no-skip",
  "masked-deferred-failure-is-not-discarded",
  "deferred-without-cause-is-total-model-state",
  "discarded-deferred-event-precedes-pop",
  "discarded-deferred-event-survives-empty-stack",
  "empty-unmasked-no-pending",
  "model-contAll-deferred-before-mask",
];
const controls = [
  "pop/already-masked-finalizer-pushes-nothing",
  "pop/duplicate-passed-frames-stay-ordered",
  "entry/empty-unmasked-no-pending",
];

const candidateHeader = `import Effect4.Runtime.LiveStack
set_option autoImplicit false
open Effect4
namespace Candidate
abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
abbrev R := FramePop Nat Nat Nat Nat Nat Nat Nat
`;
const candidateFooter = "\nend Candidate\n";
const cleanBody = `def pop (self : F) (demand : Arm) (skip : Bool) : R :=
  self.popLive demand skip
def entry (self : F) (demand : Arm) (skip : Bool) : R :=
  self.getContLive demand skip
`;
const wrapped = (helper) => `${helper}
def pop (self : F) (demand : Arm) (skip : Bool) : R :=
  alter self (self.popLive demand skip)
def entry (self : F) (demand : Arm) (skip : Bool) : R :=
  alter self (self.getContLive demand skip)
`;

const mutants = [
  {
    id: "lost-restoring-frame",
    classification: "compiled result transformation; not a production-source mutation",
    fault: "Drop a leading restoring-mask frame from an interrupted input's returned stack.",
    required: [["pop/finalizer-masks-before-discard-test", "fiber.stack"],
      ["entry/plain-entry-finalizer", "fiber.stack"]],
    body: wrapped(`private def alter (self : F) (result : R) : R :=
  if self.interrupted then
    match result.fiber.stack with
    | .setInterruptible true :: rest =>
        { result with fiber := { result.fiber with stack := rest } }
    | _ => result
  else result`),
  },
  {
    id: "erased-current-program",
    classification: "compiled result transformation; not a production-source mutation",
    fault: "Replace only the returned current program on interrupted inputs.",
    required: [["pop/value-keeps-body-name-and-suffix", "fiber.current"]],
    body: wrapped(`private def alter (self : F) (result : R) : R :=
  if self.interrupted then
    { result with fiber := { result.fiber with current := .success 0 } }
  else result`),
  },
  {
    id: "erased-cause-annotations",
    classification: "compiled result transformation; not a production-source mutation",
    fault: "Erase returned pending-cause annotations but preserve all reason payloads, repetitions and order.",
    required: [["pop/value-keeps-body-name-and-suffix", "fiber.interruptedCause"]],
    body: wrapped(`private def eraseAnnotations (cause : Cause Nat Nat Nat Nat) :
    Cause Nat Nat Nat Nat :=
  ⟨cause.reasons.map fun reason => match reason with
    | .fail value _ => .fail value .empty
    | .die value _ => .die value .empty
    | .interrupt value _ => .interrupt value .empty⟩
private def alter (self : F) (result : R) : R :=
  if self.interrupted then
    { result with fiber := { result.fiber with
        interruptedCause := result.fiber.interruptedCause.map eraseAnnotations } }
  else result`),
  },
  {
    id: "reversed-event-order",
    classification: "compiled result transformation; not a production-source mutation",
    fault: "Reverse chronological events on interrupted inputs, retaining the same events and count.",
    required: [["pop/finalizer-masks-before-discard-test", "events"],
      ["entry/discarded-deferred-event-precedes-pop", "events"]],
    body: wrapped(`private def alter (self : F) (result : R) : R :=
  if self.interrupted then { result with events := result.events.reverse }
  else result`),
  },
  {
    id: "stale-pre-hook-interruption",
    classification: "separately authored structural loop with pre-hook sampling; not a direct production-source mutation",
    fault: "Choose whether to skip from the pre-hook fiber, so masking cannot stop skipping and restoration cannot start it.",
    required: [["pop/finalizer-masks-before-discard-test", "answer"],
      ["pop/restoring-mask-starts-skip", "answer"]],
    body: `private def prependObservation (frame : P) (events : List (FrameEvent Nat Nat Nat Nat Nat Nat Nat))
    (result : R) : R :=
  { result with popped := frame :: result.popped, events := events ++ result.events }
-- Structural recursion over the original frames is explicit here. Its
-- deliberately wrong sampling point is BEFORE Prim.ensure, not after it.
private def staleLoop (demand : Arm) (skip : Bool) : List P → F → R
  | [], fiber => ⟨.empty, [], [], fiber⟩
  | frame :: rest, fiber =>
    let staleSkip := skip && fiber.interrupted
    let after := frame.ensure fiber
    let events := frame.passEvents after.snd
    match frame.answerOf demand after.snd with
    | none => prependObservation frame events (staleLoop demand skip rest after.fst)
    | some answer =>
      if staleSkip then prependObservation frame events (staleLoop demand skip rest after.fst)
      else ⟨answer, [frame], events,
        { after.fst with stack := after.fst.stack ++ rest }⟩
def pop (self : F) (demand : Arm) (skip : Bool) : R :=
  staleLoop demand skip self.stack { self with stack := [] }
-- The entry rule itself is unchanged; only its pop loop is substituted.
def entry (self : F) (demand : Arm) (skip : Bool) : R :=
  let cleared := { self with deferredInterrupt := false }
  if self.deferredInterrupt then
    if skip && self.interrupted then
      let next := pop cleared demand skip
      { next with events := .deferred self.pendingCause :: next.events }
    else ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause], cleared⟩
  else pop cleared demand skip
`,
  },
  {
    id: "legacy-deferred-shortcut",
    classification: "compiled substitution of the actual unchanged legacy entry",
    fault: "Use the old entry that drops masked deferred answers and discarded deferred events.",
    required: [["entry/masked-deferred-failure-is-not-discarded", "answer"],
      ["entry/discarded-deferred-event-survives-empty-stack", "events"]],
    body: `def pop (self : F) (demand : Arm) (skip : Bool) : R :=
  self.popLive demand skip
def entry (self : F) (demand : Arm) (skip : Bool) : R :=
  self.getCont demand skip
`,
  },
];

// One detector text for clean, every mutant, and every restored control.
// It calls the frozen checkCases both on the whole table and on each row.
// The component comparisons only explain the discrepancy; they cannot
// replace, weaken, or choose the full-result acceptance condition.
const detectorSource = `import Lean
import Candidate
import Effect4Test.Runtime.LiveStackContract
set_option autoImplicit false
open Effect4 Lean
open Effect4Test.Runtime.LiveStackContract
namespace LiveStackMutationDetector
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev R := FramePop Nat Nat Nat Nat Nat Nat Nat
private abbrev Row := String × F × Arm × Bool × R
private def inspect (suite : String) (candidate : F → Arm → Bool → R)
    (row : Row) : Json :=
  let (name, self, demand, skip, expected) := row
  let actual := candidate self demand skip
  let fields : List (String × Bool) := [
    ("answer", decide (actual.answer = expected.answer)),
    ("popped", decide (actual.popped = expected.popped)),
    ("events", decide (actual.events = expected.events)),
    ("fiber.current", decide (actual.fiber.current = expected.fiber.current)),
    ("fiber.stack", decide (actual.fiber.stack = expected.fiber.stack)),
    ("fiber.interruptible", decide (actual.fiber.interruptible = expected.fiber.interruptible)),
    ("fiber.interruptedCause", decide (actual.fiber.interruptedCause = expected.fiber.interruptedCause)),
    ("fiber.deferredInterrupt", decide (actual.fiber.deferredInterrupt = expected.fiber.deferredInterrupt))]
  Json.mkObj [
    ("suite", toJson suite), ("name", toJson name),
    ("accepted", toJson (checkCases [row] candidate)),
    ("mismatches", toJson ((fields.filter fun (_, same) => !same).map Prod.fst)),
    ("fieldComparisons", Json.mkObj (fields.map fun (key, same) => (key, toJson same))),
    ("input", Json.mkObj [
      ("interruptible", toJson self.interruptible),
      ("pendingCause", toJson self.interruptedCause.isSome),
      ("deferred", toJson self.deferredInterrupt),
      ("stackLength", toJson self.stack.length), ("skip", toJson skip)]),
    ("poppedCount", toJson actual.popped.length),
    ("expectedPoppedCount", toJson expected.popped.length),
    ("eventCount", toJson actual.events.length),
    ("expectedEventCount", toJson expected.events.length)]
def run : IO UInt32 := do
  let report := Json.mkObj [
    ("format", toJson "effect4-live-stack-literal-check-v1"),
    ("popAccepted", toJson (checkCases popCases Candidate.pop)),
    ("entryAccepted", toJson (checkCases entryCases Candidate.entry)),
    ("cases", toJson (popCases.map (inspect "pop" Candidate.pop) ++
      entryCases.map (inspect "entry" Candidate.entry)))]
  let out ← IO.getStdout
  out.putStrLn ("LIVE_STACK_MUTATION_JSON " ++ report.compress)
  return 0
end LiveStackMutationDetector
`;
const runnerSource = `import Detector
def main : IO UInt32 := LiveStackMutationDetector.run
`;

let runDir;
const receipt = {
  format: "effect4-live-stack-mutations-v1",
  status: "running",
  startedAt: new Date().toISOString(),
  boundary: "Finite execution of freshly compiled Lean candidates against 22 frozen full-result literals; not a universal source simulation or native-code compiler proof.",
  execution: "Lean's compiled-module interpreter, after separate candidate and detector compilation; C output is also emitted but is not native-linked or executed.",
  controls,
  commands: [],
  candidates: [],
};

async function command(label, executable, args, cwd = root, env = process.env) {
  const index = String(receipt.commands.length).padStart(2, "0");
  const logBase = join(runDir, `${index}-${label}`);
  const started = Date.now();
  const result = await new Promise((done) => {
    const child = spawn(executable, args, { cwd, env, stdio: ["ignore", "pipe", "pipe"] });
    let stdout = "", stderr = "", spawnError = null, timedOut = false;
    const timer = setTimeout(() => { timedOut = true; child.kill("SIGKILL"); }, 600_000);
    child.stdout.on("data", (chunk) => { stdout += chunk; });
    child.stderr.on("data", (chunk) => { stderr += chunk; });
    child.on("error", (error) => { spawnError = error.message; });
    child.on("close", (code, signal) => {
      clearTimeout(timer);
      done({ code, signal, stdout, stderr, spawnError, timedOut });
    });
  });
  await writeFile(`${logBase}.stdout`, result.stdout);
  await writeFile(`${logBase}.stderr`, result.stderr);
  const row = {
    label, executable, args, cwd, exitCode: result.code, signal: result.signal,
    timedOut: result.timedOut, spawnError: result.spawnError,
    elapsedMs: Date.now() - started,
    stdout: relative(root, `${logBase}.stdout`), stdoutSha256: digest(result.stdout),
    stderr: relative(root, `${logBase}.stderr`), stderrSha256: digest(result.stderr),
  };
  receipt.commands.push(row);
  assert.equal(result.spawnError, null, `${label}: failed to start: ${result.spawnError}`);
  assert.equal(result.timedOut, false, `${label}: timed out; not a semantic rejection`);
  assert.equal(result.code, 0,
    `${label}: exit ${result.code}; build/execution failure is not a semantic rejection. See ${logBase}.stderr and .stdout`);
  return { ...result, row };
}

function validateReport(report) {
  assert.equal(report.format, "effect4-live-stack-literal-check-v1");
  assert.equal(report.cases.length, 22, "empty or incomplete detector result");
  assert.deepEqual(report.cases.filter((row) => row.suite === "pop").map((row) => row.name), popNames);
  assert.deepEqual(report.cases.filter((row) => row.suite === "entry").map((row) => row.name), entryNames);
  for (const row of report.cases) {
    assert.equal(typeof row.accepted, "boolean");
    assert.equal(row.accepted, row.mismatches.length === 0, `full-result/component disagreement in ${row.name}`);
    assert.deepEqual(Object.keys(row.fieldComparisons).sort(), ["answer", "popped", "events",
      "fiber.current", "fiber.stack", "fiber.interruptible", "fiber.interruptedCause", "fiber.deferredInterrupt"].sort());
    for (const same of Object.values(row.fieldComparisons)) assert.equal(typeof same, "boolean");
    // Lean's JSON objects sort keys; only diagnostic field labels are sorted
    // here. No observed frame, reason, annotation or event list is sorted.
    assert.deepEqual([...row.mismatches].sort(),
      Object.entries(row.fieldComparisons).filter(([, same]) => !same).map(([name]) => name).sort());
  }
  assert.equal(report.popAccepted, report.cases.filter((row) => row.suite === "pop").every((row) => row.accepted));
  assert.equal(report.entryAccepted, report.cases.filter((row) => row.suite === "entry").every((row) => row.accepted));
}

async function compileCandidate(id, body, kind, lean, leanPath) {
  const stage = join(runDir, id);
  await mkdir(stage);
  const candidateSource = candidateHeader + body + candidateFooter;
  // Candidate code never receives fixture names, expected results or the
  // detector API. Only the unchanged detector imports the frozen packet.
  assert(!/LiveStackContract|checkCases|popCases|entryCases/.test(candidateSource));
  assert(!/\b(sorry|admit|axiom|unsafe|partial|native_decide)\b/.test(candidateSource));
  await writeFile(join(stage, "Candidate.lean"), candidateSource);
  await writeFile(join(stage, "Detector.lean"), detectorSource);
  await writeFile(join(stage, "Run.lean"), runnerSource);
  const env = { ...process.env, LEAN_PATH: [stage, leanPath].join(delimiter) };
  const candidateCompile = await command(`${id}-candidate`, lean,
    ["-DmaxErrors=10000", "-o", "Candidate.olean", "-c", "Candidate.c", "Candidate.lean"], stage, env);
  // The candidate has already compiled successfully. A proof or name error
  // in the next stage aborts; it cannot earn a semantic-negative receipt.
  const detectorCompile = await command(`${id}-detector`, lean,
    ["-DmaxErrors=10000", "-o", "Detector.olean", "-c", "Detector.c", "Detector.lean"], stage, env);
  const execution = await command(`${id}-execute`, lean, ["--run", "Run.lean"], stage, env);
  const rows = execution.stdout.split(/\r?\n/).filter((line) => line.startsWith("LIVE_STACK_MUTATION_JSON "));
  assert.equal(rows.length, 1, `${id}: exactly one nonempty detector receipt is required`);
  const report = JSON.parse(rows[0].slice("LIVE_STACK_MUTATION_JSON ".length));
  validateReport(report);
  const failures = report.cases.filter((row) => !row.accepted).map((row) => `${row.suite}/${row.name}`);
  const row = {
    id, kind,
    candidateSha256: digest(candidateSource), detectorSha256: digest(await readFile(join(stage, "Detector.lean"))),
    candidateOleanSha256: digest(await readFile(join(stage, "Candidate.olean"))),
    candidateCSha256: digest(await readFile(join(stage, "Candidate.c"))),
    compiledBeforeDetection: candidateCompile.row.exitCode === 0 && detectorCompile.row.exitCode === 0,
    executionExitCode: execution.row.exitCode,
    semanticRejection: failures.length > 0,
    failures,
    ...report,
  };
  assert.equal(row.detectorSha256, receipt.detectorSha256, `${id}: detector was changed`);
  receipt.candidates.push(row);
  return row;
}

async function main() {
  assert.equal(process.argv.length, 2, "usage: node scripts/test-live-stack-mutations.mjs");
  const parent = join(root, ".lake/live-stack/mutations");
  await mkdir(parent, { recursive: true });
  runDir = await mkdtemp(join(parent, "run-"));
  receipt.receiptPath = relative(root, join(runDir, "receipt.json"));
  receipt.detectorSha256 = digest(detectorSource);
  receipt.scriptSha256 = digest(await readFile(fileURLToPath(import.meta.url)));
  receipt.sourceBefore = {};
  const sourceBytes = new Map();
  for (const path of new Set([...Object.keys(frozenFiles), ...snapshotModules,
    "scripts/test-live-stack-mutations.mjs"])) {
    const bytes = await readFile(join(root, path));
    sourceBytes.set(path, bytes);
    receipt.sourceBefore[path] = digest(bytes);
    if (path in frozenFiles) assert.equal(digest(bytes), frozenFiles[path], `frozen source drift: ${path}`);
  }
  assert.equal(sourceBytes.get("lean-toolchain").toString().trim(), "leanprover/lean4:v4.33.1");
  const lean = (await command("locate-lean", "lake", ["env", "which", "lean"])).stdout.trim();
  assert(lean.startsWith("/"), "expected an absolute Lean toolchain path");
  const basePath = (await command("locate-lean-path", "lake", ["env", "printenv", "LEAN_PATH"])).stdout.trim();
  assert(basePath.length > 0 && !basePath.includes("\n"), "invalid Lean search path");
  const version = (await command("lean-version", lean, ["--version"])).stdout.trim();
  assert.match(version, /^Lean \(version 4\.33\.1(?:,|\))/);
  receipt.toolchain = { lean, version, node: process.version, platform: process.platform, arch: process.arch };

  // Fresh, exact-byte copies avoid stale production/test .olean files and
  // avoid mutating or rebuilding a concurrently used package build tree.
  const frozenRoot = join(runDir, "frozen");
  const leanPath = [frozenRoot, basePath].join(delimiter);
  const env = { ...process.env, LEAN_PATH: leanPath };
  receipt.snapshotCompilation = [];
  for (const path of snapshotModules) {
    const target = join(frozenRoot, path);
    await mkdir(dirname(target), { recursive: true });
    await writeFile(target, sourceBytes.get(path));
    const olean = path.replace(/\.lean$/, ".olean");
    const result = await command(`snapshot-${path.replaceAll("/", "-")}`, lean,
      ["-DmaxErrors=10000", "-o", olean, path], frozenRoot, env);
    receipt.snapshotCompilation.push({ path, sourceSha256: digest(await readFile(target)),
      oleanSha256: digest(await readFile(join(frozenRoot, olean))), exitCode: result.row.exitCode });
  }

  const clean = await compileCandidate("clean", cleanBody, "accepted-control", lean, leanPath);
  assert.equal(clean.semanticRejection, false, "clean candidate failed the independent literals");
  for (const mutant of mutants) {
    process.stderr.write(`Checking compiled semantic candidate: ${mutant.id}\n`);
    const result = await compileCandidate(mutant.id, mutant.body, "deliberately-wrong", lean, leanPath);
    result.classification = mutant.classification;
    result.fault = mutant.fault;
    result.requiredDiscriminators = mutant.required;
    assert.equal(result.semanticRejection, true, `${mutant.id}: candidate survived`);
    const lookup = (id) => result.cases.find((row) => `${row.suite}/${row.name}` === id);
    for (const [id, field] of mutant.required) {
      assert(lookup(id)?.mismatches.includes(field), `${mutant.id}: intended discriminator ${id}:${field} did not reject`);
    }
    for (const id of controls) assert.equal(lookup(id)?.accepted, true, `${mutant.id}: positive control rejected: ${id}`);
    const restored = await compileCandidate(`restored-${mutant.id}`, cleanBody, "restored-control", lean, leanPath);
    assert.equal(restored.candidateSha256, clean.candidateSha256, "restoration did not recover the exact clean candidate");
    assert.equal(restored.semanticRejection, false, `${mutant.id}: restored candidate failed`);
    result.restoredControl = restored.id;
  }
  assert.equal(receipt.candidates.length, 13);
  receipt.sourceAfter = {};
  for (const [path] of sourceBytes) receipt.sourceAfter[path] = digest(await readFile(join(root, path)));
  assert.deepEqual(receipt.sourceAfter, receipt.sourceBefore, "source changed during the campaign");
  receipt.summary = {
    frozenPopCases: popNames.length, frozenEntryCases: entryNames.length,
    independentCandidatesCompiled: receipt.candidates.length,
    wrongCandidatesRejected: mutants.length,
    cleanAndRestoredCandidatesAccepted: 1 + mutants.length,
    fullResultChecks: receipt.candidates.length * (popNames.length + entryNames.length),
    acceptedControlsPerWrongCandidate: controls.length,
    unchangedDetector: true, unchangedSource: true,
  };
  receipt.status = "passed";
}

try {
  await main();
} catch (error) {
  receipt.status = "failed";
  receipt.error = error.stack ?? String(error);
  process.exitCode = 1;
} finally {
  receipt.finishedAt = new Date().toISOString();
  if (runDir) await writeFile(join(runDir, "receipt.json"), `${JSON.stringify(receipt, null, 2)}\n`);
  process.stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
}
