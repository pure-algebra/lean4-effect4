// E4-FLOW-CE-024/025: finite historical counterexample, not a current host gate.
// Usage: node harness/trace/interrupt-mask-boundary.mjs /path/to/node_modules/effect
// Reads exact historical generated target/tail bytes, writes only an OS temp dir.
// The candidate wrapper is a scratch experiment, never generated-file editing.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtemp, readFile, writeFile, mkdir, symlink, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

assert.equal(process.argv.length, 3, "Pass the installed effect package directory");
const effectRoot = resolve(process.argv[2]);
const nodeModules = dirname(effectRoot);
const root = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const revision = "5b29edb4b33ebf7e7afb28f110dc7119e0ed1fef";
const upstream = "2600f62f4532026928454dcea8d1c48557b3f942";
const sha256 = bytes => createHash("sha256").update(bytes).digest("hex");
const sourceHash = "0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0";
const runtimeHash = "269e711472b84dcd04862f11e842acc1095cc5d22948af36cda76e9a9185828e";
const packageInfo = JSON.parse(await readFile(join(effectRoot, "package.json"), "utf8"));
assert.equal(packageInfo.version, "4.0.0-rc.112", "Effect version drift");
assert.equal(sha256(await readFile(join(effectRoot, "src/internal/effect.ts"))), sourceHash,
  "Installed source drift");
assert.equal(sha256(await readFile(join(root,
  "vendor/effect-4.0.0-rc.112/src/internal/effect.ts"))), sourceHash, "Vendored source drift");
assert.equal(sha256(await readFile(join(effectRoot, "dist/internal/effect.js"))), runtimeHash,
  "Executed runtime drift");

const historical = path => {
  const result = spawnSync("git", ["-C", root, "show", `${revision}:${path}`],
    { encoding: "utf8", maxBuffer: 4 * 1024 * 1024 });
  assert.equal(result.status, 0, result.stderr || `Cannot read ${path} at ${revision}`);
  return result.stdout;
};
const inputs = {};
const files = ["atoms.ts", "tracer.ts", "flow-fixture.ts", "interrupt-tail.ts"];
const baseline = Object.fromEntries(files.map(file => {
  const path = `harness/trace/${file}`;
  const text = historical(path);
  inputs[path] = sha256(text);
  return [file, text];
}));
const goldenPath = "generated/traces/flow/interrupt/interruptMasked.tsv";
const golden = historical(goldenPath);
inputs[goldenPath] = sha256(golden);
const rowsOf = text => text.trim().split("\n").filter(line =>
  /^(enter|op|answer|decide|leave|finalizer|done|frontier)\t/.test(line));
const goldenRows = rowsOf(golden);
assert.equal(golden.match(/^tape\t(.+)$/m)?.[1], "1000005:1");
const maskPath = "generated/traces/masks.tsv";
const maskText = historical(maskPath);
inputs[maskPath] = sha256(maskText);
const maskColumns = { op: 0, answer: 1, decide: 2, enter: 3, leave: 3,
  finalizer: 4, done: 5, frontier: 6 };
const masks = maskText.trim().split("\n").filter(row => row.startsWith("mask\t"))
  .map(row => { const [, name, ...bits] = row.split("\t"); return [name, bits]; });
const project = (rows, bits) => rows.filter(row => bits[maskColumns[row.split("\t")[0]]] === "1");
const agreement = rows => Object.fromEntries(masks.map(([name, bits]) =>
  [name, JSON.stringify(project(rows, bits)) === JSON.stringify(project(goldenRows, bits))]));

const replaceOnce = (text, before, after) => {
  assert.equal(text.split(before).length, 2, `Expected exactly one transform anchor: ${before}`);
  return text.replace(before, after);
};
const pendingBlock = `      pending = pending || answered
      if (!masked() && pending) {
        pending = false
        fiber.interruptUnsafe()
      }`;
const diagnosticBefore = `      const before = { site, answered, modelMasked: masked(),
        interruptible: fiber.interruptible, interrupted: Boolean(fiber._interruptedCause),
        deferred: fiber._deferredInterrupt }`;
const diagnosticAfter = `      deliveryDiagnostics.push({ ...before,
        afterInterrupted: Boolean(fiber._interruptedCause), afterDeferred: fiber._deferredInterrupt })`;
const instrumentTail = direct => {
  let text = replaceOnce(baseline["interrupt-tail.ts"], "const sink: Event[] = []",
    "const sink: Event[] = []\nconst deliveryDiagnostics: unknown[] = []");
  text = replaceOnce(text, pendingBlock, [diagnosticBefore,
    direct ? "      if (answered) fiber.interruptUnsafe()" : pendingBlock,
    diagnosticAfter].join("\n"));
  return replaceOnce(text, "  patchedFrames,", "  patchedFrames,\n  deliveryDiagnostics,");
};
const changeMaskedProgram = (mask, returns) => {
  const text = baseline["flow-fixture.ts"];
  const start = text.indexOf("export const interruptMasked =");
  const end = text.indexOf("/** Lowered from the region flow `interruptFinalizer`", start);
  assert(start >= 0 && end > start, "Historical program boundaries changed");
  let body = text.slice(start, end);
  if (mask) {
    body = replaceOnce(body, "const r1 = yield* Effect.scoped(",
      "const r1 = yield* Effect.uninterruptible(Effect.scoped(");
    body = replaceOnce(body, "}), (exit) => regions.leave(1, exit)))",
      "}), (exit) => regions.leave(1, exit))))");
  }
  if (returns) {
    body = replaceOnce(body, `        case 4: {
          yield* interrupts.point(1000009)
          const a4 = yield* rCell.put(b4p0)
          b5p0 = b4p0
          b5p1 = a4
          block = 5
          continue
        }
        case 5: {
          return b5p0
        }`, `        case 4: {
          return b4p0
        }`);
  }
  return text.slice(0, start) + body + text.slice(end);
};

const temp = await mkdtemp(join(tmpdir(), "effect4-interrupt-boundary-"));
const interrupted = 'done\t{"interrupted":true}';
const outside = "decide\t1000009\tfalse";
const restoredRows = goldenRows.filter(row => row !== outside);
const successfulPrefix = restoredRows.slice(0, -1);
assert.equal(goldenRows.filter(row => row === outside).length, 1);
const unmaskedRows = ["enter\t1", "op\tacquire\t5", "answer\tacquire\t5",
  "decide\t1000005\ttrue", 'leave\t1\t{"interrupted":true}',
  'finalizer\t1\t{"interrupted":true}', "op\trelease\t5", "answer\trelease\t[]", interrupted];
const summaries = [];
try {
  for (const variant of [
    { name: "baseline", direct: false, mask: false, returns: false },
    { name: "direct_without_mask", direct: true, mask: false, returns: false },
    { name: "direct_outer_mask", direct: true, mask: true, returns: false },
    { name: "baseline_return", direct: false, mask: false, returns: true },
    { name: "direct_outer_mask_return", direct: true, mask: true, returns: true }
  ]) {
    const dir = join(temp, variant.name);
    await mkdir(dir);
    await symlink(nodeModules, join(dir, "node_modules"), "dir");
    for (const file of files) await writeFile(join(dir, file),
      file === "flow-fixture.ts" ? changeMaskedProgram(variant.mask, variant.returns) :
      file === "interrupt-tail.ts" ? instrumentTail(variant.direct) : baseline[file]);
    let previousRows;
    for (const threshold of [1000000, 3]) {
      const child = spawnSync(process.execPath,
        ["--experimental-strip-types", "--no-warnings", join(dir, "interrupt-tail.ts")], {
          cwd: dir, encoding: "utf8", timeout: 30000, maxBuffer: 4 * 1024 * 1024,
          env: { ...process.env, EFFECT4_PROGRAM: "interruptMasked", EFFECT4_TAPE: "1000005:1",
            EFFECT4_MAX_OPS: String(threshold), EFFECT4_BUDGET: "100000",
            EFFECT4_EXPECT_YIELDS: threshold === 3 ? "1" : "0" }
        });
      assert.equal(child.status, 0, child.stderr || String(child.error));
      const report = JSON.parse(child.stdout);
      assert.equal(report.tracerDefect, null);
      assert.equal(report.maxOpsBeforeYield, threshold);
      assert(threshold !== 3 || report.yields > 0, "Low threshold did not exercise yielding");
      if (previousRows) assert.deepEqual(report.rows, previousRows, "Threshold changed observations");
      previousRows = report.rows;
      const expected = variant.mask ? restoredRows :
        variant.direct ? unmaskedRows :
        variant.returns ? [...successfulPrefix, 'done\t{"success":5}'] : goldenRows;
      assert.deepEqual(report.rows, expected, `${variant.name}: unexpected complete trace`);
      const first = report.deliveryDiagnostics[0];
      assert.deepEqual(first, { site: 1000005, answered: true, modelMasked: true,
        interruptible: !variant.mask, interrupted: false, deferred: false,
        afterInterrupted: variant.direct, afterDeferred: variant.direct && !variant.mask });
      if (variant.mask) {
        assert.equal(report.deliveryDiagnostics.length, 2);
        assert.deepEqual(report.deliveryDiagnostics[1], { site: 1000002, answered: false,
          modelMasked: true, interruptible: false, interrupted: true, deferred: false,
          afterInterrupted: true, afterDeferred: false });
        assert(!report.rows.includes(outside), "Restoration read another decision");
        assert.equal(report.exitTag, "Failure");
      }
      if (variant.name === "baseline") assert.deepEqual(agreement(report.rows),
        { outcome: true, m1: true, m2: true });
      if (variant.name === "direct_outer_mask") assert.deepEqual(agreement(report.rows),
        { outcome: true, m1: true, m2: false });
      if (variant.name === "direct_without_mask") assert.deepEqual(agreement(report.rows),
        { outcome: true, m1: false, m2: false });
      if (variant.name === "baseline_return") assert.equal(report.exitTag, "Success");
      summaries.push({ variant: variant.name, threshold, yields: report.yields,
        rows: report.rows, delivery: report.deliveryDiagnostics,
        historicalGoldenAgreement: agreement(report.rows) });
    }
  }
  console.log(JSON.stringify({ evidence: "finite historical counterexample and real runtime controls",
    counterexamples: ["E4-FLOW-CE-024", "E4-FLOW-CE-025"], historicalRevision: revision,
    effect: packageInfo.version, upstream, sourceSha256: sourceHash, executedInternalSha256: runtimeHash,
    node: process.version, platform: process.platform, arch: process.arch,
    command: "node harness/trace/interrupt-mask-boundary.mjs <node_modules/effect>", inputs, summaries }, null, 2));
} finally {
  await rm(temp, { recursive: true, force: true });
}
