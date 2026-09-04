// Finite rc.112 witness for E4-TARGET-CE-019. This is not a host bridge proof.
// Usage: node region-simulation-boundary.mjs /absolute/path/to/node_modules/effect
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const packageRoot = process.argv[2];
assert(packageRoot, "Pass the installed effect package directory as the only argument");
assert.equal(process.argv.length, 3, "Expected one package-directory argument");
const packagePath = resolve(packageRoot);
const packageInfo = JSON.parse(await readFile(resolve(packagePath, "package.json"), "utf8"));
assert.equal(packageInfo.version, "4.0.0-rc.112", "Effect version drift");
const expectedSource = "0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0";
const sha256 = bytes => createHash("sha256").update(bytes).digest("hex");
const sourceHash = sha256(await readFile(resolve(packagePath, "src/internal/effect.ts")));
const vendoredSource = fileURLToPath(new URL(
  "../../../vendor/effect-4.0.0-rc.112/src/internal/effect.ts", import.meta.url));
assert.equal(sourceHash, expectedSource, "Installed source drift");
assert.equal(sha256(await readFile(vendoredSource)), expectedSource, "Vendored source drift");
const runtimeHash = sha256(await readFile(resolve(packagePath, "dist/internal/effect.js")));
const Effect = await import(pathToFileURL(resolve(packagePath, "dist/Effect.js")).href);

const observe = exit => exit._tag === "Success"
  ? { tag: "success", value: exit.value }
  : { tag: "failure", reasons: exit.cause.reasons.map(reason =>
      reason._tag === "Fail" ? [reason._tag, reason.error] :
      reason._tag === "Die" ? [reason._tag, reason.defect] : [reason._tag]) };

console.log(JSON.stringify({ package: packageInfo.version, sourceSha256: sourceHash,
  executedInternalSha256: runtimeHash, evidence: "finite controls" }));

// The die case respects acquireRelease's never error row. The fail case is
// deliberately JavaScript-only: it is outside that public TypeScript signature.
for (const mode of ["success", "die", "fail"]) {
  const rows = [];
  const release = (name, exit) => Effect.suspend(() => {
    rows.push({ name, closing: observe(exit) });
    return name !== "B" || mode === "success" ? Effect.void :
      mode === "die" ? Effect.die("B cleanup") : Effect.fail("B cleanup");
  });
  const scoped = Effect.scoped(Effect.gen(function*() {
    yield* Effect.acquireRelease(Effect.succeed("A"), release);
    yield* Effect.acquireRelease(Effect.succeed("B"), release);
    return 5;
  }));
  const scopedResult = observe(Effect.runSyncExit(scoped));
  const scopedRows = rows.splice(0);
  const nested = Effect.onExit(
    Effect.onExit(Effect.succeed(5), exit => release("B", exit)),
    exit => release("A", exit));
  const nestedResult = observe(Effect.runSyncExit(nested));
  const success = { tag: "success", value: 5 };
  const failure = { tag: "failure", reasons: [[mode === "die" ? "Die" : "Fail", "B cleanup"]] };
  assert.deepEqual(scopedRows, [{ name: "B", closing: success }, { name: "A", closing: success }]);
  assert.deepEqual(rows, [{ name: "B", closing: success },
    { name: "A", closing: mode === "success" ? success : failure }]);
  assert.deepEqual(scopedResult, mode === "success" ? success : failure);
  assert.deepEqual(nestedResult, scopedResult);
  console.log(JSON.stringify({ mode, scoped: { rows: scopedRows, result: scopedResult },
    nestedOnExit: { rows, result: nestedResult } }));
}
