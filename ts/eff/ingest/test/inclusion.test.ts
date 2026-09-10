import { expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
import { mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { fileURLToPath } from "node:url"

const checker = fileURLToPath(new URL("../check-corpus.ts", import.meta.url))
const ck = fileURLToPath(new URL("../ck.ts", import.meta.url))
const oxc = fileURLToPath(new URL("../oxc.ts", import.meta.url))

// Exercise the actual command in an isolated process. Only the recognizers' returned
// verdicts are varied: no copy of the gate or its comparison rule serves as the oracle.
const run = (mutation = "none", expression = "Effect.succeed(42)",
  oracle: unknown = ["succeed", ["lit", ["nat", 42]]], mode = "inclusion-batch") => {
  const directory = mkdtempSync(join(tmpdir(), "effect4-inclusion-test-"))
  try {
    writeFileSync(join(directory, "sample.ts"), expression + "\n")
    writeFileSync(join(directory, "sample.json"), JSON.stringify(oracle))
    const script = `
      import { mock } from "bun:test";
      const ck = await import(${JSON.stringify(ck)});
      const oxc = await import(${JSON.stringify(oxc)});
      const readCk = ck.recognizeSource, readOxc = oxc.recognizeSource;
      const mutation = ${JSON.stringify(mutation)};
      const change = (verdicts, engine, file) => {
        const refusal = (code = "E-ARG-DYNAMIC") => ({ kind: "refusal", unit: verdicts[0].unit,
          code, detail: "controlled refusal" });
        if (mutation === "all-refused") return [refusal()];
        if (file !== "sample.ts") return verdicts;
        if (mutation === "asymmetric" && engine === "oxc") {
          return [refusal()];
        }
        if (mutation === "conflicting") return [refusal(engine === "ck" ? "E-ARG-DYNAMIC" : "E-IMPORT-OPAQUE")];
        if (mutation === "conflicting-detail") return [{ ...refusal(), detail: engine }];
        if (mutation === "missing") return [];
        if (mutation === "absent") return undefined;
        if (mutation === "multiple") return [verdicts[0], verdicts[0]];
        if (mutation === "malformed") return [{ kind: "refusal" }];
        if (mutation === "unknown-code") return [refusal("E-NOT-A-REFUSAL-CODE")];
        if (mutation === "unknown-kind") return [{ kind: "accepted", unit: verdicts[0].unit }];
        return verdicts;
      };
      mock.module(${JSON.stringify(ck)}, () => ({ ...ck,
        recognizeSource: (source, file) => change(readCk(source, file), "ck", file) }));
      mock.module(${JSON.stringify(oxc)}, () => ({ ...oxc,
        recognizeSource: (source, file) => change(readOxc(source, file), "oxc", file) }));
      process.argv = [process.execPath, ${JSON.stringify(checker)}, ${JSON.stringify(mode)}, ${JSON.stringify(directory)}];
      await import(${JSON.stringify(checker)});
    `
    return spawnSync(process.execPath, ["--eval", script], { encoding: "utf8", timeout: 30_000 })
  } finally {
    rmSync(directory, { recursive: true })
  }
}

test("the inclusion command rejects one reader accepting while the other refuses", () => {
  const result = run("asymmetric")
  expect(result.error).toBeUndefined()
  expect(result.status).not.toBe(0)
  expect(result.stderr).toContain("engines disagree")
})

test("the inclusion command requires its independent positive control to lift", () => {
  const result = run("all-refused")
  expect(result.error).toBeUndefined()
  expect(result.status).not.toBe(0)
  expect(result.stderr).toContain("positive control")
})

for (const [mutation, diagnostic] of [
  ["conflicting", "engines disagree"],
  ["conflicting-detail", "engines disagree"],
  ["missing", "exactly one verdict"],
  ["absent", "exactly one verdict"],
  ["multiple", "exactly one verdict"],
  ["malformed", "malformed verdict"],
  ["unknown-kind", "malformed verdict"],
  ["unknown-code", "malformed verdict"],
] as const) {
  test(`the inclusion command rejects ${mutation} verdicts`, () => {
    const result = run(mutation)
    expect(result.error).toBeUndefined()
    expect(result.status).not.toBe(0)
    expect(result.stderr).toContain(diagnostic)
  })
}

test("the actual inclusion parent reports its admitted scalar fixture", () => {
  const result = run("none", "Effect.succeed(42)", ["succeed", ["lit", ["nat", 42]]], "inclusion")
  expect(result.error).toBeUndefined()
  expect(result.status).toBe(0)
  expect(result.stderr).toBe("")
  expect(result.stdout).toContain("PASS inclusion: 1 printed modules, 1 lifted")
})

test("agreed foreign refusals remain reportable without entering the measured positive count", () => {
  const result = run("none", "Effect.fail(succ(1))",
    ["fail", ["app", "succ", ["cons", ["lit", ["nat", 1]], ["nil"]]]], "inclusion")
  expect(result.error).toBeUndefined()
  expect(result.status).toBe(0)
  expect(result.stderr).toBe("")
  expect(result.stdout).toContain("PASS inclusion: 1 printed modules, 0 lifted")
  expect(result.stdout).toContain("refused ck=E-FAIL-NOT-DOCUMENTED oxc=E-FAIL-NOT-DOCUMENTED")
})

test("the inclusion command compares service keys up to their documented renumbering", () => {
  const result = run("none", 'Effect.service(Context.Service<number>("k10_4"))',
    ["service", { name: { value: 10 }, service: { value: 4 } }])
  expect(result.error).toBeUndefined()
  expect(result.status).toBe(0)
  expect(result.stderr).toBe("")
  expect(result.stdout).toBe("sample\tincluded (foreign key base 4)\n")
})

test("an incorrect lifted meaning makes the inclusion parent fail", () => {
  const result = run("none", "Effect.succeed(42)", ["succeed", ["lit", ["nat", 41]]], "inclusion")
  expect(result.error).toBeUndefined()
  expect(result.status).not.toBe(0)
  expect(result.stdout).not.toContain("PASS inclusion")
  expect(result.stderr).toContain("different program up to key renumbering")
})
