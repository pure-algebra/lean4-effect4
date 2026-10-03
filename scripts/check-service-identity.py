#!/usr/bin/env python3
"""Finite checks of actual API-emitted service modules; no general lowering claim.

Run after the changed Lean dependencies are built, in the serialized compiler lane:
    python3 scripts/check-service-identity.py --out .lake/service-identity
The driver derives ordinary fixture types through Api.emitModule. This script checks
both shipped annotations and independent initializer inference with pinned tsgo, then
runs the emitted programs with pinned Effect under Bun. No dependencies are installed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent

INFERENCE = '''import type { Effect, Scope } from "effect"
import type * as P from "./inferred.ts"
type R<T> = T extends Effect.Effect<infer _A, infer _E, infer Req> ? Req : never
type A<T> = T extends Effect.Effect<infer Answer, infer _E, infer _R> ? Answer : never
type Same<X, Y> = [X] extends [Y] ? ([Y] extends [X] ? true : false) : false
const first: Same<R<typeof P.first>, "k4_4"> = true
const both: Same<R<typeof P.both>, "k4_4" | "k5_4"> = true
const remains: Same<R<typeof P.wrongProvision>, "k5_4"> = true
const correct: Same<R<typeof P.correct>, never> = true
const sameKey: Same<R<typeof P.sameKey>, never> = true
const scope: Same<R<typeof P.scopeService>, Scope.Scope> = true
const scoped: Same<R<typeof P.scopedLookup>, never> = true
const unknownKey: Same<R<typeof P.customUnknown>, "k6_99"> = true
const unknownAnswer: Same<A<typeof P.customUnknown>, unknown> = true
const notAny: 0 extends (1 & A<typeof P.customUnknown>) ? true : false = false
export { first, both, remains, correct, sameKey, scope, scoped, unknownKey, unknownAnswer, notAny }
'''

# JavaScript intentionally crosses the runtime boundary for the unprovided service.
# Its TypeScript requirement is checked independently above; no production cast hides it.
RUNTIME = '''import assert from "node:assert/strict"
import { Cause, Effect, Exit } from "effect"
import * as P from "./positive.ts"
assert.equal(await Effect.runPromise(P.correct), 9)
assert.equal(await Effect.runPromise(P.sameKey), 7)
assert.equal(await Effect.runPromise(P.scopedLookup), 42)
const missing = await Effect.runPromiseExit(P.wrongProvision)
assert.equal(Exit.isFailure(missing), true)
assert.equal(Exit.hasDies(missing), true)
assert.match(Cause.pretty(missing.cause), /Service not found: k5_4/)
console.log(JSON.stringify({ correct: 9, sameKey: 7, scopedLookup: 42, missing: "k5_4" }))
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / ".lake/service-identity")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    modules = ROOT / "ts/eff/node_modules"
    manifest = json.loads((ROOT / "ts/eff/package.json").read_text())
    versions = {}
    for package, expected in [
        ("@typescript/native-preview", manifest["devDependencies"]["@typescript/native-preview"]),
        ("effect", manifest["dependencies"]["effect"]),
    ]:
        actual = json.loads((modules / package / "package.json").read_text())["version"]
        if actual != expected:
            raise RuntimeError(f"{package}: installed {actual}, pinned {expected}")
        versions[package] = actual
    node, bun, lake = (shutil.which(tool) for tool in ("node", "bun", "lake"))
    if not all((node, bun, lake)):
        raise RuntimeError("node, bun and lake must already be installed")
    link = out / "node_modules"
    if link.exists() or link.is_symlink():
        if link.resolve() != modules.resolve():
            raise RuntimeError(f"{link} does not resolve to the pinned dependencies")
    else:
        link.symlink_to(modules, target_is_directory=True)
    report = {"claim": "finite compiler/runtime controls over actual Lean API emissions",
              "versions": versions, "commands": [], "passed": False}

    def run(command, timeout):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        report["commands"].append({"argv": [str(arg) for arg in command],
                                   "exit": result.returncode, "stdout": result.stdout,
                                   "stderr": result.stderr})
        return result

    try:
        bun_version = run([bun, "--version"], 10)
        if bun_version.returncode:
            raise RuntimeError("could not read Bun version")
        report["versions"]["bun"] = bun_version.stdout.strip()
        driver = ROOT / "tools/TestSupport/ServiceIdentity.lean"
        emitted = run([lake, "env", "lean", "-DwarningAsError=true", "-M4096", "--run", str(driver), str(out)], 120)
        if emitted.returncode:
            raise RuntimeError(f"Lean fixture emission failed:\n{emitted.stdout}{emitted.stderr}")
        (out / "inference.ts").write_text(INFERENCE)
        (out / "runtime.mjs").write_text(RUNTIME)
        options = json.loads((ROOT / "ts/eff/tsconfig.json").read_text())["compilerOptions"]
        compiler = [node, str(modules / "@typescript/native-preview/bin/tsgo"), "--pretty", "false", "--noEmit"]
        for name, files, expected in [
            ("positive", ["positive.ts", "inferred.ts", "inference.ts"], []),
            ("false-closed", ["false-closed.ts"], [2375]),
            ("wrong-brand", ["wrong-brand.ts"], [2375]),
        ]:
            config = out / f"tsconfig.{name}.json"
            config.write_text(json.dumps({"compilerOptions": options, "files": files}, indent=2) + "\n")
            checked = run(compiler + ["-p", str(config)], 120)
            output = checked.stdout + checked.stderr
            diagnostics = [int(code) for code in re.findall(r"error TS(\d+):", output)]
            if diagnostics != expected or (checked.returncode != 0) != bool(expected):
                raise RuntimeError(f"{name}: expected codes {expected}, got {diagnostics}, exit {checked.returncode}:\n"
                                   f"{checked.stdout}{checked.stderr}")
            if expected:
                locations = re.findall(r"^(.+)\(\d+,\d+\): error TS2375:", output, re.MULTILINE)
                if len(locations) != 1 or Path(locations[0]).name != f"{name}.ts":
                    raise RuntimeError(f"{name}: expected the refusal in its emitted declaration:\n{output}")
                identities = ['"k5_4"', "never"] if name == "false-closed" else ['"k4_4"', '"k5_4"']
                if not all(identity in output for identity in identities):
                    raise RuntimeError(f"{name}: TS2375 did not identify the expected requirement mismatch:\n{output}")
        runtime = run([bun, str(out / "runtime.mjs")], 30)
        if runtime.returncode:
            raise RuntimeError(f"runtime controls failed:\n{runtime.stdout}{runtime.stderr}")
        report["emitted_sha256"] = {
            name: hashlib.sha256((out / name).read_bytes()).hexdigest()
            for name in ("positive.ts", "inferred.ts", "false-closed.ts", "wrong-brand.ts")
        }
        report["passed"] = True
        print("PASS service identity: checked API emissions, inferred requirements, two TS2375 controls, four runtime outcomes")
        return 0
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"FAIL service identity: {error}", file=sys.stderr)
        sys.exit(1)
