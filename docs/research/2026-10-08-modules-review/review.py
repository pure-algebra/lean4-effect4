#!/usr/bin/env python3
"""Finite MODULES design review at 29f369ca; no production source changes."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PACKET = ROOT / "docs/research/2026-10-08-seat-MODULES"
ENV = dict(os.environ, LEAN_NUM_THREADS="3")
REPORT = {"kind": "finite-design-review", "reviewed_commit": "29f369ca8acc5ccef2632375357f0bf7a2c4ac22", "commands": [], "checks": {}}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save() -> None:
    (HERE / "results.json").write_text(json.dumps(REPORT, indent=2) + "\n")


def run(args: list[str], cwd: Path = ROOT, require_ok: bool = True) -> subprocess.CompletedProcess:
    start = time.monotonic()
    result = subprocess.run(args, cwd=cwd, env=ENV, text=True, capture_output=True, timeout=180)
    REPORT["commands"].append({"argv": args, "cwd": str(cwd), "exit": result.returncode,
        "seconds": round(time.monotonic() - start, 3), "stdout": result.stdout, "stderr": result.stderr})
    save()
    print(f"exit={result.returncode}: {' '.join(args)}", flush=True)
    if require_ok and result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result


def check(key: str, actual, expected) -> None:
    REPORT["checks"][key] = {"actual": actual, "expected": expected, "pass": actual == expected}
    save()
    assert actual == expected, (key, actual, expected)


original = {str(p.relative_to(ROOT)): digest(p) for p in PACKET.rglob("*") if p.is_file()}
REPORT["original_inputs"] = original
REPORT["support_inputs"] = {name: digest(ROOT / name) for name in [
    "harness/truth/generated/pDefsOdd.ts", "harness/truth/prelude.ts", "harness/truth/tsconfig.json",
    "vendor/effect-4.0.0-rc.112/src/internal/effect.ts", "ts/eff/package.json", "lean-toolchain"]}
REPORT["tools"] = {
    "effect": json.loads((ROOT / "harness/truth/node_modules/effect/package.json").read_text())["version"],
    "compiler": json.loads((ROOT / "ts/eff/node_modules/@typescript/native-preview/package.json").read_text())["version"],
    "bun": run(["bun", "--version"]).stdout.strip(),
    "lean": run(["lake", "env", "lean", "--version"]).stdout.strip(),
}
check("effect-pin", REPORT["tools"]["effect"], "4.0.0-rc.112")
check("compiler-pin", REPORT["tools"]["compiler"], "7.0.0-dev.20260629.1")
run(["lake", "build", "Effect4", "Test.Program.SemaphoreScenarios", "Effect4.Laws.Modules.Reading"])
for name in ["LatchProbe", "DenProbe", "LatchSim", "StepAlgProbe", "StepText"]:
    run(["lake", "env", "lean", "-DwarningAsError=true", str((PACKET / f"{name}.lean").relative_to(ROOT))])
for name in ["StepFrame", "Answerers", "LatchControls"]:
    probe = run(["lake", "env", "lean", "-DwarningAsError=true", str((HERE / f"{name}.lean").relative_to(ROOT))])
    if name == "Answerers":
        check("answerer-controls", probe.stdout.strip().splitlines(),
              ["true", "true", "some true", "some true", "some false", "false", "true", "true", "false"])

original_run = run(["bash", str((PACKET / "pin/run.sh").relative_to(ROOT))])
check("original-native-fixtures", all(x in original_run.stdout for x in [
    "d1 ours: [3,1,2]   Effect's: [3,1,2]", "d2 ours: [3,1,2]   Effect's: [3,1,2]",
    "d3 ours: [true,[3]]   Effect's: [true,[3]]"]), True)

with tempfile.TemporaryDirectory(prefix="modules-review-host-") as temp:
    work = Path(temp)
    (work / "node_modules").symlink_to(ROOT / "harness/truth/node_modules", target_is_directory=True)
    imports = (ROOT / "harness/truth/generated/pDefsOdd.ts").read_text().splitlines()[2:4]
    imports[0] = imports[0].replace("import { Cause,", "import { Latch, Cause,")
    imports[1] = imports[1].replace('"../prelude.ts"', json.dumps(str(ROOT / "harness/truth/prelude.ts")))
    footer = '''const result = await Effect.runPromiseExit(main)
console.log(JSON.stringify(result._tag === "Success"
  ? { _tag: "Success", value: result.value }
  : { _tag: "Failure", cause: String(result.cause) }))
'''
    bodies = {f"{client}-{side}": PACKET / f"pin/{client}-{side}.ts"
              for client in ["d1", "d2", "d3"] for side in ["lib", "pin"]}
    bodies.update({f"batch-{side}": HERE / f"batch-{side}.body.ts" for side in ["lib", "pin"]})
    for name, path in bodies.items():
        (work / f"{name}.ts").write_text("\n".join(imports) + "\n" + path.read_text() + "\n" + footer)
    config = {"extends": str(ROOT / "harness/truth/tsconfig.json"),
              "files": [f"{name}.ts" for name in bodies], "include": [], "exclude": []}
    (work / "tsconfig.json").write_text(json.dumps(config, indent=2))
    REPORT["emitted_targets"] = {f"{name}.ts": digest(work / f"{name}.ts") for name in bodies}
    REPORT["target_config"] = config
    save()
    tsgo = str(ROOT / "ts/eff/node_modules/.bin/tsgo")
    run([tsgo, "--noEmit", "-p", str(work / "tsconfig.json")])
    results = {}
    for name in bodies:
        results[name] = json.loads(run(["bun", "run", str(work / f"{name}.ts")]).stdout)
    for client, value in [("d1", [3, 1, 2]), ("d2", [3, 1, 2]), ("d3", [True, [3]])]:
        for side in ["lib", "pin"]:
            check(f"native-{client}-{side}", results[f"{client}-{side}"], {"_tag": "Success", "value": value})
    check("batch-library", results["batch-lib"], {"_tag": "Success", "value": [1, 9, 2]})
    check("batch-native", results["batch-pin"], {"_tag": "Success", "value": [1, 2, 9]})

    # Attack the submitted script in a separate replica, leaving its packet untouched.
    fake = work / "replica"
    pin = fake / "docs/research/2026-10-08-seat-MODULES/pin"
    pin.mkdir(parents=True)
    for path in (PACKET / "pin").iterdir():
        if path.is_file():
            shutil.copyfile(path, pin / path.name)
    truth = fake / "harness/truth"
    truth.parent.mkdir(parents=True)
    truth.symlink_to(ROOT / "harness/truth", target_is_directory=True)
    script = "docs/research/2026-10-08-seat-MODULES/pin/run.sh"
    check("replica-baseline-exit", run(["bash", script], cwd=fake).returncode, 0)
    (pin / "d1-lib.ts").write_text("export const main = Effect.succeed([999])\n")
    wrong = run(["bash", script], cwd=fake, require_ok=False)
    check("wrong-result-script-exit", wrong.returncode, 0)
    check("wrong-result-was-executed", "d1 ours: [999]" in wrong.stdout, True)
    (pin / "d1-lib.ts").write_text('throw new Error("REVIEW_INJECTED_CRASH")\nexport const main = Effect.succeed([999])\n')
    crash = run(["bash", script], cwd=fake, require_ok=False)
    check("crash-script-exit", crash.returncode, 0)
    check("crash-was-executed", "REVIEW_INJECTED_CRASH" in crash.stderr, True)
    shutil.copyfile(PACKET / "pin/d1-lib.ts", pin / "d1-lib.ts")
    restored = run(["bash", script], cwd=fake)
    check("restored-script-exit", restored.returncode, 0)
    check("restored-script-output", restored.stdout, original_run.stdout)

check("submitted-packet-unchanged", {str(p.relative_to(ROOT)): digest(p) for p in PACKET.rglob("*") if p.is_file()}, original)
REPORT["review_inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in HERE.iterdir()
                          if p.is_file() and p.name not in ["results.json"]}
save()
print("All finite review controls passed; retained results.json.")
