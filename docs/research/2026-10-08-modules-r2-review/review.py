#!/usr/bin/env python3
"""Reproduce MODULES-r2 review findings without changing the reviewed declarations."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PACKET = ROOT / "docs/research/2026-10-08-seat-MODULES-r2"
ENV = dict(os.environ, LEAN_NUM_THREADS="3", PYTHONDONTWRITEBYTECODE="1")
REPORT = {"kind": "finite-design-review", "reviewed_commit": "3af74a28", "commands": [], "checks": {}}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save() -> None:
    (HERE / "results.json").write_text(json.dumps(REPORT, indent=2) + "\n")


def check(name: str, actual, expected) -> None:
    REPORT["checks"][name] = {"actual": actual, "expected": expected, "pass": actual == expected}
    save()
    assert actual == expected, (name, actual, expected)


def run(args: list[str], expected: int = 0) -> subprocess.CompletedProcess:
    start = time.monotonic()
    result = subprocess.run(args, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=180)
    REPORT["commands"].append({"argv": args, "exit": result.returncode,
        "seconds": round(time.monotonic() - start, 3), "stdout": result.stdout, "stderr": result.stderr})
    save()
    print(f"exit={result.returncode}: {' '.join(args)}", flush=True)
    if result.returncode != expected:
        raise RuntimeError(result.stdout + result.stderr)
    return result


files = [p for p in PACKET.iterdir() if p.is_file()]
files += [ROOT / "docs/research/2026-10-08-seat-MODULES-r2.md"]
original = {str(p.relative_to(ROOT)): digest(p) for p in files}
REPORT["submitted_inputs"] = original
REPORT["tools"] = {
    "effect": json.loads((ROOT / "harness/truth/node_modules/effect/package.json").read_text())["version"],
    "tsgo": json.loads((ROOT / "ts/eff/node_modules/@typescript/native-preview/package.json").read_text())["version"],
    "bun": run(["bun", "--version"]).stdout.strip(),
    "lean": run(["lake", "env", "lean", "--version"]).stdout.strip(),
}
check("effect-pin", REPORT["tools"]["effect"], "4.0.0-rc.112")
check("compiler-pin", REPORT["tools"]["tsgo"], "7.0.0-dev.20260629.1")
run(["lake", "build", "Effect4", "Test.Program.SemaphoreScenarios",
     "Effect4.Laws.Modules.Reading", "Effect4.Laws.Schema.Codec"])
for name in ["StepData", "BatchLatch", "TyModel"]:
    run(["lake", "env", "lean", "-DwarningAsError=true", str((PACKET / f"{name}.lean").relative_to(ROOT))])

baseline = run(["python3", str((PACKET / "native.py").relative_to(ROOT))], expected=2)
check("coalesced-batch-agrees", "batch-coalesced: pass" in baseline.stdout, True)
check("original-batch-stays-candidate", "batch: candidate" in baseline.stdout, True)
REPORT["native_baseline"] = json.loads((PACKET / "native-results.json").read_text())
run(["python3", str((PACKET / "native.py").relative_to(ROOT)), "--self-test"])

source = (PACKET / "TyModel.lean").read_text()
prefix = source[:source.index("/-! ## Latch's cell, declared once -/")] + "\nend TyModel\n"
with tempfile.TemporaryDirectory(prefix="modules-r2-lean-review-") as temp:
    scratch = Path(temp)
    control = scratch / "TyControls.lean"
    control.write_text(prefix + (HERE / "ty-controls.inc.lean").read_text())
    observation = run(["lake", "env", "lean", "-DwarningAsError=true", str(control)])
    check("carrier-control-results", observation.stdout.strip().splitlines(), [
        "none", "true", "false", "false", 'some "handle: an identity needs its table"',
        "true", "true", "false", "true"])
    duplicate = scratch / "Duplicate.lean"
    duplicate.write_text(prefix + (HERE / "duplicate.inc.lean").read_text())
    rejected = run(["lake", "env", "lean", "-DwarningAsError=true", str(duplicate)], expected=1)
    check("duplicate-rejected-at-inverse-proof", "unsolved goals" in rejected.stdout and
          "{ a := a✝, b := a✝ } = { a := a✝, b := b✝ }" in rejected.stdout, True)

run(["python3", str((HERE / "native-controls.py").relative_to(ROOT))])
check("submitted-packet-unchanged", {str(p.relative_to(ROOT)): digest(p) for p in files}, original)
REPORT["support_inputs"] = {name: digest(ROOT / name) for name in [
    "harness/truth/generated/pDefsOdd.ts", "harness/truth/prelude.ts", "harness/truth/tsconfig.json",
    "vendor/effect-4.0.0-rc.112/src/internal/effect.ts", "ts/eff/package.json", "lean-toolchain"]}
REPORT["review_inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in HERE.iterdir()
    if p.is_file() and p.name != "results.json"}
save()
print("All review controls reproduce. Expected design defects remain recorded.")
