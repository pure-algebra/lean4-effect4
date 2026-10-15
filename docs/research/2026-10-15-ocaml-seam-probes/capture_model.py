#!/usr/bin/env python3
"""Run the finite model reader and retain its direct import identities.

Run through scratch/lean-slot.sh. This does not rebuild imported modules.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
IMPORTS = [
    "Effect4/Schema/Modeled",
    "Effect4/Program/Typed",
    "Effect4/Store/Domain/Canonical",
]
SOURCES = [
    "lean-toolchain",
    "src/Effect4/Schema/Modeled.lean",
    "src/Effect4/Program/Typed.lean",
    "src/Effect4/Store/Domain/Canonical.lean",
    "src/Effect4/Store/Carrier/Image.lean",
    "src/Effect4/Store/Carrier/Image/Containers.lean",
    "src/Effect4/Program/TyCore.lean",
    str((HERE / "ModelProbe.lean").relative_to(ROOT)),
]


def command(argv):
    result = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True)
    return {"argv": argv, "exit": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def hashes(paths):
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in paths}


artifacts = [f".lake/build/lib/lean/{name}{suffix}"
             for name in IMPORTS for suffix in (".olean", ".trace")]
before = hashes(SOURCES + artifacts)
head_before = command(["git", "rev-parse", "HEAD"])
run = command(["lake", "env", "lean", "-M4096", "--run",
               str((HERE / "ModelProbe.lean").relative_to(ROOT))])
(HERE / "model-probe.log").write_text(run["stdout"] + run["stderr"])
after = hashes(SOURCES + artifacts)
record = {
    "captured_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Finite readers using existing compiled imports; no fresh build or theorem audit",
    "head_before": head_before,
    "head_after": command(["git", "rev-parse", "HEAD"]),
    "lean_version": command(["lake", "env", "lean", "--version"]),
    "run": run,
    "input_sha256_before": before,
    "input_sha256_after": after,
    "inputs_unchanged_during_run": before == after,
}
(HERE / "model-provenance.json").write_text(json.dumps(record, indent=2) + "\n")
assert run["exit"] == 0, run
assert before == after, "Model inputs changed during execution"
assert "MEASURE finite_model_checks=12" in run["stdout"]
print("PASS finite model probe; direct compiled imports and source hashes retained")
