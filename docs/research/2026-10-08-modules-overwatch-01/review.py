#!/usr/bin/env python3
"""Reproduce the first module overwatch against the pinned L1 sources."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = "a2d1dc7aa7e8bfea426b71cb7e00f5e821dc08a9"
ENV = dict(os.environ, LEAN_NUM_THREADS="3", PYTHONDONTWRITEBYTECODE="1")
REPORT = {"kind": "finite-overwatch-review", "reviewed_commit": BASE,
          "commands": [], "checks": {}}
SOURCES = ["src/Effect4/Schema/Modeled.lean", "src/Effect4/Schema/Modeled/Derive.lean",
 "src/Effect4/Laws/Schema/Modeled.lean", "src/Effect4/Store/Carrier/Image/Record.lean",
 "Test/Schema/Modeled.lean", "Test/Audit/AxiomGate.lean", "tools/Tools/SemanticsRegistry.lean",
 "docs/research/2026-10-08-seat-MODULES-r3/native.py", "docs/core/decisions.md"]

def digest(data):
    return hashlib.sha256(data).hexdigest()

def save():
    (HERE / "results.json").write_text(json.dumps(REPORT, indent=2) + "\n")

def check(name, condition):
    REPORT["checks"][name] = bool(condition)
    save()
    if not condition:
        raise RuntimeError(name)

def run(args, expected=0):
    start = time.monotonic()
    r = subprocess.run(args, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=180)
    REPORT["commands"].append({"argv": args, "exit": r.returncode,
      "seconds": round(time.monotonic()-start, 3), "stdout": r.stdout, "stderr": r.stderr})
    save()
    print(f"exit={r.returncode}: {' '.join(args)}", flush=True)
    if r.returncode != expected:
        raise RuntimeError(r.stdout+r.stderr)
    return r

REPORT["source_digests"] = {p:digest((ROOT/p).read_bytes()) for p in SOURCES}
for p in SOURCES:
    frozen = subprocess.run(["git", "show", f"{BASE}:{p}"], cwd=ROOT,
                            check=True, capture_output=True).stdout
    check(f"pinned:{p}", digest(frozen) == REPORT["source_digests"][p])
REPORT["tools"] = {"lean": run(["lake", "env", "lean", "--version"]).stdout.strip()}
run(["lake", "build", "Effect4.Schema.Modeled.Derive", "Effect4.Laws.Schema.Modeled",
     "Test.Schema.Modeled", "Tools.SemanticsRegistry"])
for name in ["positive", "opaque-composed", "audit"]:
    run(["lake", "env", "lean", "-DwarningAsError=true", str(HERE/f"{name}.lean")])
opaque = run(["lake", "env", "lean", "-DwarningAsError=true", str(HERE/"opaque.lean")], 1)
check("opaque-valid-instance-fails-at-computed-check",
      "Tactic `decide` failed" in opaque.stdout and "Model.refusal Holder.modeledTy" in opaque.stdout
      and "failed to synthesize" not in opaque.stdout)
collision = run(["lake", "env", "lean", "-DwarningAsError=true", str(HERE/"collision.lean")], 1)
check("collision-leaves-helpers-in-failed-environment",
      "has already been declared" in collision.stdout and
      "DeriveCollisionReview.Token.modeled_checked :" in collision.stdout and
      "DeriveCollisionReview.Token.modeledToC (s : Token)" in collision.stdout)
run(["python3", "docs/research/2026-10-08-seat-MODULES-r3/native.py"])
run(["python3", "docs/research/2026-10-08-seat-MODULES-r3/native.py", "--self-test"])
REPORT["native_baseline"] = json.loads((ROOT/"docs/research/2026-10-08-seat-MODULES-r3/native-results.json").read_text())
check("reviewed-source-unchanged",
      REPORT["source_digests"] == {p:digest((ROOT/p).read_bytes()) for p in SOURCES})
REPORT["probe_digests"] = {p.name:digest(p.read_bytes()) for p in HERE.iterdir()
                           if p.is_file() and p.name != "results.json"}
save()
print("Overwatch controls reproduce; the deriving failures remain findings, not repaired code.")
