#!/usr/bin/env python3
"""Reproduce the second module overwatch at landed L2."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = "09da9715a5d6eb07b78b8c512ca565430379e0cf"
L1 = "a2d1dc7aa7e8bfea426b71cb7e00f5e821dc08a9"
ENV = dict(os.environ, LEAN_NUM_THREADS="3", PYTHONDONTWRITEBYTECODE="1")
REPORT = {"kind": "scoped-module-overwatch", "reviewed_commit": BASE,
          "started_utc": datetime.now(timezone.utc).isoformat(), "commands": [], "checks": {}}

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
    r = subprocess.run(args, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=300)
    REPORT["commands"].append({"argv": args, "exit": r.returncode,
      "seconds": round(time.monotonic()-start, 3), "stdout": r.stdout, "stderr": r.stderr})
    save()
    print(f"exit={r.returncode}: {' '.join(args)}", flush=True)
    if r.returncode != expected:
        raise RuntimeError(r.stdout+r.stderr)
    return r

changed = subprocess.run(["git", "diff", "--name-only", L1, BASE], cwd=ROOT,
                         check=True, capture_output=True, text=True).stdout.splitlines()
SOURCES = sorted(set(changed + [
    "AGENTS.md", "src/Effect4/Schema/Modeled/Derive.lean", "Test/Schema/Modeled.lean",
    "src/Effect4/Laws/Schema/Modeled.lean", "Test/Audit/AxiomGate.lean",
    "src/Effect4/Modules/Semaphore/Cell.lean", "src/Effect4/Modules/Semaphore/Steps.lean",
    "src/Effect4/Laws/Modules/Semaphore/Steps.lean", "src/Effect4/Laws/Modules/Semaphore/Ops.lean",
    "tools/Effect4Gen/Fold.lean", "tools/Effect4Gen/manifest.json",
    "docs/research/2026-10-08-seat-MODULES-r3.md"]))
REPORT["source_digests"] = {p:digest((ROOT/p).read_bytes()) for p in SOURCES}
for p in SOURCES:
    frozen = subprocess.run(["git", "show", f"{BASE}:{p}"], cwd=ROOT,
                            check=True, capture_output=True).stdout
    check(f"pinned:{p}", digest(frozen) == REPORT["source_digests"][p])
REPORT["tools"] = {"lean": run(["lake", "env", "lean", "--version"]).stdout.strip()}
run(["lake", "build", "Effect4.Laws.Modules.Step", "Effect4.Laws.Schema.FieldRef",
     "Effect4.Laws.Program.TyNormal", "Test.Program.StepLanguage", "Test.Schema.Modeled",
     "Tools.SemanticsRegistry"])
for name in ["safety-controls", "positions", "existing-seams", "frame-sharing", "audit"]:
    run(["lake", "env", "lean", "-DwarningAsError=true", str(HERE/f"{name}.lean")])
old = HERE.parent / "2026-10-08-modules-overwatch-01"
run(["lake", "env", "lean", "-DwarningAsError=true", str(old/"opaque-composed.lean")])
opaque = run(["lake", "env", "lean", "-DwarningAsError=true", str(old/"opaque.lean")], 1)
check("OW-01-still-reproduces", "Tactic `decide` failed" in opaque.stdout and
      "Model.refusal Holder.modeledTy" in opaque.stdout and "failed to synthesize" not in opaque.stdout)
collision = run(["lake", "env", "lean", "-DwarningAsError=true", str(old/"collision.lean")], 1)
check("OW-02-still-reproduces", "has already been declared" in collision.stdout and
      "DeriveCollisionReview.Token.modeled_checked :" in collision.stdout and
      "DeriveCollisionReview.Token.modeledToC (s : Token)" in collision.stdout)
check("reviewed-source-unchanged",
      REPORT["source_digests"] == {p:digest((ROOT/p).read_bytes()) for p in SOURCES})
REPORT["probe_digests"] = {p.name:digest(p.read_bytes()) for p in HERE.iterdir()
                           if p.is_file() and p.name != "results.json"}
REPORT["reused_probe_digests"] = {p.name:digest(p.read_bytes()) for p in
    [old/"opaque-composed.lean", old/"opaque.lean", old/"collision.lean"]}
REPORT["finished_utc"] = datetime.now(timezone.utc).isoformat()
save()
print("L2 checks pass; positional drift is reproduced; OW-01 and OW-02 remain open.")
