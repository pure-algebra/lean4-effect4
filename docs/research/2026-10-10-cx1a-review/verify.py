#!/usr/bin/env python3
"""Run isolated CX1a controls in one serialized Lean lane."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys
P = Path(__file__).resolve().parent
ROOT = P.parents[2]
BASE = "f00008eeaef00b67fe93cfd0327754c9f42694ee"
ENV = {**os.environ, "LEAN_NUM_THREADS": "3"}
record_path = P / "verification.json"
record = json.loads(record_path.read_text()) if record_path.exists() else {"reviewed_commit": BASE, "checks": {}}
jobs = {
    "build": ["lake", "build", "Effect4.Laws.Program.Typed.Scope", "Effect4.Laws.Program.Typed.Adequacy", "Test.Program.InvokeControls", "TestSupport.AcquireHandle", "ProofGraph.AxiomAudit", "ProofGraph.Plan"],
    "source-diff": ["git", "diff", "--exit-code", BASE, "--", "src", "tools", "Test", "lakefile.toml", "lake-manifest.json"],
}
for name in ["ScopeControls", "MemoControls", "CleanupControls", "Audit"]:
    jobs[name] = ["lake", "env", "sh", "-c",
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/$2.olean" "$1/$2.lean"',
        "cx1a-review", str(P), name]
jobs["language"] = ["python3", "scripts/check-language.py", "--strict", str(P / "README.md"), str(P / "PLAN.md")]
selected = sys.argv[1:] or list(jobs)
for name in selected:
    cmd = jobs[name]
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result = subprocess.run(cmd, cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = result.stdout + "\nExit: " + str(result.returncode) + "\n"
    (P / (name + ".log")).write_text(log)
    record["checks"][name] = {"command": cmd, "started_utc": start, "exit": result.returncode,
                              "log_sha256": hashlib.sha256(log.encode()).hexdigest()}
    record["source_sha256"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [ROOT / "src/Effect4/Laws/Program/Typed/Scope.lean", ROOT / "src/Effect4/Laws/Program/Typed/Adequacy.lean"]}
    record["probe_source_sha256"] = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(P.glob("*.lean"))}
    record["all_recorded_passed"] = all(c["exit"] == 0 for c in record["checks"].values())
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    print(name + ": " + str(result.returncode), flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
