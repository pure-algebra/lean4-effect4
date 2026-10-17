"""Recheck the scout without changing its files or the production tree."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
SCOUT = ROOT / "docs/research/2026-10-17-proof-scout"
BUILD = Path(tempfile.mkdtemp(prefix="effect4-final-review-", dir="/private/tmp"))
(BUILD / "probes").mkdir()
ENV = os.environ.copy()
ENV["LEAN_NUM_THREADS"] = "3"
ENV["LEAN_PATH"] = str(BUILD) + os.pathsep + ENV.get("LEAN_PATH", "")
records = []

def run(label, args):
    start = time.monotonic()
    result = subprocess.run(args, cwd=ROOT, env=ENV, capture_output=True, text=True)
    (OUT / (label + ".log")).write_text(result.stdout + result.stderr)
    records.append({"label": label, "command": args, "exit_code": result.returncode,
                    "seconds": round(time.monotonic() - start, 3)})
    (OUT / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(records[-1]), flush=True)
    if result.returncode:
        print(result.stdout + result.stderr, flush=True)
        raise SystemExit(result.returncode)

sources = list((SCOUT / "probes").glob("*.lean"))
sources += [SCOUT / "README.md", OUT / "run.py", OUT / "probes.lean", OUT / "handles.lean", OUT / "audit.lean"]
manifest = {
    "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
    "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    "build_directory": str(BUILD),
    "sources": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sources if p.exists()},
    "completion_criteria": ["Scout probes compile", "Probe axiom audit passes",
                            "Existing law status checked", "Review controls compile",
                            "Review controls axiom audit passes", "Report identifies scope and corrections"]
}
(OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
imports = sorted({m for p in sources if p.suffix == ".lean" for m in
                  re.findall(r"^import ([A-Za-z0-9_.]+)$", p.read_text(), re.MULTILINE)
                  if not m.startswith("probes") and m != "handles"})
run("dependencies", ["lake", "build", *imports])
for name in ["A", "B", "C", "D", "E", "R", "FGH"]:
    run(name, ["lean", "-DwarningAsError=true", "-R", str(SCOUT), "-o",
               str(BUILD / "probes" / (name + ".olean")), str(SCOUT / "probes" / (name + ".lean"))])
for name in ["Audit", "Status"]:
    run(name, ["lean", "-DwarningAsError=true", "-R", str(SCOUT), str(SCOUT / "probes" / (name + ".lean"))])
if (OUT / "probes.lean").exists():
    run("review", ["lean", "-DwarningAsError=true", "-R", str(OUT), "-o", str(BUILD / "probes.olean"), str(OUT / "probes.lean")])
    run("handles", ["lean", "-DwarningAsError=true", "-R", str(OUT), "-o", str(BUILD / "handles.olean"), str(OUT / "handles.lean")])
    run("review-audit", ["lean", "-DwarningAsError=true", "-R", str(OUT), str(OUT / "audit.lean")])
