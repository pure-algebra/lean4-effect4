#!/usr/bin/env python3
"""Run the isolated finite controls and trust audit serially."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
PREFIX = PACKET.relative_to(ROOT).as_posix()
ENV = dict(os.environ, LEAN_NUM_THREADS="3")
changed = subprocess.check_output(
    ["git", "diff", "--name-only", "41ec1e0c", "--", "src", "tools", "lakefile.toml",
     "lake-manifest.json", "lean-toolchain"], cwd=ROOT, text=True).strip()
if changed:
    raise SystemExit("This packet targets 41ec1e0c; adapt it before checking changed source:\n" + changed)
if sys.argv[1:] == ["--check-source-only"]:
    print("Source matches the reviewed commit.")
    raise SystemExit(0)
rows = []
for label, filename in [("probe", "Probe.lean"), ("audit", "Audit.lean")]:
    cmd = ["lake", "env", "lean", "-DwarningAsError=true", f"{PREFIX}/{filename}"]
    before = datetime.now(timezone.utc).isoformat()
    result = subprocess.run(cmd, cwd=ROOT, env=ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (PACKET / f"{label}.log").write_text(result.stdout)
    rows.append({"label": label, "command": cmd, "started_utc": before,
                 "finished_utc": datetime.now(timezone.utc).isoformat(),
                 "exit_code": result.returncode})
    print(label, result.returncode, flush=True)
    print(result.stdout[-4500:], flush=True)
    if result.returncode:
        break
files = ["src/Effect4/Program/Refs.lean", "src/Effect4/Api.lean",
         "src/Effect4/Program/Typing/Blame.lean", "src/Effect4/Api/RefusalsDerived.lean",
         "src/Effect4/Laws/Program/Typed/Admission.lean", "tools/Tools/Query.lean",
         "tools/Tools/Session.lean", "tools/Tools/View/Program.lean"]
data = {"reviewed_commit": subprocess.check_output(
    ["git", "rev-parse", "41ec1e0c"], cwd=ROOT, text=True).strip(),
    "lean_num_threads": "3", "results": rows,
    "source_sha256": {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    "probe_sha256": hashlib.sha256((PACKET / "Probe.lean").read_bytes()).hexdigest(),
    "guards": (PACKET / "Probe.lean").read_text().count("#guard ")}
(PACKET / "verification.json").write_text(json.dumps(data, indent=2) + "\n")
raise SystemExit(0 if len(rows) == 2 and all(r["exit_code"] == 0 for r in rows) else 1)
